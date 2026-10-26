import V185TrunkScan21Chunk114

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1398162 : List Nat := [3, 2, 3, 3, 2, 1, 7]
def baseStart_1398162 : Nat := 118140960795 + 1398162 * 2 ^ 59
def prefixEnd_1398162 : Nat := 4983230072969 + 3 ^ 40 * 1398162 * 2
def baseEnd_1398162 : Nat := 35453290807489576219505

theorem tailTrace_1398162 : CollatzResearch.WordTrace tailWord_1398162 prefixEnd_1398162 35453290807489576219505 := by
  unfold tailWord_1398162
  simp only [CollatzResearch.WordTrace]
  refine ⟨12748789390176333975975185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33996771707136890602600493 12748789390176333975975185)
  ·
    refine ⟨9561592042632250481981389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12748789390176333975975185 9561592042632250481981389)
    ·
      refine ⟨3585597015987093930743021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9561592042632250481981389 3585597015987093930743021)
      ·
        refine ⟨1344598880995160224028633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3585597015987093930743021 1344598880995160224028633)
        ·
          refine ⟨1008449160746370168021475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1344598880995160224028633 1008449160746370168021475)
          ·
            refine ⟨1512673741119555252032213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1008449160746370168021475 1512673741119555252032213)
            ·
              refine ⟨35453290807489576219505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1512673741119555252032213 35453290807489576219505)
              ·
                rfl

theorem cell21_1398162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 7].length) (baseStart_1398162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1398162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1398162 prefixEnd_1398162 := by exact prefixLift 1398162
  have htrace : WordTrace (prefixWord ++ tailWord_1398162) baseStart_1398162 baseEnd_1398162 := by
    simpa [prefixWord, tailWord_1398162, baseEnd_1398162] using wordTrace_append hprefix tailTrace_1398162
  have hstable : (prefixWord ++ tailWord_1398162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398162).length < 2 ^ (prefixWord ++ tailWord_1398162).sum := by decide
  have hdescent : baseEnd_1398162 < baseStart_1398162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398173 : List Nat := [1, 4, 2, 1, 3, 1, 2, 1, 6]
def baseStart_1398173 : Nat := 118140960795 + 1398173 * 2 ^ 59
def prefixEnd_1398173 : Nat := 4983230072969 + 3 ^ 40 * 1398173 * 2
def baseEnd_1398173 : Nat := 319082127617272611292189

theorem tailTrace_1398173 : CollatzResearch.WordTrace tailWord_1398173 prefixEnd_1398173 319082127617272611292189 := by
  unfold tailWord_1398173
  simp only [CollatzResearch.WordTrace]
  refine ⟨50995558763665484782551173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33997039175776989855034115 50995558763665484782551173)
  ·
    refine ⟨9561667268187278396728345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50995558763665484782551173 9561667268187278396728345)
    ·
      refine ⟨7171250451140458797546259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9561667268187278396728345 7171250451140458797546259)
      ·
        refine ⟨10756875676710688196319389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7171250451140458797546259 10756875676710688196319389)
        ·
          refine ⟨4033828378766508073619771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10756875676710688196319389 4033828378766508073619771)
          ·
            refine ⟨6050742568149762110429657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4033828378766508073619771 6050742568149762110429657)
            ·
              refine ⟨4538056926112321582822243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6050742568149762110429657 4538056926112321582822243)
              ·
                refine ⟨6807085389168482374233365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4538056926112321582822243 6807085389168482374233365)
                ·
                  refine ⟨319082127617272611292189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6807085389168482374233365 319082127617272611292189)
                  ·
                    rfl

theorem cell21_1398173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_1398173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1398173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1398173 prefixEnd_1398173 := by exact prefixLift 1398173
  have htrace : WordTrace (prefixWord ++ tailWord_1398173) baseStart_1398173 baseEnd_1398173 := by
    simpa [prefixWord, tailWord_1398173, baseEnd_1398173] using wordTrace_append hprefix tailTrace_1398173
  have hstable : (prefixWord ++ tailWord_1398173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398173).length < 2 ^ (prefixWord ++ tailWord_1398173).sum := by decide
  have hdescent : baseEnd_1398173 < baseStart_1398173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398176 : List Nat := [2, 1, 1, 4, 1, 2, 5, 2, 3]
def baseStart_1398176 : Nat := 118140960795 + 1398176 * 2 ^ 59
def prefixEnd_1398176 : Nat := 4983230072969 + 3 ^ 40 * 1398176 * 2
def baseEnd_1398176 : Nat := 319082812258145272742183

theorem tailTrace_1398176 : CollatzResearch.WordTrace tailWord_1398176 prefixEnd_1398176 319082812258145272742183 := by
  unfold tailWord_1398176
  simp only [CollatzResearch.WordTrace]
  refine ⟨25497834091327308147455191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33997112121769744196606921 25497834091327308147455191)
  ·
    refine ⟨38246751136990962221182787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25497834091327308147455191 38246751136990962221182787)
    ·
      refine ⟨57370126705486443331774181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38246751136990962221182787 57370126705486443331774181)
      ·
        refine ⟨10756898757278708124707659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57370126705486443331774181 10756898757278708124707659)
        ·
          refine ⟨16135348135918062187061489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10756898757278708124707659 16135348135918062187061489)
          ·
            refine ⟨12101511101938546640296117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16135348135918062187061489 12101511101938546640296117)
            ·
              refine ⟨1134516665806738747527761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12101511101938546640296117 1134516665806738747527761)
              ·
                refine ⟨850887499355054060645821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1134516665806738747527761 850887499355054060645821)
                ·
                  refine ⟨319082812258145272742183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 850887499355054060645821 319082812258145272742183)
                  ·
                    rfl

theorem cell21_1398176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2, 3].length) (baseStart_1398176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1398176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1398176 prefixEnd_1398176 := by exact prefixLift 1398176
  have htrace : WordTrace (prefixWord ++ tailWord_1398176) baseStart_1398176 baseEnd_1398176 := by
    simpa [prefixWord, tailWord_1398176, baseEnd_1398176] using wordTrace_append hprefix tailTrace_1398176
  have hstable : (prefixWord ++ tailWord_1398176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398176).length < 2 ^ (prefixWord ++ tailWord_1398176).sum := by decide
  have hdescent : baseEnd_1398176 < baseStart_1398176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398232 : List Nat := [2, 1, 2, 2, 2, 1, 2, 3, 6]
def baseStart_1398232 : Nat := 118140960795 + 1398232 * 2 ^ 59
def prefixEnd_1398232 : Nat := 4983230072969 + 3 ^ 40 * 1398232 * 2
def baseEnd_1398232 : Nat := 319095592221101619808735

theorem tailTrace_1398232 : CollatzResearch.WordTrace tailWord_1398232 prefixEnd_1398232 319095592221101619808735 := by
  unfold tailWord_1398232
  simp only [CollatzResearch.WordTrace]
  refine ⟨25498855335225868929474475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33998473780301158572632633 25498855335225868929474475)
  ·
    refine ⟨38248283002838803394211713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25498855335225868929474475 38248283002838803394211713)
    ·
      refine ⟨28686212252129102545658785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38248283002838803394211713 28686212252129102545658785)
      ·
        refine ⟨21514659189096826909244089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28686212252129102545658785 21514659189096826909244089)
        ·
          refine ⟨16135994391822620181933067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21514659189096826909244089 16135994391822620181933067)
          ·
            refine ⟨24203991587733930272899601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16135994391822620181933067 24203991587733930272899601)
            ·
              refine ⟨18152993690800447704674701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24203991587733930272899601 18152993690800447704674701)
              ·
                refine ⟨6807372634050167889253013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18152993690800447704674701 6807372634050167889253013)
                ·
                  refine ⟨319095592221101619808735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6807372634050167889253013 319095592221101619808735)
                  ·
                    rfl

theorem cell21_1398232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 6].length) (baseStart_1398232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1398232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1398232 prefixEnd_1398232 := by exact prefixLift 1398232
  have htrace : WordTrace (prefixWord ++ tailWord_1398232) baseStart_1398232 baseEnd_1398232 := by
    simpa [prefixWord, tailWord_1398232, baseEnd_1398232] using wordTrace_append hprefix tailTrace_1398232
  have hstable : (prefixWord ++ tailWord_1398232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398232).length < 2 ^ (prefixWord ++ tailWord_1398232).sum := by decide
  have hdescent : baseEnd_1398232 < baseStart_1398232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398277 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 9]
def baseStart_1398277 : Nat := 118140960795 + 1398277 * 2 ^ 59
def prefixEnd_1398277 : Nat := 4983230072969 + 3 ^ 40 * 1398277 * 2
def baseEnd_1398277 : Nat := 319105861834191541558643

theorem tailTrace_1398277 : CollatzResearch.WordTrace tailWord_1398277 prefixEnd_1398277 319105861834191541558643 := by
  unfold tailWord_1398277
  simp only [CollatzResearch.WordTrace]
  refine ⟨50999351955288710544337085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33999567970192473696224723 50999351955288710544337085)
  ·
    refine ⟨19124756983233266454126407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50999351955288710544337085 19124756983233266454126407)
    ·
      refine ⟨28687135474849899681189611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19124756983233266454126407 28687135474849899681189611)
      ·
        refine ⟨43030703212274849521784417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28687135474849899681189611 43030703212274849521784417)
        ·
          refine ⟨32273027409206137141338313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43030703212274849521784417 32273027409206137141338313)
          ·
            refine ⟨24204770556904602856003735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32273027409206137141338313 24204770556904602856003735)
            ·
              refine ⟨36307155835356904284005603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24204770556904602856003735 36307155835356904284005603)
              ·
                refine ⟨54460733753035356426008405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36307155835356904284005603 54460733753035356426008405)
                ·
                  refine ⟨319105861834191541558643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54460733753035356426008405 319105861834191541558643)
                  ·
                    rfl

theorem cell21_1398277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_1398277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1398277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1398277 prefixEnd_1398277 := by exact prefixLift 1398277
  have htrace : WordTrace (prefixWord ++ tailWord_1398277) baseStart_1398277 baseEnd_1398277 := by
    simpa [prefixWord, tailWord_1398277, baseEnd_1398277] using wordTrace_append hprefix tailTrace_1398277
  have hstable : (prefixWord ++ tailWord_1398277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398277).length < 2 ^ (prefixWord ++ tailWord_1398277).sum := by decide
  have hdescent : baseEnd_1398277 < baseStart_1398277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398283 : List Nat := [1, 1, 1, 1, 9, 1, 1, 2, 4]
def baseStart_1398283 : Nat := 118140960795 + 1398283 * 2 ^ 59
def prefixEnd_1398283 : Nat := 4983230072969 + 3 ^ 40 * 1398283 * 2
def baseEnd_1398283 : Nat := 319107231115936864458631

theorem tailTrace_1398283 : CollatzResearch.WordTrace tailWord_1398283 prefixEnd_1398283 319107231115936864458631 := by
  unfold tailWord_1398283
  simp only [CollatzResearch.WordTrace]
  refine ⟨50999570793266973569055503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33999713862177982379370335 50999570793266973569055503)
  ·
    refine ⟨76499356189900460353583255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50999570793266973569055503 76499356189900460353583255)
    ·
      refine ⟨114749034284850690530374883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76499356189900460353583255 114749034284850690530374883)
      ·
        refine ⟨172123551427276035795562325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114749034284850690530374883 172123551427276035795562325)
        ·
          refine ⟨1008536434144195522239623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 172123551427276035795562325 1008536434144195522239623)
          ·
            refine ⟨1512804651216293283359435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1008536434144195522239623 1512804651216293283359435)
            ·
              refine ⟨2269206976824439925039153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1512804651216293283359435 2269206976824439925039153)
              ·
                refine ⟨1701905232618329943779365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2269206976824439925039153 1701905232618329943779365)
                ·
                  refine ⟨319107231115936864458631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1701905232618329943779365 319107231115936864458631)
                  ·
                    rfl

theorem cell21_1398283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 4].length) (baseStart_1398283 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1398283 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1398283 prefixEnd_1398283 := by exact prefixLift 1398283
  have htrace : WordTrace (prefixWord ++ tailWord_1398283) baseStart_1398283 baseEnd_1398283 := by
    simpa [prefixWord, tailWord_1398283, baseEnd_1398283] using wordTrace_append hprefix tailTrace_1398283
  have hstable : (prefixWord ++ tailWord_1398283).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398283).length < 2 ^ (prefixWord ++ tailWord_1398283).sum := by decide
  have hdescent : baseEnd_1398283 < baseStart_1398283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398328 : List Nat := [2, 1, 2, 1, 4, 4, 1, 3, 3]
def baseStart_1398328 : Nat := 118140960795 + 1398328 * 2 ^ 59
def prefixEnd_1398328 : Nat := 4983230072969 + 3 ^ 40 * 1398328 * 2
def baseEnd_1398328 : Nat := 319117500729026786208539

theorem tailTrace_1398328 : CollatzResearch.WordTrace tailWord_1398328 prefixEnd_1398328 319117500729026786208539 := by
  unfold tailWord_1398328
  simp only [CollatzResearch.WordTrace]
  refine ⟨25500606039051973127221819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34000808052069297502962425 25500606039051973127221819)
  ·
    refine ⟨38250909058577959690832729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25500606039051973127221819 38250909058577959690832729)
    ·
      refine ⟨28688181793933469768124547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38250909058577959690832729 28688181793933469768124547)
      ·
        refine ⟨43032272690900204652186821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28688181793933469768124547 43032272690900204652186821)
        ·
          refine ⟨8068551129543788372285029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43032272690900204652186821 8068551129543788372285029)
          ·
            refine ⟨1512853336789460319803443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8068551129543788372285029 1512853336789460319803443)
            ·
              refine ⟨2269280005184190479705165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1512853336789460319803443 2269280005184190479705165)
              ·
                refine ⟨850980001944071429889437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2269280005184190479705165 850980001944071429889437)
                ·
                  refine ⟨319117500729026786208539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 850980001944071429889437 319117500729026786208539)
                  ·
                    rfl

theorem cell21_1398328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3, 3].length) (baseStart_1398328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1398328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1398328 prefixEnd_1398328 := by exact prefixLift 1398328
  have htrace : WordTrace (prefixWord ++ tailWord_1398328) baseStart_1398328 baseEnd_1398328 := by
    simpa [prefixWord, tailWord_1398328, baseEnd_1398328] using wordTrace_append hprefix tailTrace_1398328
  have hstable : (prefixWord ++ tailWord_1398328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398328).length < 2 ^ (prefixWord ++ tailWord_1398328).sum := by decide
  have hdescent : baseEnd_1398328 < baseStart_1398328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398401 : List Nat := [1, 2, 4, 2, 1, 2, 1, 4, 4]
def baseStart_1398401 : Nat := 118140960795 + 1398401 * 2 ^ 59
def prefixEnd_1398401 : Nat := 4983230072969 + 3 ^ 40 * 1398401 * 2
def baseEnd_1398401 : Nat := 319134160323594881491723

theorem tailTrace_1398401 : CollatzResearch.WordTrace tailWord_1398401 prefixEnd_1398401 319134160323594881491723 := by
  unfold tailWord_1398401
  simp only [CollatzResearch.WordTrace]
  refine ⟨51003874606839479721851057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34002583071226319814567371 51003874606839479721851057)
  ·
    refine ⟨38252905955129609791388293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51003874606839479721851057 38252905955129609791388293)
    ·
      refine ⟨7172419866586801835885305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38252905955129609791388293 7172419866586801835885305)
      ·
        refine ⟨5379314899940101376913979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7172419866586801835885305 5379314899940101376913979)
        ·
          refine ⟨8068972349910152065370969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5379314899940101376913979 8068972349910152065370969)
          ·
            refine ⟨6051729262432614049028227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8068972349910152065370969 6051729262432614049028227)
            ·
              refine ⟨9077593893648921073542341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6051729262432614049028227 9077593893648921073542341)
              ·
                refine ⟨1702048855059172701289189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9077593893648921073542341 1702048855059172701289189)
                ·
                  refine ⟨319134160323594881491723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1702048855059172701289189 319134160323594881491723)
                  ·
                    rfl

theorem cell21_1398401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 4].length) (baseStart_1398401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1398401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1398401 prefixEnd_1398401 := by exact prefixLift 1398401
  have htrace : WordTrace (prefixWord ++ tailWord_1398401) baseStart_1398401 baseEnd_1398401 := by
    simpa [prefixWord, tailWord_1398401, baseEnd_1398401] using wordTrace_append hprefix tailTrace_1398401
  have hstable : (prefixWord ++ tailWord_1398401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398401).length < 2 ^ (prefixWord ++ tailWord_1398401).sum := by decide
  have hdescent : baseEnd_1398401 < baseStart_1398401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398404 : List Nat := [2, 3, 2, 1, 4, 1, 1, 4, 3]
def baseStart_1398404 : Nat := 118140960795 + 1398404 * 2 ^ 59
def prefixEnd_1398404 : Nat := 4983230072969 + 3 ^ 40 * 1398404 * 2
def baseEnd_1398404 : Nat := 319134844964467542941717

theorem tailTrace_1398404 : CollatzResearch.WordTrace tailWord_1398404 prefixEnd_1398404 319134844964467542941717 := by
  unfold tailWord_1398404
  simp only [CollatzResearch.WordTrace]
  refine ⟨25501992012914305617105133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34002656017219074156140177 25501992012914305617105133)
  ·
    refine ⟨9563247004842864606414425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25501992012914305617105133 9563247004842864606414425)
    ·
      refine ⟨7172435253632148454810819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9563247004842864606414425 7172435253632148454810819)
      ·
        refine ⟨10758652880448222682216229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7172435253632148454810819 10758652880448222682216229)
        ·
          refine ⟨2017247415084041752915543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10758652880448222682216229 2017247415084041752915543)
          ·
            refine ⟨3025871122626062629373315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2017247415084041752915543 3025871122626062629373315)
            ·
              refine ⟨4538806683939093944059973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3025871122626062629373315 4538806683939093944059973)
              ·
                refine ⟨851026253238580114511245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4538806683939093944059973 851026253238580114511245)
                ·
                  refine ⟨319134844964467542941717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 851026253238580114511245 319134844964467542941717)
                  ·
                    rfl

theorem cell21_1398404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_1398404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1398404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1398404 prefixEnd_1398404 := by exact prefixLift 1398404
  have htrace : WordTrace (prefixWord ++ tailWord_1398404) baseStart_1398404 baseEnd_1398404 := by
    simpa [prefixWord, tailWord_1398404, baseEnd_1398404] using wordTrace_append hprefix tailTrace_1398404
  have hstable : (prefixWord ++ tailWord_1398404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398404).length < 2 ^ (prefixWord ++ tailWord_1398404).sum := by decide
  have hdescent : baseEnd_1398404 < baseStart_1398404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398432 : List Nat := [2, 1, 1, 4, 3, 2, 3, 5]
def baseStart_1398432 : Nat := 118140960795 + 1398432 * 2 ^ 59
def prefixEnd_1398432 : Nat := 4983230072969 + 3 ^ 40 * 1398432 * 2
def baseEnd_1398432 : Nat := 106380411648648572158331

theorem tailTrace_1398432 : CollatzResearch.WordTrace tailWord_1398432 prefixEnd_1398432 106380411648648572158331 := by
  unfold tailWord_1398432
  simp only [CollatzResearch.WordTrace]
  refine ⟨25502502634863586008114775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34003336846484781344153033 25502502634863586008114775)
  ·
    refine ⟨38253753952295379012172163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25502502634863586008114775 38253753952295379012172163)
    ·
      refine ⟨57380630928443068518258245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38253753952295379012172163 57380630928443068518258245)
      ·
        refine ⟨10758868299083075347173421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57380630928443068518258245 10758868299083075347173421)
        ·
          refine ⟨4034575612156153255190033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10758868299083075347173421 4034575612156153255190033)
          ·
            refine ⟨3025931709117114941392525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4034575612156153255190033 3025931709117114941392525)
            ·
              refine ⟨1134724390918918103022197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3025931709117114941392525 1134724390918918103022197)
              ·
                refine ⟨106380411648648572158331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1134724390918918103022197 106380411648648572158331)
                ·
                  rfl

theorem cell21_1398432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 5].length) (baseStart_1398432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1398432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1398432 prefixEnd_1398432 := by exact prefixLift 1398432
  have htrace : WordTrace (prefixWord ++ tailWord_1398432) baseStart_1398432 baseEnd_1398432 := by
    simpa [prefixWord, tailWord_1398432, baseEnd_1398432] using wordTrace_append hprefix tailTrace_1398432
  have hstable : (prefixWord ++ tailWord_1398432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398432).length < 2 ^ (prefixWord ++ tailWord_1398432).sum := by decide
  have hdescent : baseEnd_1398432 < baseStart_1398432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398497 : List Nat := [1, 2, 3, 1, 6, 1, 1, 3, 3]
def baseStart_1398497 : Nat := 118140960795 + 1398497 * 2 ^ 59
def prefixEnd_1398497 : Nat := 4983230072969 + 3 ^ 40 * 1398497 * 2
def baseEnd_1398497 : Nat := 319156068831520047891527

theorem tailTrace_1398497 : CollatzResearch.WordTrace tailWord_1398497 prefixEnd_1398497 319156068831520047891527 := by
  unfold tailWord_1398497
  simp only [CollatzResearch.WordTrace]
  refine ⟨51007376014491688117345745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34004917342994458744897163 51007376014491688117345745)
  ·
    refine ⟨38255532010868766088009309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51007376014491688117345745 38255532010868766088009309)
    ·
      refine ⟨14345824504075787283003491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38255532010868766088009309 14345824504075787283003491)
      ·
        refine ⟨21518736756113680924505237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14345824504075787283003491 21518736756113680924505237)
        ·
          refine ⟨1008690785442828793336183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21518736756113680924505237 1008690785442828793336183)
          ·
            refine ⟨1513036178164243190004275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1008690785442828793336183 1513036178164243190004275)
            ·
              refine ⟨2269554267246364785006413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1513036178164243190004275 2269554267246364785006413)
              ·
                refine ⟨851082850217386794377405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2269554267246364785006413 851082850217386794377405)
                ·
                  refine ⟨319156068831520047891527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 851082850217386794377405 319156068831520047891527)
                  ·
                    rfl

theorem cell21_1398497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3, 3].length) (baseStart_1398497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1398497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1398497 prefixEnd_1398497 := by exact prefixLift 1398497
  have htrace : WordTrace (prefixWord ++ tailWord_1398497) baseStart_1398497 baseEnd_1398497 := by
    simpa [prefixWord, tailWord_1398497, baseEnd_1398497] using wordTrace_append hprefix tailTrace_1398497
  have hstable : (prefixWord ++ tailWord_1398497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398497).length < 2 ^ (prefixWord ++ tailWord_1398497).sum := by decide
  have hdescent : baseEnd_1398497 < baseStart_1398497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398688 : List Nat := [2, 1, 1, 4, 1, 1, 1, 6, 4]
def baseStart_1398688 : Nat := 118140960795 + 1398688 * 2 ^ 59
def prefixEnd_1398688 : Nat := 4983230072969 + 3 ^ 40 * 1398688 * 2
def baseEnd_1398688 : Nat := 319199657633746160207803

theorem tailTrace_1398688 : CollatzResearch.WordTrace tailWord_1398688 prefixEnd_1398688 319199657633746160207803 := by
  unfold tailWord_1398688
  simp only [CollatzResearch.WordTrace]
  refine ⟨25507171178399863868774359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34009561571199818491699145 25507171178399863868774359)
  ·
    refine ⟨38260756767599795803161539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25507171178399863868774359 38260756767599795803161539)
    ·
      refine ⟨57391135151399693704742309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38260756767599795803161539 57391135151399693704742309)
      ·
        refine ⟨10760837840887442569639183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57391135151399693704742309 10760837840887442569639183)
        ·
          refine ⟨16141256761331163854458775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10760837840887442569639183 16141256761331163854458775)
          ·
            refine ⟨24211885141996745781688163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16141256761331163854458775 24211885141996745781688163)
            ·
              refine ⟨36317827712995118672532245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24211885141996745781688163 36317827712995118672532245)
              ·
                refine ⟨1702398174046646187774949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36317827712995118672532245 1702398174046646187774949)
                ·
                  refine ⟨319199657633746160207803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1702398174046646187774949 319199657633746160207803)
                  ·
                    rfl

theorem cell21_1398688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 4].length) (baseStart_1398688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1398688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1398688 prefixEnd_1398688 := by exact prefixLift 1398688
  have htrace : WordTrace (prefixWord ++ tailWord_1398688) baseStart_1398688 baseEnd_1398688 := by
    simpa [prefixWord, tailWord_1398688, baseEnd_1398688] using wordTrace_append hprefix tailTrace_1398688
  have hstable : (prefixWord ++ tailWord_1398688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398688).length < 2 ^ (prefixWord ++ tailWord_1398688).sum := by decide
  have hdescent : baseEnd_1398688 < baseStart_1398688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398705 : List Nat := [1, 2, 2, 4, 2, 2, 1, 3, 4]
def baseStart_1398705 : Nat := 118140960795 + 1398705 * 2 ^ 59
def prefixEnd_1398705 : Nat := 4983230072969 + 3 ^ 40 * 1398705 * 2
def baseEnd_1398705 : Nat := 319203537265357908424435

theorem tailTrace_1398705 : CollatzResearch.WordTrace tailWord_1398705 prefixEnd_1398705 319203537265357908424435 := by
  unfold tailWord_1398705
  simp only [CollatzResearch.WordTrace]
  refine ⟨51014962397738139640917569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34009974931825426427278379 51014962397738139640917569)
  ·
    refine ⟨38261221798303604730688177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51014962397738139640917569 38261221798303604730688177)
    ·
      refine ⟨28695916348727703548016133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38261221798303604730688177 28695916348727703548016133)
      ·
        refine ⟨5380484315386444415253025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28695916348727703548016133 5380484315386444415253025)
        ·
          refine ⟨4035363236539833311439769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5380484315386444415253025 4035363236539833311439769)
          ·
            refine ⟨3026522427404874983579827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4035363236539833311439769 3026522427404874983579827)
            ·
              refine ⟨4539783641107312475369741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3026522427404874983579827 4539783641107312475369741)
              ·
                refine ⟨1702418865415242178263653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4539783641107312475369741 1702418865415242178263653)
                ·
                  refine ⟨319203537265357908424435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1702418865415242178263653 319203537265357908424435)
                  ·
                    rfl

theorem cell21_1398705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 4].length) (baseStart_1398705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1398705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1398705 prefixEnd_1398705 := by exact prefixLift 1398705
  have htrace : WordTrace (prefixWord ++ tailWord_1398705) baseStart_1398705 baseEnd_1398705 := by
    simpa [prefixWord, tailWord_1398705, baseEnd_1398705] using wordTrace_append hprefix tailTrace_1398705
  have hstable : (prefixWord ++ tailWord_1398705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398705).length < 2 ^ (prefixWord ++ tailWord_1398705).sum := by decide
  have hdescent : baseEnd_1398705 < baseStart_1398705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398742 : List Nat := [5, 2, 1, 1, 3, 2, 2, 2, 3]
def baseStart_1398742 : Nat := 118140960795 + 1398742 * 2 ^ 59
def prefixEnd_1398742 : Nat := 4983230072969 + 3 ^ 40 * 1398742 * 2
def baseEnd_1398742 : Nat := 319211981169454066307693

theorem tailTrace_1398742 : CollatzResearch.WordTrace tailWord_1398742 prefixEnd_1398742 319211981169454066307693 := by
  unfold tailWord_1398742
  simp only [CollatzResearch.WordTrace]
  refine ⟨3188519493662755935000905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34010874599069396640009653 3188519493662755935000905)
  ·
    refine ⟨2391389620247066951250679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3188519493662755935000905 2391389620247066951250679)
    ·
      refine ⟨3587084430370600426876019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2391389620247066951250679 3587084430370600426876019)
      ·
        refine ⟨5380626645555900640314029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3587084430370600426876019 5380626645555900640314029)
        ·
          refine ⟨2017734992083462740117761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5380626645555900640314029 2017734992083462740117761)
          ·
            refine ⟨1513301244062597055088321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2017734992083462740117761 1513301244062597055088321)
            ·
              refine ⟨1134975933046947791316241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1513301244062597055088321 1134975933046947791316241)
              ·
                refine ⟨851231949785210843487181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1134975933046947791316241 851231949785210843487181)
                ·
                  refine ⟨319211981169454066307693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 851231949785210843487181 319211981169454066307693)
                  ·
                    rfl

theorem cell21_1398742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_1398742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1398742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1398742 prefixEnd_1398742 := by exact prefixLift 1398742
  have htrace : WordTrace (prefixWord ++ tailWord_1398742) baseStart_1398742 baseEnd_1398742 := by
    simpa [prefixWord, tailWord_1398742, baseEnd_1398742] using wordTrace_append hprefix tailTrace_1398742
  have hstable : (prefixWord ++ tailWord_1398742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398742).length < 2 ^ (prefixWord ++ tailWord_1398742).sum := by decide
  have hdescent : baseEnd_1398742 < baseStart_1398742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398790 : List Nat := [6, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_1398790 : Nat := 118140960795 + 1398790 * 2 ^ 59
def prefixEnd_1398790 : Nat := 4983230072969 + 3 ^ 40 * 1398790 * 2
def baseEnd_1398790 : Nat := 319222935423416649507595

theorem tailTrace_1398790 : CollatzResearch.WordTrace tailWord_1398790 prefixEnd_1398790 319222935423416649507595 := by
  unfold tailWord_1398790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1594314456325943723680057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34012041734953466105174549 1594314456325943723680057)
  ·
    refine ⟨1195735842244457792760043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1594314456325943723680057 1195735842244457792760043)
    ·
      refine ⟨1793603763366686689140065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1195735842244457792760043 1793603763366686689140065)
      ·
        refine ⟨1345202822525015016855049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1793603763366686689140065 1345202822525015016855049)
        ·
          refine ⟨1008902116893761262641287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1345202822525015016855049 1008902116893761262641287)
          ·
            refine ⟨1513353175340641893961931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1008902116893761262641287 1513353175340641893961931)
            ·
              refine ⟨2270029763010962840942897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1513353175340641893961931 2270029763010962840942897)
              ·
                refine ⟨1702522322258222130707173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2270029763010962840942897 1702522322258222130707173)
                ·
                  refine ⟨319222935423416649507595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1702522322258222130707173 319222935423416649507595)
                  ·
                    rfl

theorem cell21_1398790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_1398790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1398790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1398790 prefixEnd_1398790 := by exact prefixLift 1398790
  have htrace : WordTrace (prefixWord ++ tailWord_1398790) baseStart_1398790 baseEnd_1398790 := by
    simpa [prefixWord, tailWord_1398790, baseEnd_1398790] using wordTrace_append hprefix tailTrace_1398790
  have hstable : (prefixWord ++ tailWord_1398790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398790).length < 2 ^ (prefixWord ++ tailWord_1398790).sum := by decide
  have hdescent : baseEnd_1398790 < baseStart_1398790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398826 : List Nat := [3, 1, 4, 1, 2, 1, 2, 2, 5]
def baseStart_1398826 : Nat := 118140960795 + 1398826 * 2 ^ 59
def prefixEnd_1398826 : Nat := 4983230072969 + 3 ^ 40 * 1398826 * 2
def baseEnd_1398826 : Nat := 319231151113888586907521

theorem tailTrace_1398826 : CollatzResearch.WordTrace tailWord_1398826 prefixEnd_1398826 319231151113888586907521 := by
  unfold tailWord_1398826
  simp only [CollatzResearch.WordTrace]
  refine ⟨12754843907574944326518083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34012917086866518204048221 12754843907574944326518083)
  ·
    refine ⟨19132265861362416489777125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12754843907574944326518083 19132265861362416489777125)
    ·
      refine ⟨3587299849005453091833211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19132265861362416489777125 3587299849005453091833211)
      ·
        refine ⟨5380949773508179637749817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3587299849005453091833211 5380949773508179637749817)
        ·
          refine ⟨4035712330131134728312363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5380949773508179637749817 4035712330131134728312363)
          ·
            refine ⟨6053568495196702092468545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4035712330131134728312363 6053568495196702092468545)
            ·
              refine ⟨4540176371397526569351409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6053568495196702092468545 4540176371397526569351409)
              ·
                refine ⟨3405132278548144927013557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4540176371397526569351409 3405132278548144927013557)
                ·
                  refine ⟨319231151113888586907521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3405132278548144927013557 319231151113888586907521)
                  ·
                    rfl

theorem cell21_1398826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_1398826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1398826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1398826 prefixEnd_1398826 := by exact prefixLift 1398826
  have htrace : WordTrace (prefixWord ++ tailWord_1398826) baseStart_1398826 baseEnd_1398826 := by
    simpa [prefixWord, tailWord_1398826, baseEnd_1398826] using wordTrace_append hprefix tailTrace_1398826
  have hstable : (prefixWord ++ tailWord_1398826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398826).length < 2 ^ (prefixWord ++ tailWord_1398826).sum := by decide
  have hdescent : baseEnd_1398826 < baseStart_1398826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398919 : List Nat := [1, 1, 4, 2, 1, 1, 6, 2, 3]
def baseStart_1398919 : Nat := 118140960795 + 1398919 * 2 ^ 59
def prefixEnd_1398919 : Nat := 4983230072969 + 3 ^ 40 * 1398919 * 2
def baseEnd_1398919 : Nat := 319252374980941091857331

theorem tailTrace_1398919 : CollatzResearch.WordTrace tailWord_1398919 prefixEnd_1398919 319252374980941091857331 := by
  unfold tailWord_1398919
  simp only [CollatzResearch.WordTrace]
  refine ⟨51022767618962854189207811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34015178412641902792805207 51022767618962854189207811)
  ·
    refine ⟨76534151428444281283811717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51022767618962854189207811 76534151428444281283811717)
    ·
      refine ⟨14350153392833302740714697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76534151428444281283811717 14350153392833302740714697)
      ·
        refine ⟨10762615044624977055536023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14350153392833302740714697 10762615044624977055536023)
        ·
          refine ⟨16143922566937465583304035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10762615044624977055536023 16143922566937465583304035)
          ·
            refine ⟨24215883850406198374956053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16143922566937465583304035 24215883850406198374956053)
            ·
              refine ⟨1135119555487790548826065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24215883850406198374956053 1135119555487790548826065)
              ·
                refine ⟨851339666615842911619549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1135119555487790548826065 851339666615842911619549)
                ·
                  refine ⟨319252374980941091857331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 851339666615842911619549 319252374980941091857331)
                  ·
                    rfl

theorem cell21_1398919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2, 3].length) (baseStart_1398919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1398919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1398919 prefixEnd_1398919 := by exact prefixLift 1398919
  have htrace : WordTrace (prefixWord ++ tailWord_1398919) baseStart_1398919 baseEnd_1398919 := by
    simpa [prefixWord, tailWord_1398919, baseEnd_1398919] using wordTrace_append hprefix tailTrace_1398919
  have hstable : (prefixWord ++ tailWord_1398919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398919).length < 2 ^ (prefixWord ++ tailWord_1398919).sum := by decide
  have hdescent : baseEnd_1398919 < baseStart_1398919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399082 : List Nat := [3, 1, 4, 2, 11]
def baseStart_1399082 : Nat := 118140960795 + 1399082 * 2 ^ 59
def prefixEnd_1399082 : Nat := 4983230072969 + 3 ^ 40 * 1399082 * 2
def baseEnd_1399082 : Nat := 3941846590144309020251

theorem tailTrace_1399082 : CollatzResearch.WordTrace tailWord_1399082 prefixEnd_1399082 3941846590144309020251 := by
  unfold tailWord_1399082
  simp only [CollatzResearch.WordTrace]
  refine ⟨12757178179343083256847875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34019141811581555351594333 12757178179343083256847875)
  ·
    refine ⟨19135767269014624885271813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12757178179343083256847875 19135767269014624885271813)
    ·
      refine ⟨3587956362940242165988465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19135767269014624885271813 3587956362940242165988465)
      ·
        refine ⟨2690967272205181624491349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3587956362940242165988465 2690967272205181624491349)
        ·
          refine ⟨3941846590144309020251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2690967272205181624491349 3941846590144309020251)
          ·
            rfl

theorem cell21_1399082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 11].length) (baseStart_1399082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1399082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1399082 prefixEnd_1399082 := by exact prefixLift 1399082
  have htrace : WordTrace (prefixWord ++ tailWord_1399082) baseStart_1399082 baseEnd_1399082 := by
    simpa [prefixWord, tailWord_1399082, baseEnd_1399082] using wordTrace_append hprefix tailTrace_1399082
  have hstable : (prefixWord ++ tailWord_1399082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399082).length < 2 ^ (prefixWord ++ tailWord_1399082).sum := by decide
  have hdescent : baseEnd_1399082 < baseStart_1399082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399127 : List Nat := [1, 1, 3, 2, 3, 1, 2, 2, 6]
def baseStart_1399127 : Nat := 118140960795 + 1399127 * 2 ^ 59
def prefixEnd_1399127 : Nat := 4983230072969 + 3 ^ 40 * 1399127 * 2
def baseEnd_1399127 : Nat := 319299843414778952390239

theorem tailTrace_1399127 : CollatzResearch.WordTrace tailWord_1399127 prefixEnd_1399127 319299843414778952390239 := by
  unfold tailWord_1399127
  simp only [CollatzResearch.WordTrace]
  refine ⟨51030354002209305712779635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34020236001472870475186423 51030354002209305712779635)
  ·
    refine ⟨76545531003313958569169453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51030354002209305712779635 76545531003313958569169453)
    ·
      refine ⟨28704574126242734463438545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76545531003313958569169453 28704574126242734463438545)
      ·
        refine ⟨21528430594682050847578909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28704574126242734463438545 21528430594682050847578909)
        ·
          refine ⟨8073161473005769067842091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21528430594682050847578909 8073161473005769067842091)
          ·
            refine ⟨12109742209508653601763137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8073161473005769067842091 12109742209508653601763137)
            ·
              refine ⟨9082306657131490201322353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12109742209508653601763137 9082306657131490201322353)
              ·
                refine ⟨6811729992848617650991765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9082306657131490201322353 6811729992848617650991765)
                ·
                  refine ⟨319299843414778952390239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6811729992848617650991765 319299843414778952390239)
                  ·
                    rfl

theorem cell21_1399127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 6].length) (baseStart_1399127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1399127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1399127 prefixEnd_1399127 := by exact prefixLift 1399127
  have htrace : WordTrace (prefixWord ++ tailWord_1399127) baseStart_1399127 baseEnd_1399127 := by
    simpa [prefixWord, tailWord_1399127, baseEnd_1399127] using wordTrace_append hprefix tailTrace_1399127
  have hstable : (prefixWord ++ tailWord_1399127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399127).length < 2 ^ (prefixWord ++ tailWord_1399127).sum := by decide
  have hdescent : baseEnd_1399127 < baseStart_1399127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399144 : List Nat := [2, 1, 4, 2, 2, 2, 1, 1, 6]
def baseStart_1399144 : Nat := 118140960795 + 1399144 * 2 ^ 59
def prefixEnd_1399144 : Nat := 4983230072969 + 3 ^ 40 * 1399144 * 2
def baseEnd_1399144 : Nat := 319303723046390700606871

theorem tailTrace_1399144 : CollatzResearch.WordTrace tailWord_1399144 prefixEnd_1399144 319303723046390700606871 := by
  unfold tailWord_1399144
  simp only [CollatzResearch.WordTrace]
  refine ⟨25515487021573858808074243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34020649362098478410765657 25515487021573858808074243)
  ·
    refine ⟨38273230532360788212111365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25515487021573858808074243 38273230532360788212111365)
    ·
      refine ⟨7176230724817647789770881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38273230532360788212111365 7176230724817647789770881)
      ·
        refine ⟨5382173043613235842328161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7176230724817647789770881 5382173043613235842328161)
        ·
          refine ⟨4036629782709926881746121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5382173043613235842328161 4036629782709926881746121)
          ·
            refine ⟨3027472337032445161309591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4036629782709926881746121 3027472337032445161309591)
            ·
              refine ⟨4541208505548667741964387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3027472337032445161309591 4541208505548667741964387)
              ·
                refine ⟨6811812758323001612946581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4541208505548667741964387 6811812758323001612946581)
                ·
                  refine ⟨319303723046390700606871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6811812758323001612946581 319303723046390700606871)
                  ·
                    rfl

theorem cell21_1399144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 6].length) (baseStart_1399144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1399144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1399144 prefixEnd_1399144 := by exact prefixLift 1399144
  have htrace : WordTrace (prefixWord ++ tailWord_1399144) baseStart_1399144 baseEnd_1399144 := by
    simpa [prefixWord, tailWord_1399144, baseEnd_1399144] using wordTrace_append hprefix tailTrace_1399144
  have hstable : (prefixWord ++ tailWord_1399144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399144).length < 2 ^ (prefixWord ++ tailWord_1399144).sum := by decide
  have hdescent : baseEnd_1399144 < baseStart_1399144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399203 : List Nat := [1, 1, 1, 4, 1, 4, 2, 1, 6]
def baseStart_1399203 : Nat := 118140960795 + 1399203 * 2 ^ 59
def prefixEnd_1399203 : Nat := 4983230072969 + 3 ^ 40 * 1399203 * 2
def baseEnd_1399203 : Nat := 319317187650219709123417

theorem tailTrace_1399203 : CollatzResearch.WordTrace tailWord_1399203 prefixEnd_1399203 319317187650219709123417 := by
  unfold tailWord_1399203
  simp only [CollatzResearch.WordTrace]
  refine ⟨51033125949933970692546263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34022083966622647128364175 51033125949933970692546263)
  ·
    refine ⟨76549688924900956038819395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51033125949933970692546263 76549688924900956038819395)
    ·
      refine ⟨114824533387351434058229093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76549688924900956038819395 114824533387351434058229093)
      ·
        refine ⟨21529600010128393885917955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114824533387351434058229093 21529600010128393885917955)
        ·
          refine ⟨32294400015192590828876933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21529600010128393885917955 32294400015192590828876933)
          ·
            refine ⟨6055200002848610780414425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32294400015192590828876933 6055200002848610780414425)
            ·
              refine ⟨4541400002136458085310819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6055200002848610780414425 4541400002136458085310819)
              ·
                refine ⟨6812100003204687127966229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4541400002136458085310819 6812100003204687127966229)
                ·
                  refine ⟨319317187650219709123417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6812100003204687127966229 319317187650219709123417)
                  ·
                    rfl

theorem cell21_1399203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 6].length) (baseStart_1399203 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1399203 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1399203 prefixEnd_1399203 := by exact prefixLift 1399203
  have htrace : WordTrace (prefixWord ++ tailWord_1399203) baseStart_1399203 baseEnd_1399203 := by
    simpa [prefixWord, tailWord_1399203, baseEnd_1399203] using wordTrace_append hprefix tailTrace_1399203
  have hstable : (prefixWord ++ tailWord_1399203).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399203).length < 2 ^ (prefixWord ++ tailWord_1399203).sum := by decide
  have hdescent : baseEnd_1399203 < baseStart_1399203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399282 : List Nat := [3, 2, 1, 4, 2, 1, 1, 2, 5]
def baseStart_1399282 : Nat := 118140960795 + 1399282 * 2 ^ 59
def prefixEnd_1399282 : Nat := 4983230072969 + 3 ^ 40 * 1399282 * 2
def baseEnd_1399282 : Nat := 319335216526533127306589

theorem tailTrace_1399282 : CollatzResearch.WordTrace tailWord_1399282 prefixEnd_1399282 319335216526533127306589 := by
  unfold tailWord_1399282
  simp only [CollatzResearch.WordTrace]
  refine ⟨12759001829161941796168025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34024004877765178123114733 12759001829161941796168025)
  ·
    refine ⟨9569251371871456347126019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12759001829161941796168025 9569251371871456347126019)
    ·
      refine ⟨14353877057807184520689029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9569251371871456347126019 14353877057807184520689029)
      ·
        refine ⟨2691351948338847097629193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14353877057807184520689029 2691351948338847097629193)
        ·
          refine ⟨2018513961254135323221895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2691351948338847097629193 2018513961254135323221895)
          ·
            refine ⟨3027770941881202984832843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2018513961254135323221895 3027770941881202984832843)
            ·
              refine ⟨4541656412821804477249265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3027770941881202984832843 4541656412821804477249265)
              ·
                refine ⟨3406242309616353357936949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4541656412821804477249265 3406242309616353357936949)
                ·
                  refine ⟨319335216526533127306589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3406242309616353357936949 319335216526533127306589)
                  ·
                    rfl

theorem cell21_1399282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_1399282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1399282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1399282 prefixEnd_1399282 := by exact prefixLift 1399282
  have htrace : WordTrace (prefixWord ++ tailWord_1399282) baseStart_1399282 baseEnd_1399282 := by
    simpa [prefixWord, tailWord_1399282, baseEnd_1399282] using wordTrace_append hprefix tailTrace_1399282
  have hstable : (prefixWord ++ tailWord_1399282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399282).length < 2 ^ (prefixWord ++ tailWord_1399282).sum := by decide
  have hdescent : baseEnd_1399282 < baseStart_1399282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399310 : List Nat := [4, 1, 1, 2, 3, 2, 8]
def baseStart_1399310 : Nat := 118140960795 + 1399310 * 2 ^ 59
def prefixEnd_1399310 : Nat := 4983230072969 + 3 ^ 40 * 1399310 * 2
def baseEnd_1399310 : Nat := 35482400723112366759985

theorem tailTrace_1399310 : CollatzResearch.WordTrace tailWord_1399310 prefixEnd_1399310 35482400723112366759985 := by
  unfold tailWord_1399310
  simp only [CollatzResearch.WordTrace]
  refine ⟨6379628570068290995836423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34024685707030885311127589 6379628570068290995836423)
  ·
    refine ⟨9569442855102436493754635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6379628570068290995836423 9569442855102436493754635)
    ·
      refine ⟨14354164282653654740631953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9569442855102436493754635 14354164282653654740631953)
      ·
        refine ⟨10765623211990241055473965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14354164282653654740631953 10765623211990241055473965)
        ·
          refine ⟨4037108704496340395802737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10765623211990241055473965 4037108704496340395802737)
          ·
            refine ⟨3027831528372255296852053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4037108704496340395802737 3027831528372255296852053)
            ·
              refine ⟨35482400723112366759985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3027831528372255296852053 35482400723112366759985)
              ·
                rfl

theorem cell21_1399310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 8].length) (baseStart_1399310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1399310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1399310 prefixEnd_1399310 := by exact prefixLift 1399310
  have htrace : WordTrace (prefixWord ++ tailWord_1399310) baseStart_1399310 baseEnd_1399310 := by
    simpa [prefixWord, tailWord_1399310, baseEnd_1399310] using wordTrace_append hprefix tailTrace_1399310
  have hstable : (prefixWord ++ tailWord_1399310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399310).length < 2 ^ (prefixWord ++ tailWord_1399310).sum := by decide
  have hdescent : baseEnd_1399310 < baseStart_1399310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399538 : List Nat := [3, 2, 1, 3, 1, 4, 7]
def baseStart_1399538 : Nat := 118140960795 + 1399538 * 2 ^ 59
def prefixEnd_1399538 : Nat := 4983230072969 + 3 ^ 40 * 1399538 * 2
def baseEnd_1399538 : Nat := 35488182134925952337711

theorem tailTrace_1399538 : CollatzResearch.WordTrace tailWord_1399538 prefixEnd_1399538 35488182134925952337711 := by
  unfold tailWord_1399538
  simp only [CollatzResearch.WordTrace]
  refine ⟨12761336100930080726497817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34030229602480215270660845 12761336100930080726497817)
  ·
    refine ⟨9571002075697560544873363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12761336100930080726497817 9571002075697560544873363)
    ·
      refine ⟨14356503113546340817310045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9571002075697560544873363 14356503113546340817310045)
      ·
        refine ⟨5383688667579877806491267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14356503113546340817310045 5383688667579877806491267)
        ·
          refine ⟨8075533001369816709736901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5383688667579877806491267 8075533001369816709736901)
          ·
            refine ⟨1514162437756840633075669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8075533001369816709736901 1514162437756840633075669)
            ·
              refine ⟨35488182134925952337711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1514162437756840633075669 35488182134925952337711)
              ·
                rfl

theorem cell21_1399538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 7].length) (baseStart_1399538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1399538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1399538 prefixEnd_1399538 := by exact prefixLift 1399538
  have htrace : WordTrace (prefixWord ++ tailWord_1399538) baseStart_1399538 baseEnd_1399538 := by
    simpa [prefixWord, tailWord_1399538, baseEnd_1399538] using wordTrace_append hprefix tailTrace_1399538
  have hstable : (prefixWord ++ tailWord_1399538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399538).length < 2 ^ (prefixWord ++ tailWord_1399538).sum := by decide
  have hdescent : baseEnd_1399538 < baseStart_1399538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399603 : List Nat := [1, 1, 1, 2, 6, 3, 2, 2, 3]
def baseStart_1399603 : Nat := 118140960795 + 1399603 * 2 ^ 59
def prefixEnd_1399603 : Nat := 4983230072969 + 3 ^ 40 * 1399603 * 2
def baseEnd_1399603 : Nat := 319408473099907902455933

theorem tailTrace_1399603 : CollatzResearch.WordTrace tailWord_1399603 prefixEnd_1399603 319408473099907902455933 := by
  unfold tailWord_1399603
  simp only [CollatzResearch.WordTrace]
  refine ⟨51047715148484839007107463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34031810098989892671404975 51047715148484839007107463)
  ·
    refine ⟨76571572722727258510661195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51047715148484839007107463 76571572722727258510661195)
    ·
      refine ⟨114857359084090887765991793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76571572722727258510661195 114857359084090887765991793)
      ·
        refine ⟨86143019313068165824493845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114857359084090887765991793 86143019313068165824493845)
        ·
          refine ⟨4037954030300070273023149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 86143019313068165824493845 4037954030300070273023149)
          ·
            refine ⟨1514232761362526352383681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4037954030300070273023149 1514232761362526352383681)
            ·
              refine ⟨1135674571021894764287761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1514232761362526352383681 1135674571021894764287761)
              ·
                refine ⟨851755928266421073215821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1135674571021894764287761 851755928266421073215821)
                ·
                  refine ⟨319408473099907902455933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 851755928266421073215821 319408473099907902455933)
                  ·
                    rfl

theorem cell21_1399603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2, 3].length) (baseStart_1399603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1399603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1399603 prefixEnd_1399603 := by exact prefixLift 1399603
  have htrace : WordTrace (prefixWord ++ tailWord_1399603) baseStart_1399603 baseEnd_1399603 := by
    simpa [prefixWord, tailWord_1399603, baseEnd_1399603] using wordTrace_append hprefix tailTrace_1399603
  have hstable : (prefixWord ++ tailWord_1399603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399603).length < 2 ^ (prefixWord ++ tailWord_1399603).sum := by decide
  have hdescent : baseEnd_1399603 < baseStart_1399603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399628 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 7]
def baseStart_1399628 : Nat := 118140960795 + 1399628 * 2 ^ 59
def prefixEnd_1399628 : Nat := 4983230072969 + 3 ^ 40 * 1399628 * 2
def baseEnd_1399628 : Nat := 319414178440513414539215

theorem tailTrace_1399628 : CollatzResearch.WordTrace tailWord_1399628 prefixEnd_1399628 319414178440513414539215 := by
  unfold tailWord_1399628
  simp only [CollatzResearch.WordTrace]
  refine ⟨25524313486697134138383769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34032417982262845517845025 25524313486697134138383769)
  ·
    refine ⟨19143235115022850603787827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25524313486697134138383769 19143235115022850603787827)
    ·
      refine ⟨28714852672534275905681741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19143235115022850603787827 28714852672534275905681741)
      ·
        refine ⟨10768069752200353464630653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28714852672534275905681741 10768069752200353464630653)
        ·
          refine ⟨4038026157075132549236495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10768069752200353464630653 4038026157075132549236495)
          ·
            refine ⟨6057039235612698823854743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4038026157075132549236495 6057039235612698823854743)
            ·
              refine ⟨9085558853419048235782115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6057039235612698823854743 9085558853419048235782115)
              ·
                refine ⟨13628338280128572353673173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9085558853419048235782115 13628338280128572353673173)
                ·
                  refine ⟨319414178440513414539215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13628338280128572353673173 319414178440513414539215)
                  ·
                    rfl

theorem cell21_1399628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_1399628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1399628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1399628 prefixEnd_1399628 := by exact prefixLift 1399628
  have htrace : WordTrace (prefixWord ++ tailWord_1399628) baseStart_1399628 baseEnd_1399628 := by
    simpa [prefixWord, tailWord_1399628, baseEnd_1399628] using wordTrace_append hprefix tailTrace_1399628
  have hstable : (prefixWord ++ tailWord_1399628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399628).length < 2 ^ (prefixWord ++ tailWord_1399628).sum := by decide
  have hdescent : baseEnd_1399628 < baseStart_1399628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399659 : List Nat := [1, 1, 1, 1, 2, 2, 7, 2, 4]
def baseStart_1399659 : Nat := 118140960795 + 1399659 * 2 ^ 59
def prefixEnd_1399659 : Nat := 4983230072969 + 3 ^ 40 * 1399659 * 2
def baseEnd_1399659 : Nat := 319421253062864249522485

theorem tailTrace_1399659 : CollatzResearch.WordTrace tailWord_1399659 prefixEnd_1399659 319421253062864249522485 := by
  unfold tailWord_1399659
  simp only [CollatzResearch.WordTrace]
  refine ⟨51049757636281960571146031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34033171757521307047430687 51049757636281960571146031)
  ·
    refine ⟨76574636454422940856719047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51049757636281960571146031 76574636454422940856719047)
    ·
      refine ⟨114861954681634411285078571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76574636454422940856719047 114861954681634411285078571)
      ·
        refine ⟨172292932022451616927617857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114861954681634411285078571 172292932022451616927617857)
        ·
          refine ⟨129219699016838712695713393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172292932022451616927617857 129219699016838712695713393)
          ·
            refine ⟨96914774262629034521785045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129219699016838712695713393 96914774262629034521785045)
            ·
              refine ⟨2271440021780367996604337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 96914774262629034521785045 2271440021780367996604337)
              ·
                refine ⟨1703580016335275997453253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2271440021780367996604337 1703580016335275997453253)
                ·
                  refine ⟨319421253062864249522485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1703580016335275997453253 319421253062864249522485)
                  ·
                    rfl

theorem cell21_1399659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 4].length) (baseStart_1399659 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1399659 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1399659 prefixEnd_1399659 := by exact prefixLift 1399659
  have htrace : WordTrace (prefixWord ++ tailWord_1399659) baseStart_1399659 baseEnd_1399659 := by
    simpa [prefixWord, tailWord_1399659, baseEnd_1399659] using wordTrace_append hprefix tailTrace_1399659
  have hstable : (prefixWord ++ tailWord_1399659).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399659).length < 2 ^ (prefixWord ++ tailWord_1399659).sum := by decide
  have hdescent : baseEnd_1399659 < baseStart_1399659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399662 : List Nat := [4, 1, 2, 3, 2, 1, 2, 1, 5]
def baseStart_1399662 : Nat := 118140960795 + 1399662 * 2 ^ 59
def prefixEnd_1399662 : Nat := 4983230072969 + 3 ^ 40 * 1399662 * 2
def baseEnd_1399662 : Nat := 319421937703736910972479

theorem tailTrace_1399662 : CollatzResearch.WordTrace tailWord_1399662 prefixEnd_1399662 319421937703736910972479 := by
  unfold tailWord_1399662
  simp only [CollatzResearch.WordTrace]
  refine ⟨6381233381908886510438155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34033244703514061389003493 6381233381908886510438155)
  ·
    refine ⟨9571850072863329765657233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6381233381908886510438155 9571850072863329765657233)
    ·
      refine ⟨7178887554647497324242925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9571850072863329765657233 7178887554647497324242925)
      ·
        refine ⟨2692082832992811496591097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7178887554647497324242925 2692082832992811496591097)
        ·
          refine ⟨2019062124744608622443323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2692082832992811496591097 2019062124744608622443323)
          ·
            refine ⟨3028593187116912933664985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2019062124744608622443323 3028593187116912933664985)
            ·
              refine ⟨2271444890337684700248739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3028593187116912933664985 2271444890337684700248739)
              ·
                refine ⟨3407167335506527050373109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2271444890337684700248739 3407167335506527050373109)
                ·
                  refine ⟨319421937703736910972479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3407167335506527050373109 319421937703736910972479)
                  ·
                    rfl

theorem cell21_1399662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_1399662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1399662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1399662 prefixEnd_1399662 := by exact prefixLift 1399662
  have htrace : WordTrace (prefixWord ++ tailWord_1399662) baseStart_1399662 baseEnd_1399662 := by
    simpa [prefixWord, tailWord_1399662, baseEnd_1399662] using wordTrace_append hprefix tailTrace_1399662
  have hstable : (prefixWord ++ tailWord_1399662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399662).length < 2 ^ (prefixWord ++ tailWord_1399662).sum := by decide
  have hdescent : baseEnd_1399662 < baseStart_1399662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399682 : List Nat := [3, 4, 2, 2, 2, 1, 2, 5]
def baseStart_1399682 : Nat := 118140960795 + 1399682 * 2 ^ 59
def prefixEnd_1399682 : Nat := 4983230072969 + 3 ^ 40 * 1399682 * 2
def baseEnd_1399682 : Nat := 106475500658740440213035

theorem tailTrace_1399682 : CollatzResearch.WordTrace tailWord_1399682 prefixEnd_1399682 106475500658740440213035 := by
  unfold tailWord_1399682
  simp only [CollatzResearch.WordTrace]
  refine ⟨12762649128799658874808325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34033731010132423666155533 12762649128799658874808325)
  ·
    refine ⟨2392996711649936039026561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12762649128799658874808325 2392996711649936039026561)
    ·
      refine ⟨1794747533737452029269921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2392996711649936039026561 1794747533737452029269921)
      ·
        refine ⟨1346060650303089021952441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1794747533737452029269921 1346060650303089021952441)
        ·
          refine ⟨1009545487727316766464331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1346060650303089021952441 1009545487727316766464331)
          ·
            refine ⟨1514318231590975149696497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1009545487727316766464331 1514318231590975149696497)
            ·
              refine ⟨1135738673693231362272373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1514318231590975149696497 1135738673693231362272373)
              ·
                refine ⟨106475500658740440213035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1135738673693231362272373 106475500658740440213035)
                ·
                  rfl

theorem cell21_1399682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 5].length) (baseStart_1399682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1399682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1399682 prefixEnd_1399682 := by exact prefixLift 1399682
  have htrace : WordTrace (prefixWord ++ tailWord_1399682) baseStart_1399682 baseEnd_1399682 := by
    simpa [prefixWord, tailWord_1399682, baseEnd_1399682] using wordTrace_append hprefix tailTrace_1399682
  have hstable : (prefixWord ++ tailWord_1399682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399682).length < 2 ^ (prefixWord ++ tailWord_1399682).sum := by decide
  have hdescent : baseEnd_1399682 < baseStart_1399682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399690 : List Nat := [3, 1, 2, 4, 1, 2, 1, 7]
def baseStart_1399690 : Nat := 118140960795 + 1399690 * 2 ^ 59
def prefixEnd_1399690 : Nat := 4983230072969 + 3 ^ 40 * 1399690 * 2
def baseEnd_1399690 : Nat := 106476109228405028168585

theorem tailTrace_1399690 : CollatzResearch.WordTrace tailWord_1399690 prefixEnd_1399690 106476109228405028168585 := by
  unfold tailWord_1399690
  simp only [CollatzResearch.WordTrace]
  refine ⟨12762722074792413216381131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34033925532779768577016349 12762722074792413216381131)
  ·
    refine ⟨19144083112188619824571697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12762722074792413216381131 19144083112188619824571697)
    ·
      refine ⟨14358062334141464868428773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19144083112188619824571697 14358062334141464868428773)
      ·
        refine ⟨2692136687651524662830395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14358062334141464868428773 2692136687651524662830395)
        ·
          refine ⟨4038205031477286994245593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2692136687651524662830395 4038205031477286994245593)
          ·
            refine ⟨3028653773607965245684195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4038205031477286994245593 3028653773607965245684195)
            ·
              refine ⟨4542980660411947868526293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3028653773607965245684195 4542980660411947868526293)
              ·
                refine ⟨106476109228405028168585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4542980660411947868526293 106476109228405028168585)
                ·
                  rfl

theorem cell21_1399690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 7].length) (baseStart_1399690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1399690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1399690 prefixEnd_1399690 := by exact prefixLift 1399690
  have htrace : WordTrace (prefixWord ++ tailWord_1399690) baseStart_1399690 baseEnd_1399690 := by
    simpa [prefixWord, tailWord_1399690, baseEnd_1399690] using wordTrace_append hprefix tailTrace_1399690
  have hstable : (prefixWord ++ tailWord_1399690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399690).length < 2 ^ (prefixWord ++ tailWord_1399690).sum := by decide
  have hdescent : baseEnd_1399690 < baseStart_1399690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399766 : List Nat := [5, 2, 1, 1, 2, 10]
def baseStart_1399766 : Nat := 118140960795 + 1399766 * 2 ^ 59
def prefixEnd_1399766 : Nat := 4983230072969 + 3 ^ 40 * 1399766 * 2
def baseEnd_1399766 : Nat := 11831321182246512638479

theorem tailTrace_1399766 : CollatzResearch.WordTrace tailWord_1399766 prefixEnd_1399766 11831321182246512638479 := by
  unfold tailWord_1399766
  simp only [CollatzResearch.WordTrace]
  refine ⟨3190853765430894865330697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34035773497929545230194101 3190853765430894865330697)
  ·
    refine ⟨2393140324073171148998023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3190853765430894865330697 2393140324073171148998023)
    ·
      refine ⟨3589710486109756723497035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2393140324073171148998023 3589710486109756723497035)
      ·
        refine ⟨5384565729164635085245553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3589710486109756723497035 5384565729164635085245553)
        ·
          refine ⟨4038424296873476313934165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5384565729164635085245553 4038424296873476313934165)
          ·
            refine ⟨11831321182246512638479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4038424296873476313934165 11831321182246512638479)
            ·
              rfl

theorem cell21_1399766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 10].length) (baseStart_1399766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1399766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1399766 prefixEnd_1399766 := by exact prefixLift 1399766
  have htrace : WordTrace (prefixWord ++ tailWord_1399766) baseStart_1399766 baseEnd_1399766 := by
    simpa [prefixWord, tailWord_1399766, baseEnd_1399766] using wordTrace_append hprefix tailTrace_1399766
  have hstable : (prefixWord ++ tailWord_1399766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399766).length < 2 ^ (prefixWord ++ tailWord_1399766).sum := by decide
  have hdescent : baseEnd_1399766 < baseStart_1399766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399991 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 7]
def baseStart_1399991 : Nat := 118140960795 + 1399991 * 2 ^ 59
def prefixEnd_1399991 : Nat := 4983230072969 + 3 ^ 40 * 1399991 * 2
def baseEnd_1399991 : Nat := 319497019986105449988473

theorem tailTrace_1399991 : CollatzResearch.WordTrace tailWord_1399991 prefixEnd_1399991 319497019986105449988473 := by
  unfold tailWord_1399991
  simp only [CollatzResearch.WordTrace]
  refine ⟨51061866671079181272231827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34041244447386120848154551 51061866671079181272231827)
  ·
    refine ⟨76592800006618771908347741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51061866671079181272231827 76592800006618771908347741)
    ·
      refine ⟨28722300002482039465630403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76592800006618771908347741 28722300002482039465630403)
      ·
        refine ⟨43083450003723059198445605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28722300002482039465630403 43083450003723059198445605)
        ·
          refine ⟨8078146875698073599708551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43083450003723059198445605 8078146875698073599708551)
          ·
            refine ⟨12117220313547110399562827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8078146875698073599708551 12117220313547110399562827)
            ·
              refine ⟨18175830470320665599344241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12117220313547110399562827 18175830470320665599344241)
              ·
                refine ⟨13631872852740499199508181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18175830470320665599344241 13631872852740499199508181)
                ·
                  refine ⟨319497019986105449988473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13631872852740499199508181 319497019986105449988473)
                  ·
                    rfl

theorem cell21_1399991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 7].length) (baseStart_1399991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1399991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1399991 prefixEnd_1399991 := by exact prefixLift 1399991
  have htrace : WordTrace (prefixWord ++ tailWord_1399991) baseStart_1399991 baseEnd_1399991 := by
    simpa [prefixWord, tailWord_1399991, baseEnd_1399991] using wordTrace_append hprefix tailTrace_1399991
  have hstable : (prefixWord ++ tailWord_1399991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399991).length < 2 ^ (prefixWord ++ tailWord_1399991).sum := by decide
  have hdescent : baseEnd_1399991 < baseStart_1399991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400042 : List Nat := [3, 1, 3, 1, 1, 5, 1, 3, 3]
def baseStart_1400042 : Nat := 118140960795 + 1400042 * 2 ^ 59
def prefixEnd_1400042 : Nat := 4983230072969 + 3 ^ 40 * 1400042 * 2
def baseEnd_1400042 : Nat := 319508658880940694638369

theorem tailTrace_1400042 : CollatzResearch.WordTrace tailWord_1400042 prefixEnd_1400042 319508658880940694638369 := by
  unfold tailWord_1400042
  simp only [CollatzResearch.WordTrace]
  refine ⟨12765931698473604245584595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34042484529262944654892253 12765931698473604245584595)
  ·
    refine ⟨19148897547710406368376893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12765931698473604245584595 19148897547710406368376893)
    ·
      refine ⟨7180836580391402388141335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19148897547710406368376893 7180836580391402388141335)
      ·
        refine ⟨10771254870587103582212003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7180836580391402388141335 10771254870587103582212003)
        ·
          refine ⟨16156882305880655373318005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10771254870587103582212003 16156882305880655373318005)
          ·
            refine ⟨1514707716176311441248563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16156882305880655373318005 1514707716176311441248563)
            ·
              refine ⟨2272061574264467161872845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1514707716176311441248563 2272061574264467161872845)
              ·
                refine ⟨852023090349175185702317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2272061574264467161872845 852023090349175185702317)
                ·
                  refine ⟨319508658880940694638369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 852023090349175185702317 319508658880940694638369)
                  ·
                    rfl

theorem cell21_1400042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3, 3].length) (baseStart_1400042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1400042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1400042 prefixEnd_1400042 := by exact prefixLift 1400042
  have htrace : WordTrace (prefixWord ++ tailWord_1400042) baseStart_1400042 baseEnd_1400042 := by
    simpa [prefixWord, tailWord_1400042, baseEnd_1400042] using wordTrace_append hprefix tailTrace_1400042
  have hstable : (prefixWord ++ tailWord_1400042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400042).length < 2 ^ (prefixWord ++ tailWord_1400042).sum := by decide
  have hdescent : baseEnd_1400042 < baseStart_1400042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400115 : List Nat := [1, 1, 1, 2, 5, 3, 2, 2, 4]
def baseStart_1400115 : Nat := 118140960795 + 1400115 * 2 ^ 59
def prefixEnd_1400115 : Nat := 4983230072969 + 3 ^ 40 * 1400115 * 2
def baseEnd_1400115 : Nat := 319525318475508789921553

theorem tailTrace_1400115 : CollatzResearch.WordTrace tailWord_1400115 prefixEnd_1400115 319525318475508789921553 := by
  unfold tailWord_1400115
  simp only [CollatzResearch.WordTrace]
  refine ⟨51066389322629950449745799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34044259548419966966497199 51066389322629950449745799)
  ·
    refine ⟨76599583983944925674618699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51066389322629950449745799 76599583983944925674618699)
    ·
      refine ⟨114899375975917388511928049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76599583983944925674618699 114899375975917388511928049)
      ·
        refine ⟨86174531981938041383946037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114899375975917388511928049 86174531981938041383946037)
        ·
          refine ⟨8078862373306691379744941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86174531981938041383946037 8078862373306691379744941)
          ·
            refine ⟨3029573389990009267404353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8078862373306691379744941 3029573389990009267404353)
            ·
              refine ⟨2272180042492506950553265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3029573389990009267404353 2272180042492506950553265)
              ·
                refine ⟨1704135031869380212914949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2272180042492506950553265 1704135031869380212914949)
                ·
                  refine ⟨319525318475508789921553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1704135031869380212914949 319525318475508789921553)
                  ·
                    rfl

theorem cell21_1400115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 4].length) (baseStart_1400115 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1400115 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1400115 prefixEnd_1400115 := by exact prefixLift 1400115
  have htrace : WordTrace (prefixWord ++ tailWord_1400115) baseStart_1400115 baseEnd_1400115 := by
    simpa [prefixWord, tailWord_1400115, baseEnd_1400115] using wordTrace_append hprefix tailTrace_1400115
  have hstable : (prefixWord ++ tailWord_1400115).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400115).length < 2 ^ (prefixWord ++ tailWord_1400115).sum := by decide
  have hdescent : baseEnd_1400115 < baseStart_1400115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400132 : List Nat := [2, 3, 4, 1, 1, 1, 2, 3, 4]
def baseStart_1400132 : Nat := 118140960795 + 1400132 * 2 ^ 59
def prefixEnd_1400132 : Nat := 4983230072969 + 3 ^ 40 * 1400132 * 2
def baseEnd_1400132 : Nat := 319529198107120538138185

theorem tailTrace_1400132 : CollatzResearch.WordTrace tailWord_1400132 prefixEnd_1400132 319529198107120538138185 := by
  unfold tailWord_1400132
  simp only [CollatzResearch.WordTrace]
  refine ⟨25533504681784181176557325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34044672909045574902076433 25533504681784181176557325)
  ·
    refine ⟨9575064255669067941208997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25533504681784181176557325 9575064255669067941208997)
    ·
      refine ⟨1795324547937950238976687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9575064255669067941208997 1795324547937950238976687)
      ·
        refine ⟨2692986821906925358465031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1795324547937950238976687 2692986821906925358465031)
        ·
          refine ⟨4039480232860388037697547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2692986821906925358465031 4039480232860388037697547)
          ·
            refine ⟨6059220349290582056546321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4039480232860388037697547 6059220349290582056546321)
            ·
              refine ⟨4544415261967936542409741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6059220349290582056546321 4544415261967936542409741)
              ·
                refine ⟨1704155723237976203403653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4544415261967936542409741 1704155723237976203403653)
                ·
                  refine ⟨319529198107120538138185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1704155723237976203403653 319529198107120538138185)
                  ·
                    rfl

theorem cell21_1400132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_1400132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1400132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1400132 prefixEnd_1400132 := by exact prefixLift 1400132
  have htrace : WordTrace (prefixWord ++ tailWord_1400132) baseStart_1400132 baseEnd_1400132 := by
    simpa [prefixWord, tailWord_1400132, baseEnd_1400132] using wordTrace_append hprefix tailTrace_1400132
  have hstable : (prefixWord ++ tailWord_1400132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400132).length < 2 ^ (prefixWord ++ tailWord_1400132).sum := by decide
  have hdescent : baseEnd_1400132 < baseStart_1400132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400188 : List Nat := [2, 2, 2, 1, 1, 1, 4, 8]
def baseStart_1400188 : Nat := 118140960795 + 1400188 * 2 ^ 59
def prefixEnd_1400188 : Nat := 4983230072969 + 3 ^ 40 * 1400188 * 2
def baseEnd_1400188 : Nat := 106513992690025628401579

theorem tailTrace_1400188 : CollatzResearch.WordTrace tailWord_1400188 prefixEnd_1400188 106513992690025628401579 := by
  unfold tailWord_1400188
  simp only [CollatzResearch.WordTrace]
  refine ⟨25534525925682741958576609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34046034567576989278102145 25534525925682741958576609)
  ·
    refine ⟨19150894444262056468932457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25534525925682741958576609 19150894444262056468932457)
    ·
      refine ⟨14363170833196542351699343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19150894444262056468932457 14363170833196542351699343)
      ·
        refine ⟨21544756249794813527549015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14363170833196542351699343 21544756249794813527549015)
        ·
          refine ⟨32317134374692220291323523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21544756249794813527549015 32317134374692220291323523)
          ·
            refine ⟨48475701562038330436985285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32317134374692220291323523 48475701562038330436985285)
            ·
              refine ⟨9089194042882186956934741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48475701562038330436985285 9089194042882186956934741)
              ·
                refine ⟨106513992690025628401579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9089194042882186956934741 106513992690025628401579)
                ·
                  rfl

theorem cell21_1400188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 8].length) (baseStart_1400188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1400188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1400188 prefixEnd_1400188 := by exact prefixLift 1400188
  have htrace : WordTrace (prefixWord ++ tailWord_1400188) baseStart_1400188 baseEnd_1400188 := by
    simpa [prefixWord, tailWord_1400188, baseEnd_1400188] using wordTrace_append hprefix tailTrace_1400188
  have hstable : (prefixWord ++ tailWord_1400188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400188).length < 2 ^ (prefixWord ++ tailWord_1400188).sum := by decide
  have hdescent : baseEnd_1400188 < baseStart_1400188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400236 : List Nat := [2, 2, 1, 1, 1, 1, 4, 6, 3]
def baseStart_1400236 : Nat := 118140960795 + 1400236 * 2 ^ 59
def prefixEnd_1400236 : Nat := 4983230072969 + 3 ^ 40 * 1400236 * 2
def baseEnd_1400236 : Nat := 319552932324039468404639

theorem tailTrace_1400236 : CollatzResearch.WordTrace tailWord_1400236 prefixEnd_1400236 319552932324039468404639 := by
  unfold tailWord_1400236
  simp only [CollatzResearch.WordTrace]
  refine ⟨25535401277595794057450281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34047201703461058743267041 25535401277595794057450281)
  ·
    refine ⟨19151550958196845543087711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25535401277595794057450281 19151550958196845543087711)
    ·
      refine ⟨28727326437295268314631567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19151550958196845543087711 28727326437295268314631567)
      ·
        refine ⟨43090989655942902471947351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28727326437295268314631567 43090989655942902471947351)
        ·
          refine ⟨64636484483914353707921027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43090989655942902471947351 64636484483914353707921027)
          ·
            refine ⟨96954726725871530561881541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64636484483914353707921027 96954726725871530561881541)
            ·
              refine ⟨18179011261100911980352789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96954726725871530561881541 18179011261100911980352789)
              ·
                refine ⟨852141152864105249079037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18179011261100911980352789 852141152864105249079037)
                ·
                  refine ⟨319552932324039468404639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 852141152864105249079037 319552932324039468404639)
                  ·
                    rfl

theorem cell21_1400236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6, 3].length) (baseStart_1400236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1400236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1400236 prefixEnd_1400236 := by exact prefixLift 1400236
  have htrace : WordTrace (prefixWord ++ tailWord_1400236) baseStart_1400236 baseEnd_1400236 := by
    simpa [prefixWord, tailWord_1400236, baseEnd_1400236] using wordTrace_append hprefix tailTrace_1400236
  have hstable : (prefixWord ++ tailWord_1400236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400236).length < 2 ^ (prefixWord ++ tailWord_1400236).sum := by decide
  have hdescent : baseEnd_1400236 < baseStart_1400236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400264 : List Nat := [2, 1, 3, 1, 3, 1, 1, 9]
def baseStart_1400264 : Nat := 118140960795 + 1400264 * 2 ^ 59
def prefixEnd_1400264 : Nat := 4983230072969 + 3 ^ 40 * 1400264 * 2
def baseEnd_1400264 : Nat := 106519774101839213979305

theorem tailTrace_1400264 : CollatzResearch.WordTrace tailWord_1400264 prefixEnd_1400264 106519774101839213979305 := by
  unfold tailWord_1400264
  simp only [CollatzResearch.WordTrace]
  refine ⟨25535911899545074448459923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34047882532726765931279897 25535911899545074448459923)
  ·
    refine ⟨38303867849317611672689885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25535911899545074448459923 38303867849317611672689885)
    ·
      refine ⟨14363950443494104377258707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38303867849317611672689885 14363950443494104377258707)
      ·
        refine ⟨21545925665241156565888061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14363950443494104377258707 21545925665241156565888061)
        ·
          refine ⟨8079722124465433712208023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21545925665241156565888061 8079722124465433712208023)
          ·
            refine ⟨12119583186698150568312035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8079722124465433712208023 12119583186698150568312035)
            ·
              refine ⟨18179374780047225852468053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12119583186698150568312035 18179374780047225852468053)
              ·
                refine ⟨106519774101839213979305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18179374780047225852468053 106519774101839213979305)
                ·
                  rfl

theorem cell21_1400264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 9].length) (baseStart_1400264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1400264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1400264 prefixEnd_1400264 := by exact prefixLift 1400264
  have htrace : WordTrace (prefixWord ++ tailWord_1400264) baseStart_1400264 baseEnd_1400264 := by
    simpa [prefixWord, tailWord_1400264, baseEnd_1400264] using wordTrace_append hprefix tailTrace_1400264
  have hstable : (prefixWord ++ tailWord_1400264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400264).length < 2 ^ (prefixWord ++ tailWord_1400264).sum := by decide
  have hdescent : baseEnd_1400264 < baseStart_1400264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400298 : List Nat := [3, 1, 3, 1, 4, 2, 1, 6]
def baseStart_1400298 : Nat := 118140960795 + 1400298 * 2 ^ 59
def prefixEnd_1400298 : Nat := 4983230072969 + 3 ^ 40 * 1400298 * 2
def baseEnd_1400298 : Nat := 106522360522913712790393

theorem tailTrace_1400298 : CollatzResearch.WordTrace tailWord_1400298 prefixEnd_1400298 106522360522913712790393 := by
  unfold tailWord_1400298
  simp only [CollatzResearch.WordTrace]
  refine ⟨12768265970241743175914387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34048709253977981802438365 12768265970241743175914387)
  ·
    refine ⟨19152398955362614763871581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12768265970241743175914387 19152398955362614763871581)
    ·
      refine ⟨7182149608260980536451843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19152398955362614763871581 7182149608260980536451843)
      ·
        refine ⟨10773224412391470804677765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7182149608260980536451843 10773224412391470804677765)
        ·
          refine ⟨2019979577323400775877081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10773224412391470804677765 2019979577323400775877081)
          ·
            refine ⟨1514984682992550581907811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2019979577323400775877081 1514984682992550581907811)
            ·
              refine ⟨2272477024488825872861717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1514984682992550581907811 2272477024488825872861717)
              ·
                refine ⟨106522360522913712790393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2272477024488825872861717 106522360522913712790393)
                ·
                  rfl

theorem cell21_1400298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 6].length) (baseStart_1400298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1400298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1400298 prefixEnd_1400298 := by exact prefixLift 1400298
  have htrace : WordTrace (prefixWord ++ tailWord_1400298) baseStart_1400298 baseEnd_1400298 := by
    simpa [prefixWord, tailWord_1400298, baseEnd_1400298] using wordTrace_append hprefix tailTrace_1400298
  have hstable : (prefixWord ++ tailWord_1400298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400298).length < 2 ^ (prefixWord ++ tailWord_1400298).sum := by decide
  have hdescent : baseEnd_1400298 < baseStart_1400298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400371 : List Nat := [1, 1, 1, 2, 4, 3, 2, 2, 5]
def baseStart_1400371 : Nat := 118140960795 + 1400371 * 2 ^ 59
def prefixEnd_1400371 : Nat := 4983230072969 + 3 ^ 40 * 1400371 * 2
def baseEnd_1400371 : Nat := 319583741163309233654363

theorem tailTrace_1400371 : CollatzResearch.WordTrace tailWord_1400371 prefixEnd_1400371 319583741163309233654363 := by
  unfold tailWord_1400371
  simp only [CollatzResearch.WordTrace]
  refine ⟨51075726409702506171064967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34050484273135004114043311 51075726409702506171064967)
  ·
    refine ⟨76613589614553759256597451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51075726409702506171064967 76613589614553759256597451)
    ·
      refine ⟨114920384421830638884896177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76613589614553759256597451 114920384421830638884896177)
      ·
        refine ⟨86190288316372979163672133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114920384421830638884896177 86190288316372979163672133)
        ·
          refine ⟨16160679059319933593188525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86190288316372979163672133 16160679059319933593188525)
          ·
            refine ⟨6060254647244975097445697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16160679059319933593188525 6060254647244975097445697)
            ·
              refine ⟨4545190985433731323084273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6060254647244975097445697 4545190985433731323084273)
              ·
                refine ⟨3408893239075298492313205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4545190985433731323084273 3408893239075298492313205)
                ·
                  refine ⟨319583741163309233654363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3408893239075298492313205 319583741163309233654363)
                  ·
                    rfl

theorem cell21_1400371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 5].length) (baseStart_1400371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1400371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1400371 prefixEnd_1400371 := by exact prefixLift 1400371
  have htrace : WordTrace (prefixWord ++ tailWord_1400371) baseStart_1400371 baseEnd_1400371 := by
    simpa [prefixWord, tailWord_1400371, baseEnd_1400371] using wordTrace_append hprefix tailTrace_1400371
  have hstable : (prefixWord ++ tailWord_1400371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400371).length < 2 ^ (prefixWord ++ tailWord_1400371).sum := by decide
  have hdescent : baseEnd_1400371 < baseStart_1400371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400374 : List Nat := [5, 1, 2, 1, 3, 1, 1, 7]
def baseStart_1400374 : Nat := 118140960795 + 1400374 * 2 ^ 59
def prefixEnd_1400374 : Nat := 4983230072969 + 3 ^ 40 * 1400374 * 2
def baseEnd_1400374 : Nat := 106528141934727298368119

theorem tailTrace_1400374 : CollatzResearch.WordTrace tailWord_1400374 prefixEnd_1400374 106528141934727298368119 := by
  unfold tailWord_1400374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3192239739293227355214011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34050557219127758455616117 3192239739293227355214011)
  ·
    refine ⟨4788359608939841032821017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3192239739293227355214011 4788359608939841032821017)
    ·
      refine ⟨3591269706704880774615763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4788359608939841032821017 3591269706704880774615763)
      ·
        refine ⟨5386904560057321161923645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3591269706704880774615763 5386904560057321161923645)
        ·
          refine ⟨2020089210021495435721367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5386904560057321161923645 2020089210021495435721367)
          ·
            refine ⟨3030133815032243153582051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2020089210021495435721367 3030133815032243153582051)
            ·
              refine ⟨4545200722548364730373077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3030133815032243153582051 4545200722548364730373077)
              ·
                refine ⟨106528141934727298368119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4545200722548364730373077 106528141934727298368119)
                ·
                  rfl

theorem cell21_1400374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_1400374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1400374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1400374 prefixEnd_1400374 := by exact prefixLift 1400374
  have htrace : WordTrace (prefixWord ++ tailWord_1400374) baseStart_1400374 baseEnd_1400374 := by
    simpa [prefixWord, tailWord_1400374, baseEnd_1400374] using wordTrace_append hprefix tailTrace_1400374
  have hstable : (prefixWord ++ tailWord_1400374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400374).length < 2 ^ (prefixWord ++ tailWord_1400374).sum := by decide
  have hdescent : baseEnd_1400374 < baseStart_1400374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400402 : List Nat := [3, 2, 2, 1, 2, 2, 2, 1, 6]
def baseStart_1400402 : Nat := 118140960795 + 1400402 * 2 ^ 59
def prefixEnd_1400402 : Nat := 4983230072969 + 3 ^ 40 * 1400402 * 2
def baseEnd_1400402 : Nat := 319590815785660068637633

theorem tailTrace_1400402 : CollatzResearch.WordTrace tailWord_1400402 prefixEnd_1400402 319590815785660068637633 := by
  unfold tailWord_1400402
  simp only [CollatzResearch.WordTrace]
  refine ⟨12769214268147549616360865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34051238048393465643628973 12769214268147549616360865)
  ·
    refine ⟨9576910701110662212270649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12769214268147549616360865 9576910701110662212270649)
    ·
      refine ⟨7182683025832996659202987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9576910701110662212270649 7182683025832996659202987)
      ·
        refine ⟨10774024538749494988804481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7182683025832996659202987 10774024538749494988804481)
        ·
          refine ⟨8080518404062121241603361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10774024538749494988804481 8080518404062121241603361)
          ·
            refine ⟨6060388803046590931202521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8080518404062121241603361 6060388803046590931202521)
            ·
              refine ⟨4545291602284943198401891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6060388803046590931202521 4545291602284943198401891)
              ·
                refine ⟨6817937403427414797602837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4545291602284943198401891 6817937403427414797602837)
                ·
                  refine ⟨319590815785660068637633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6817937403427414797602837 319590815785660068637633)
                  ·
                    rfl

theorem cell21_1400402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_1400402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1400402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1400402 prefixEnd_1400402 := by exact prefixLift 1400402
  have htrace : WordTrace (prefixWord ++ tailWord_1400402) baseStart_1400402 baseEnd_1400402 := by
    simpa [prefixWord, tailWord_1400402, baseEnd_1400402] using wordTrace_append hprefix tailTrace_1400402
  have hstable : (prefixWord ++ tailWord_1400402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400402).length < 2 ^ (prefixWord ++ tailWord_1400402).sum := by decide
  have hdescent : baseEnd_1400402 < baseStart_1400402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400419 : List Nat := [1, 1, 1, 5, 1, 3, 4, 1, 4]
def baseStart_1400419 : Nat := 118140960795 + 1400419 * 2 ^ 59
def prefixEnd_1400419 : Nat := 4983230072969 + 3 ^ 40 * 1400419 * 2
def baseEnd_1400419 : Nat := 319594695417271816854265

theorem tailTrace_1400419 : CollatzResearch.WordTrace tailWord_1400419 prefixEnd_1400419 319594695417271816854265 := by
  unfold tailWord_1400419
  simp only [CollatzResearch.WordTrace]
  refine ⟨51077477113528610368812311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34051651409019073579208207 51077477113528610368812311)
  ·
    refine ⟨76616215670292915553218467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51077477113528610368812311 76616215670292915553218467)
    ·
      refine ⟨114924323505439373329827701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76616215670292915553218467 114924323505439373329827701)
      ·
        refine ⟨10774155328634941249671347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 114924323505439373329827701 10774155328634941249671347)
        ·
          refine ⟨16161232992952411874507021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10774155328634941249671347 16161232992952411874507021)
          ·
            refine ⟨6060462372357154452940133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16161232992952411874507021 6060462372357154452940133)
            ·
              refine ⟨1136336694816966459926275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6060462372357154452940133 1136336694816966459926275)
              ·
                refine ⟨1704505042225449689889413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1136336694816966459926275 1704505042225449689889413)
                ·
                  refine ⟨319594695417271816854265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1704505042225449689889413 319594695417271816854265)
                  ·
                    rfl

theorem cell21_1400419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 4].length) (baseStart_1400419 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1400419 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1400419 prefixEnd_1400419 := by exact prefixLift 1400419
  have htrace : WordTrace (prefixWord ++ tailWord_1400419) baseStart_1400419 baseEnd_1400419 := by
    simpa [prefixWord, tailWord_1400419, baseEnd_1400419] using wordTrace_append hprefix tailTrace_1400419
  have hstable : (prefixWord ++ tailWord_1400419).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400419).length < 2 ^ (prefixWord ++ tailWord_1400419).sum := by decide
  have hdescent : baseEnd_1400419 < baseStart_1400419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400456 : List Nat := [2, 1, 3, 5, 2, 1, 2, 2, 3]
def baseStart_1400456 : Nat := 118140960795 + 1400456 * 2 ^ 59
def prefixEnd_1400456 : Nat := 4983230072969 + 3 ^ 40 * 1400456 * 2
def baseEnd_1400456 : Nat := 319603139321367974737523

theorem tailTrace_1400456 : CollatzResearch.WordTrace tailWord_1400456 prefixEnd_1400456 319603139321367974737523 := by
  unfold tailWord_1400456
  simp only [CollatzResearch.WordTrace]
  refine ⟨25539413307197282843954611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34052551076263043791939481 25539413307197282843954611)
  ·
    refine ⟨38309119960795924265931917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25539413307197282843954611 38309119960795924265931917)
    ·
      refine ⟨14365919985298471599724469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38309119960795924265931917 14365919985298471599724469)
      ·
        refine ⟨1346804998621731712474169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14365919985298471599724469 1346804998621731712474169)
        ·
          refine ⟨1010103748966298784355627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1346804998621731712474169 1010103748966298784355627)
          ·
            refine ⟨1515155623449448176533441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1010103748966298784355627 1515155623449448176533441)
            ·
              refine ⟨1136366717587086132400081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1515155623449448176533441 1136366717587086132400081)
              ·
                refine ⟨852275038190314599300061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1136366717587086132400081 852275038190314599300061)
                ·
                  refine ⟨319603139321367974737523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 852275038190314599300061 319603139321367974737523)
                  ·
                    rfl

theorem cell21_1400456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2, 3].length) (baseStart_1400456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1400456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1400456 prefixEnd_1400456 := by exact prefixLift 1400456
  have htrace : WordTrace (prefixWord ++ tailWord_1400456) baseStart_1400456 baseEnd_1400456 := by
    simpa [prefixWord, tailWord_1400456, baseEnd_1400456] using wordTrace_append hprefix tailTrace_1400456
  have hstable : (prefixWord ++ tailWord_1400456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400456).length < 2 ^ (prefixWord ++ tailWord_1400456).sum := by decide
  have hdescent : baseEnd_1400456 < baseStart_1400456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400557 : List Nat := [1, 5, 1, 2, 1, 2, 3, 3, 3]
def baseStart_1400557 : Nat := 118140960795 + 1400557 * 2 ^ 59
def prefixEnd_1400557 : Nat := 4983230072969 + 3 ^ 40 * 1400557 * 2
def baseEnd_1400557 : Nat := 319626188897414243553983

theorem tailTrace_1400557 : CollatzResearch.WordTrace tailWord_1400557 prefixEnd_1400557 319626188897414243553983 := by
  unfold tailWord_1400557
  simp only [CollatzResearch.WordTrace]
  refine ⟨51082510387028659937335925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34055006924685773291557283 51082510387028659937335925)
  ·
    refine ⟨4788985348783936869125243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51082510387028659937335925 4788985348783936869125243)
    ·
      refine ⟨7183478023175905303687865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4788985348783936869125243 7183478023175905303687865)
      ·
        refine ⟨5387608517381928977765899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7183478023175905303687865 5387608517381928977765899)
        ·
          refine ⟨8081412776072893466648849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5387608517381928977765899 8081412776072893466648849)
          ·
            refine ⟨6061059582054670099986637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8081412776072893466648849 6061059582054670099986637)
            ·
              refine ⟨2272897343270501287494989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6061059582054670099986637 2272897343270501287494989)
              ·
                refine ⟨852336503726437982810621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2272897343270501287494989 852336503726437982810621)
                ·
                  refine ⟨319626188897414243553983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 852336503726437982810621 319626188897414243553983)
                  ·
                    rfl

theorem cell21_1400557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_1400557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1400557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1400557 prefixEnd_1400557 := by exact prefixLift 1400557
  have htrace : WordTrace (prefixWord ++ tailWord_1400557) baseStart_1400557 baseEnd_1400557 := by
    simpa [prefixWord, tailWord_1400557, baseEnd_1400557] using wordTrace_append hprefix tailTrace_1400557
  have hstable : (prefixWord ++ tailWord_1400557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400557).length < 2 ^ (prefixWord ++ tailWord_1400557).sum := by decide
  have hdescent : baseEnd_1400557 < baseStart_1400557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400574 : List Nat := [4, 2, 2, 1, 4, 1, 1, 1, 5]
def baseStart_1400574 : Nat := 118140960795 + 1400574 * 2 ^ 59
def prefixEnd_1400574 : Nat := 4983230072969 + 3 ^ 40 * 1400574 * 2
def baseEnd_1400574 : Nat := 319630068529025991770615

theorem tailTrace_1400574 : CollatzResearch.WordTrace tailWord_1400574 prefixEnd_1400574 319630068529025991770615 := by
  unfold tailWord_1400574
  simp only [CollatzResearch.WordTrace]
  refine ⟨6385391303495883980088097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34055420285311381227136517 6385391303495883980088097)
  ·
    refine ⟨4789043477621912985066073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6385391303495883980088097 4789043477621912985066073)
    ·
      refine ⟨3591782608216434738799555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4789043477621912985066073 3591782608216434738799555)
      ·
        refine ⟨5387673912324652108199333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3591782608216434738799555 5387673912324652108199333)
        ·
          refine ⟨1010188858560872270287375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5387673912324652108199333 1010188858560872270287375)
          ·
            refine ⟨1515283287841308405431063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1010188858560872270287375 1515283287841308405431063)
            ·
              refine ⟨2272924931761962608146595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1515283287841308405431063 2272924931761962608146595)
              ·
                refine ⟨3409387397642943912219893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2272924931761962608146595 3409387397642943912219893)
                ·
                  refine ⟨319630068529025991770615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3409387397642943912219893 319630068529025991770615)
                  ·
                    rfl

theorem cell21_1400574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_1400574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1400574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1400574 prefixEnd_1400574 := by exact prefixLift 1400574
  have htrace : WordTrace (prefixWord ++ tailWord_1400574) baseStart_1400574 baseEnd_1400574 := by
    simpa [prefixWord, tailWord_1400574, baseEnd_1400574] using wordTrace_append hprefix tailTrace_1400574
  have hstable : (prefixWord ++ tailWord_1400574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400574).length < 2 ^ (prefixWord ++ tailWord_1400574).sum := by decide
  have hdescent : baseEnd_1400574 < baseStart_1400574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400627 : List Nat := [1, 1, 1, 2, 16]
def baseStart_1400627 : Nat := 118140960795 + 1400627 * 2 ^ 59
def prefixEnd_1400627 : Nat := 4983230072969 + 3 ^ 40 * 1400627 * 2
def baseEnd_1400627 : Nat := 3946199553717403424533

theorem tailTrace_1400627 : CollatzResearch.WordTrace tailWord_1400627 prefixEnd_1400627 3946199553717403424533 := by
  unfold tailWord_1400627
  simp only [CollatzResearch.WordTrace]
  refine ⟨51085063496775061892384135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34056708997850041261589423 51085063496775061892384135)
  ·
    refine ⟨76627595245162592838576203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51085063496775061892384135 76627595245162592838576203)
    ·
      refine ⟨114941392867743889257864305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76627595245162592838576203 114941392867743889257864305)
      ·
        refine ⟨86206044650807916943398229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114941392867743889257864305 86206044650807916943398229)
        ·
          refine ⟨3946199553717403424533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 86206044650807916943398229 3946199553717403424533)
          ·
            rfl

theorem cell21_1400627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 16].length) (baseStart_1400627 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1400627 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1400627 prefixEnd_1400627 := by exact prefixLift 1400627
  have htrace : WordTrace (prefixWord ++ tailWord_1400627) baseStart_1400627 baseEnd_1400627 := by
    simpa [prefixWord, tailWord_1400627, baseEnd_1400627] using wordTrace_append hprefix tailTrace_1400627
  have hstable : (prefixWord ++ tailWord_1400627).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400627).length < 2 ^ (prefixWord ++ tailWord_1400627).sum := by decide
  have hdescent : baseEnd_1400627 < baseStart_1400627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400661 : List Nat := [1, 3, 2, 2, 2, 3, 3, 5]
def baseStart_1400661 : Nat := 118140960795 + 1400661 * 2 ^ 59
def prefixEnd_1400661 : Nat := 4983230072969 + 3 ^ 40 * 1400661 * 2
def baseEnd_1400661 : Nat := 106549974371444391273479

theorem tailTrace_1400661 : CollatzResearch.WordTrace tailWord_1400661 prefixEnd_1400661 106549974371444391273479 := by
  unfold tailWord_1400661
  simp only [CollatzResearch.WordTrace]
  refine ⟨51086303578651885699121837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34057535719101257132747891 51086303578651885699121837)
  ·
    refine ⟨19157363841994457137170689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51086303578651885699121837 19157363841994457137170689)
    ·
      refine ⟨14368022881495842852878017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19157363841994457137170689 14368022881495842852878017)
      ·
        refine ⟨10776017161121882139658513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14368022881495842852878017 10776017161121882139658513)
        ·
          refine ⟨8082012870841411604743885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10776017161121882139658513 8082012870841411604743885)
          ·
            refine ⟨3030754826565529351778957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8082012870841411604743885 3030754826565529351778957)
            ·
              refine ⟨1136533059962073506917109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3030754826565529351778957 1136533059962073506917109)
              ·
                refine ⟨106549974371444391273479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1136533059962073506917109 106549974371444391273479)
                ·
                  rfl

theorem cell21_1400661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 5].length) (baseStart_1400661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1400661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1400661 prefixEnd_1400661 := by exact prefixLift 1400661
  have htrace : WordTrace (prefixWord ++ tailWord_1400661) baseStart_1400661 baseEnd_1400661 := by
    simpa [prefixWord, tailWord_1400661, baseEnd_1400661] using wordTrace_append hprefix tailTrace_1400661
  have hstable : (prefixWord ++ tailWord_1400661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400661).length < 2 ^ (prefixWord ++ tailWord_1400661).sum := by decide
  have hdescent : baseEnd_1400661 < baseStart_1400661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400689 : List Nat := [1, 2, 2, 2, 1, 3, 3, 1, 6]
def baseStart_1400689 : Nat := 118140960795 + 1400689 * 2 ^ 59
def prefixEnd_1400689 : Nat := 4983230072969 + 3 ^ 40 * 1400689 * 2
def baseEnd_1400689 : Nat := 319656313095811347353713

theorem tailTrace_1400689 : CollatzResearch.WordTrace tailWord_1400689 prefixEnd_1400689 319656313095811347353713 := by
  unfold tailWord_1400689
  simp only [CollatzResearch.WordTrace]
  refine ⟨51087324822550446481141121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34058216548366964320760747 51087324822550446481141121)
  ·
    refine ⟨38315493616912834860855841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51087324822550446481141121 38315493616912834860855841)
    ·
      refine ⟨28736620212684626145641881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38315493616912834860855841 28736620212684626145641881)
      ·
        refine ⟨21552465159513469609231411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28736620212684626145641881 21552465159513469609231411)
        ·
          refine ⟨32328697739270204413847117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21552465159513469609231411 32328697739270204413847117)
          ·
            refine ⟨12123261652226326655192669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32328697739270204413847117 12123261652226326655192669)
            ·
              refine ⟨4546223119584872495697251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12123261652226326655192669 4546223119584872495697251)
              ·
                refine ⟨6819334679377308743545877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4546223119584872495697251 6819334679377308743545877)
                ·
                  refine ⟨319656313095811347353713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6819334679377308743545877 319656313095811347353713)
                  ·
                    rfl

theorem cell21_1400689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 6].length) (baseStart_1400689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1400689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1400689 prefixEnd_1400689 := by exact prefixLift 1400689
  have htrace : WordTrace (prefixWord ++ tailWord_1400689) baseStart_1400689 baseEnd_1400689 := by
    simpa [prefixWord, tailWord_1400689, baseEnd_1400689] using wordTrace_append hprefix tailTrace_1400689
  have hstable : (prefixWord ++ tailWord_1400689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400689).length < 2 ^ (prefixWord ++ tailWord_1400689).sum := by decide
  have hdescent : baseEnd_1400689 < baseStart_1400689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400703 : List Nat := [1, 1, 2, 2, 1, 1, 3, 10]
def baseStart_1400703 : Nat := 118140960795 + 1400703 * 2 ^ 59
def prefixEnd_1400703 : Nat := 4983230072969 + 3 ^ 40 * 1400703 * 2
def baseEnd_1400703 : Nat := 106553169362183478040117

theorem tailTrace_1400703 : CollatzResearch.WordTrace tailWord_1400703 prefixEnd_1400703 106553169362183478040117 := by
  unfold tailWord_1400703
  simp only [CollatzResearch.WordTrace]
  refine ⟨51087835444499726872150763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34058556962999817914767175 51087835444499726872150763)
  ·
    refine ⟨76631753166749590308226145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51087835444499726872150763 76631753166749590308226145)
    ·
      refine ⟨57473814875062192731169609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76631753166749590308226145 57473814875062192731169609)
      ·
        refine ⟨43105361156296644548377207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57473814875062192731169609 43105361156296644548377207)
        ·
          refine ⟨64658041734444966822565811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43105361156296644548377207 64658041734444966822565811)
          ·
            refine ⟨96987062601667450233848717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64658041734444966822565811 96987062601667450233848717)
            ·
              refine ⟨36370148475625293837693269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96987062601667450233848717 36370148475625293837693269)
              ·
                refine ⟨106553169362183478040117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36370148475625293837693269 106553169362183478040117)
                ·
                  rfl

theorem cell21_1400703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 10].length) (baseStart_1400703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1400703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1400703 prefixEnd_1400703 := by exact prefixLift 1400703
  have htrace : WordTrace (prefixWord ++ tailWord_1400703) baseStart_1400703 baseEnd_1400703 := by
    simpa [prefixWord, tailWord_1400703, baseEnd_1400703] using wordTrace_append hprefix tailTrace_1400703
  have hstable : (prefixWord ++ tailWord_1400703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400703).length < 2 ^ (prefixWord ++ tailWord_1400703).sum := by decide
  have hdescent : baseEnd_1400703 < baseStart_1400703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400737 : List Nat := [1, 2, 3, 4, 2, 2, 7]
def baseStart_1400737 : Nat := 118140960795 + 1400737 * 2 ^ 59
def prefixEnd_1400737 : Nat := 4983230072969 + 3 ^ 40 * 1400737 * 2
def baseEnd_1400737 : Nat := 35518585261085992283735

theorem tailTrace_1400737 : CollatzResearch.WordTrace tailWord_1400737 prefixEnd_1400737 35518585261085992283735 := by
  unfold tailWord_1400737
  simp only [CollatzResearch.WordTrace]
  refine ⟨51089075526376550678888465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34059383684251033785925643 51089075526376550678888465)
  ·
    refine ⟨38316806644782413009166349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51089075526376550678888465 38316806644782413009166349)
    ·
      refine ⟨14368802491793404878437381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38316806644782413009166349 14368802491793404878437381)
      ·
        refine ⟨2694150467211263414707009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14368802491793404878437381 2694150467211263414707009)
        ·
          refine ⟨2020612850408447561030257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2694150467211263414707009 2020612850408447561030257)
          ·
            refine ⟨1515459637806335670772693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2020612850408447561030257 1515459637806335670772693)
            ·
              refine ⟨35518585261085992283735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1515459637806335670772693 35518585261085992283735)
              ·
                rfl

theorem cell21_1400737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 7].length) (baseStart_1400737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1400737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1400737 prefixEnd_1400737 := by exact prefixLift 1400737
  have htrace : WordTrace (prefixWord ++ tailWord_1400737) baseStart_1400737 baseEnd_1400737 := by
    simpa [prefixWord, tailWord_1400737, baseEnd_1400737] using wordTrace_append hprefix tailTrace_1400737
  have hstable : (prefixWord ++ tailWord_1400737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400737).length < 2 ^ (prefixWord ++ tailWord_1400737).sum := by decide
  have hdescent : baseEnd_1400737 < baseStart_1400737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400779 : List Nat := [1, 1, 1, 1, 3, 4, 1, 9]
def baseStart_1400779 : Nat := 118140960795 + 1400779 * 2 ^ 59
def prefixEnd_1400779 : Nat := 4983230072969 + 3 ^ 40 * 1400779 * 2
def baseEnd_1400779 : Nat := 106558950773997063617843

theorem tailTrace_1400779 : CollatzResearch.WordTrace tailWord_1400779 prefixEnd_1400779 106558950773997063617843 := by
  unfold tailWord_1400779
  simp only [CollatzResearch.WordTrace]
  refine ⟨51090607392224391851917391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34060404928149594567944927 51090607392224391851917391)
  ·
    refine ⟨76635911088336587777876087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51090607392224391851917391 76635911088336587777876087)
    ·
      refine ⟨114953866632504881666814131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76635911088336587777876087 114953866632504881666814131)
      ·
        refine ⟨172430799948757322500221197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114953866632504881666814131 172430799948757322500221197)
        ·
          refine ⟨64661549980783995937582949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172430799948757322500221197 64661549980783995937582949)
          ·
            refine ⟨12124040621396999238296803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64661549980783995937582949 12124040621396999238296803)
            ·
              refine ⟨18186060932095498857445205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12124040621396999238296803 18186060932095498857445205)
              ·
                refine ⟨106558950773997063617843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18186060932095498857445205 106558950773997063617843)
                ·
                  rfl

theorem cell21_1400779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 9].length) (baseStart_1400779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1400779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1400779 prefixEnd_1400779 := by exact prefixLift 1400779
  have htrace : WordTrace (prefixWord ++ tailWord_1400779) baseStart_1400779 baseEnd_1400779 := by
    simpa [prefixWord, tailWord_1400779, baseEnd_1400779] using wordTrace_append hprefix tailTrace_1400779
  have hstable : (prefixWord ++ tailWord_1400779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400779).length < 2 ^ (prefixWord ++ tailWord_1400779).sum := by decide
  have hdescent : baseEnd_1400779 < baseStart_1400779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400802 : List Nat := [3, 3, 3, 1, 2, 1, 1, 4, 3]
def baseStart_1400802 : Nat := 118140960795 + 1400802 * 2 ^ 59
def prefixEnd_1400802 : Nat := 4983230072969 + 3 ^ 40 * 1400802 * 2
def baseEnd_1400802 : Nat := 319682101235348261970149

theorem tailTrace_1400802 : CollatzResearch.WordTrace tailWord_1400802 prefixEnd_1400802 319682101235348261970149 := by
  unfold tailWord_1400802
  simp only [CollatzResearch.WordTrace]
  refine ⟨12772861567785266695001165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34060964180760711186669773 12772861567785266695001165)
  ·
    refine ⟨4789823087919475010625437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12772861567785266695001165 4789823087919475010625437)
    ·
      refine ⟨1796183657969803128984539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4789823087919475010625437 1796183657969803128984539)
      ·
        refine ⟨2694275486954704693476809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1796183657969803128984539 2694275486954704693476809)
        ·
          refine ⟨2020706615216028520107607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2694275486954704693476809 2020706615216028520107607)
          ·
            refine ⟨3031059922824042780161411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2020706615216028520107607 3031059922824042780161411)
            ·
              refine ⟨4546589884236064170242117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3031059922824042780161411 4546589884236064170242117)
              ·
                refine ⟨852485603294262031920397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4546589884236064170242117 852485603294262031920397)
                ·
                  refine ⟨319682101235348261970149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 852485603294262031920397 319682101235348261970149)
                  ·
                    rfl

theorem cell21_1400802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_1400802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1400802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1400802 prefixEnd_1400802 := by exact prefixLift 1400802
  have htrace : WordTrace (prefixWord ++ tailWord_1400802) baseStart_1400802 baseEnd_1400802 := by
    simpa [prefixWord, tailWord_1400802, baseEnd_1400802] using wordTrace_append hprefix tailTrace_1400802
  have hstable : (prefixWord ++ tailWord_1400802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400802).length < 2 ^ (prefixWord ++ tailWord_1400802).sum := by decide
  have hdescent : baseEnd_1400802 < baseStart_1400802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400830 : List Nat := [4, 2, 2, 2, 1, 2, 3, 5]
def baseStart_1400830 : Nat := 118140960795 + 1400830 * 2 ^ 59
def prefixEnd_1400830 : Nat := 4983230072969 + 3 ^ 40 * 1400830 * 2
def baseEnd_1400830 : Nat := 106562830405608811834475

theorem tailTrace_1400830 : CollatzResearch.WordTrace tailWord_1400830 prefixEnd_1400830 106562830405608811834475 := by
  unfold tailWord_1400830
  simp only [CollatzResearch.WordTrace]
  refine ⟨6386558439379953445252993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34061645010026418374682629 6386558439379953445252993)
  ·
    refine ⟨4789918829534965083939745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6386558439379953445252993 4789918829534965083939745)
    ·
      refine ⟨3592439122151223812954809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4789918829534965083939745 3592439122151223812954809)
      ·
        refine ⟨2694329341613417859716107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3592439122151223812954809 2694329341613417859716107)
        ·
          refine ⟨4041494012420126789574161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2694329341613417859716107 4041494012420126789574161)
          ·
            refine ⟨3031120509315095092180621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4041494012420126789574161 3031120509315095092180621)
            ·
              refine ⟨1136670190993160659567733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3031120509315095092180621 1136670190993160659567733)
              ·
                refine ⟨106562830405608811834475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1136670190993160659567733 106562830405608811834475)
                ·
                  rfl

theorem cell21_1400830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_1400830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1400830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1400830 prefixEnd_1400830 := by exact prefixLift 1400830
  have htrace : WordTrace (prefixWord ++ tailWord_1400830) baseStart_1400830 baseEnd_1400830 := by
    simpa [prefixWord, tailWord_1400830, baseEnd_1400830] using wordTrace_append hprefix tailTrace_1400830
  have hstable : (prefixWord ++ tailWord_1400830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400830).length < 2 ^ (prefixWord ++ tailWord_1400830).sum := by decide
  have hdescent : baseEnd_1400830 < baseStart_1400830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400844 : List Nat := [2, 2, 1, 2, 3, 1, 4, 3, 3]
def baseStart_1400844 : Nat := 118140960795 + 1400844 * 2 ^ 59
def prefixEnd_1400844 : Nat := 4983230072969 + 3 ^ 40 * 1400844 * 2
def baseEnd_1400844 : Nat := 319691686207565522270063

theorem tailTrace_1400844 : CollatzResearch.WordTrace tailWord_1400844 prefixEnd_1400844 319691686207565522270063 := by
  unfold tailWord_1400844
  simp only [CollatzResearch.WordTrace]
  refine ⟨25546489068494453976516793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34061985424659271968689057 25546489068494453976516793)
  ·
    refine ⟨19159866801370840482387595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25546489068494453976516793 19159866801370840482387595)
    ·
      refine ⟨28739800202056260723581393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19159866801370840482387595 28739800202056260723581393)
      ·
        refine ⟨21554850151542195542686045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28739800202056260723581393 21554850151542195542686045)
        ·
          refine ⟨8083068806828323328507267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21554850151542195542686045 8083068806828323328507267)
          ·
            refine ⟨12124603210242484992760901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8083068806828323328507267 12124603210242484992760901)
            ·
              refine ⟨2273363101920465936142669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12124603210242484992760901 2273363101920465936142669)
              ·
                refine ⟨852511163220174726053501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2273363101920465936142669 852511163220174726053501)
                ·
                  refine ⟨319691686207565522270063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 852511163220174726053501 319691686207565522270063)
                  ·
                    rfl

theorem cell21_1400844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3, 3].length) (baseStart_1400844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1400844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1400844 prefixEnd_1400844 := by exact prefixLift 1400844
  have htrace : WordTrace (prefixWord ++ tailWord_1400844) baseStart_1400844 baseEnd_1400844 := by
    simpa [prefixWord, tailWord_1400844, baseEnd_1400844] using wordTrace_append hprefix tailTrace_1400844
  have hstable : (prefixWord ++ tailWord_1400844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400844).length < 2 ^ (prefixWord ++ tailWord_1400844).sum := by decide
  have hdescent : baseEnd_1400844 < baseStart_1400844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400858 : List Nat := [3, 1, 1, 3, 1, 3, 3, 2, 4]
def baseStart_1400858 : Nat := 118140960795 + 1400858 * 2 ^ 59
def prefixEnd_1400858 : Nat := 4983230072969 + 3 ^ 40 * 1400858 * 2
def baseEnd_1400858 : Nat := 319694881198304609036701

theorem tailTrace_1400858 : CollatzResearch.WordTrace tailWord_1400858 prefixEnd_1400858 319694881198304609036701 := by
  unfold tailWord_1400858
  simp only [CollatzResearch.WordTrace]
  refine ⟨12773372189734547086010807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34062325839292125562695485 12773372189734547086010807)
  ·
    refine ⟨19160058284601820629016211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12773372189734547086010807 19160058284601820629016211)
    ·
      refine ⟨28740087426902730943524317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19160058284601820629016211 28740087426902730943524317)
      ·
        refine ⟨10777532785088524103821619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28740087426902730943524317 10777532785088524103821619)
        ·
          refine ⟨16166299177632786155732429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10777532785088524103821619 16166299177632786155732429)
          ·
            refine ⟨6062362191612294808399661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16166299177632786155732429 6062362191612294808399661)
            ·
              refine ⟨2273385821854610553149873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6062362191612294808399661 2273385821854610553149873)
              ·
                refine ⟨1705039366390957914862405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2273385821854610553149873 1705039366390957914862405)
                ·
                  refine ⟨319694881198304609036701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1705039366390957914862405 319694881198304609036701)
                  ·
                    rfl

theorem cell21_1400858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_1400858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1400858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1400858 prefixEnd_1400858 := by exact prefixLift 1400858
  have htrace : WordTrace (prefixWord ++ tailWord_1400858) baseStart_1400858 baseEnd_1400858 := by
    simpa [prefixWord, tailWord_1400858, baseEnd_1400858] using wordTrace_append hprefix tailTrace_1400858
  have hstable : (prefixWord ++ tailWord_1400858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400858).length < 2 ^ (prefixWord ++ tailWord_1400858).sum := by decide
  have hdescent : baseEnd_1400858 < baseStart_1400858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400917 : List Nat := [1, 3, 2, 2, 1, 3, 2, 1, 6]
def baseStart_1400917 : Nat := 118140960795 + 1400917 * 2 ^ 59
def prefixEnd_1400917 : Nat := 4983230072969 + 3 ^ 40 * 1400917 * 2
def baseEnd_1400917 : Nat := 319708345802133617553247

theorem tailTrace_1400917 : CollatzResearch.WordTrace tailWord_1400917 prefixEnd_1400917 319708345802133617553247 := by
  unfold tailWord_1400917
  simp only [CollatzResearch.WordTrace]
  refine ⟨51095640665724441420441005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34063760443816294280294003 51095640665724441420441005)
  ·
    refine ⟨19160865249646665532665377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51095640665724441420441005 19160865249646665532665377)
    ·
      refine ⟨14370648937234999149499033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19160865249646665532665377 14370648937234999149499033)
      ·
        refine ⟨10777986702926249362124275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14370648937234999149499033 10777986702926249362124275)
        ·
          refine ⟨16166980054389374043186413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10777986702926249362124275 16166980054389374043186413)
          ·
            refine ⟨6062617520396015266194905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16166980054389374043186413 6062617520396015266194905)
            ·
              refine ⟨4546963140297011449646179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6062617520396015266194905 4546963140297011449646179)
              ·
                refine ⟨6820444710445517174469269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4546963140297011449646179 6820444710445517174469269)
                ·
                  refine ⟨319708345802133617553247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6820444710445517174469269 319708345802133617553247)
                  ·
                    rfl

theorem cell21_1400917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_1400917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1400917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1400917 prefixEnd_1400917 := by exact prefixLift 1400917
  have htrace : WordTrace (prefixWord ++ tailWord_1400917) baseStart_1400917 baseEnd_1400917 := by
    simpa [prefixWord, tailWord_1400917, baseEnd_1400917] using wordTrace_append hprefix tailTrace_1400917
  have hstable : (prefixWord ++ tailWord_1400917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400917).length < 2 ^ (prefixWord ++ tailWord_1400917).sum := by decide
  have hdescent : baseEnd_1400917 < baseStart_1400917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400926 : List Nat := [4, 4, 1, 1, 2, 2, 2, 1, 4]
def baseStart_1400926 : Nat := 118140960795 + 1400926 * 2 ^ 59
def prefixEnd_1400926 : Nat := 4983230072969 + 3 ^ 40 * 1400926 * 2
def baseEnd_1400926 : Nat := 319710399724751601903229

theorem tailTrace_1400926 : CollatzResearch.WordTrace tailWord_1400926 prefixEnd_1400926 319710399724751601903229 := by
  unfold tailWord_1400926
  simp only [CollatzResearch.WordTrace]
  refine ⟨6386996115336479494689829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34063979281794557305012421 6386996115336479494689829)
  ·
    refine ⟨1197561771625589905254343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6386996115336479494689829 1197561771625589905254343)
    ·
      refine ⟨1796342657438384857881515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1197561771625589905254343 1796342657438384857881515)
      ·
        refine ⟨2694513986157577286822273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1796342657438384857881515 2694513986157577286822273)
        ·
          refine ⟨2020885489618182965116705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2694513986157577286822273 2020885489618182965116705)
          ·
            refine ⟨1515664117213637223837529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2020885489618182965116705 1515664117213637223837529)
            ·
              refine ⟨1136748087910227917878147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1515664117213637223837529 1136748087910227917878147)
              ·
                refine ⟨1705122131865341876817221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1136748087910227917878147 1705122131865341876817221)
                ·
                  refine ⟨319710399724751601903229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1705122131865341876817221 319710399724751601903229)
                  ·
                    rfl

theorem cell21_1400926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_1400926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1400926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1400926 prefixEnd_1400926 := by exact prefixLift 1400926
  have htrace : WordTrace (prefixWord ++ tailWord_1400926) baseStart_1400926 baseEnd_1400926 := by
    simpa [prefixWord, tailWord_1400926, baseEnd_1400926] using wordTrace_append hprefix tailTrace_1400926
  have hstable : (prefixWord ++ tailWord_1400926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400926).length < 2 ^ (prefixWord ++ tailWord_1400926).sum := by decide
  have hdescent : baseEnd_1400926 < baseStart_1400926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400931 : List Nat := [1, 1, 1, 5, 1, 1, 3, 8]
def baseStart_1400931 : Nat := 118140960795 + 1400931 * 2 ^ 59
def prefixEnd_1400931 : Nat := 4983230072969 + 3 ^ 40 * 1400931 * 2
def baseEnd_1400931 : Nat := 106570513597624234773295

theorem tailTrace_1400931 : CollatzResearch.WordTrace tailWord_1400931 prefixEnd_1400931 106570513597624234773295 := by
  unfold tailWord_1400931
  simp only [CollatzResearch.WordTrace]
  refine ⟨51096151287673721811450647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34064100858449147874300431 51096151287673721811450647)
  ·
    refine ⟨76644226931510582717175971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51096151287673721811450647 76644226931510582717175971)
    ·
      refine ⟨114966340397265874075763957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76644226931510582717175971 114966340397265874075763957)
      ·
        refine ⟨10778094412243675694602871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 114966340397265874075763957 10778094412243675694602871)
        ·
          refine ⟨16167141618365513541904307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10778094412243675694602871 16167141618365513541904307)
          ·
            refine ⟨24250712427548270312856461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16167141618365513541904307 24250712427548270312856461)
            ·
              refine ⟨9094017160330601367321173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24250712427548270312856461 9094017160330601367321173)
              ·
                refine ⟨106570513597624234773295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9094017160330601367321173 106570513597624234773295)
                ·
                  rfl

theorem cell21_1400931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 8].length) (baseStart_1400931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1400931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1400931 prefixEnd_1400931 := by exact prefixLift 1400931
  have htrace : WordTrace (prefixWord ++ tailWord_1400931) baseStart_1400931 baseEnd_1400931 := by
    simpa [prefixWord, tailWord_1400931, baseEnd_1400931] using wordTrace_append hprefix tailTrace_1400931
  have hstable : (prefixWord ++ tailWord_1400931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400931).length < 2 ^ (prefixWord ++ tailWord_1400931).sum := by decide
  have hdescent : baseEnd_1400931 < baseStart_1400931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401086 : List Nat := [4, 2, 2, 1, 1, 1, 2, 4, 4]
def baseStart_1401086 : Nat := 118140960795 + 1401086 * 2 ^ 59
def prefixEnd_1401086 : Nat := 4983230072969 + 3 ^ 40 * 1401086 * 2
def baseEnd_1401086 : Nat := 319746913904626879236235

theorem tailTrace_1401086 : CollatzResearch.WordTrace tailWord_1401086 prefixEnd_1401086 319746913904626879236235 := by
  unfold tailWord_1401086
  simp only [CollatzResearch.WordTrace]
  refine ⟨6387725575264022910417889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34067869734741455522228741 6387725575264022910417889)
  ·
    refine ⟨4790794181448017182813417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6387725575264022910417889 4790794181448017182813417)
    ·
      refine ⟨3593095636086012887110063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4790794181448017182813417 3593095636086012887110063)
      ·
        refine ⟨5389643454129019330665095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3593095636086012887110063 5389643454129019330665095)
        ·
          refine ⟨8084465181193528995997643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5389643454129019330665095 8084465181193528995997643)
          ·
            refine ⟨12126697771790293493996465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8084465181193528995997643 12126697771790293493996465)
            ·
              refine ⟨9095023328842720120497349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12126697771790293493996465 9095023328842720120497349)
              ·
                refine ⟨1705316874158010022593253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9095023328842720120497349 1705316874158010022593253)
                ·
                  refine ⟨319746913904626879236235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1705316874158010022593253 319746913904626879236235)
                  ·
                    rfl

theorem cell21_1401086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_1401086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1401086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1401086 prefixEnd_1401086 := by exact prefixLift 1401086
  have htrace : WordTrace (prefixWord ++ tailWord_1401086) baseStart_1401086 baseEnd_1401086 := by
    simpa [prefixWord, tailWord_1401086, baseEnd_1401086] using wordTrace_append hprefix tailTrace_1401086
  have hstable : (prefixWord ++ tailWord_1401086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401086).length < 2 ^ (prefixWord ++ tailWord_1401086).sum := by decide
  have hdescent : baseEnd_1401086 < baseStart_1401086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401258 : List Nat := [3, 1, 6, 1, 1, 2, 1, 1, 5]
def baseStart_1401258 : Nat := 118140960795 + 1401258 * 2 ^ 59
def prefixEnd_1401258 : Nat := 4983230072969 + 3 ^ 40 * 1401258 * 2
def baseEnd_1401258 : Nat := 319786166647992802369217

theorem tailTrace_1401258 : CollatzResearch.WordTrace tailWord_1401258 prefixEnd_1401258 319786166647992802369217 := by
  unfold tailWord_1401258
  simp only [CollatzResearch.WordTrace]
  refine ⟨12777019489372264164651107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34072051971659371105736285 12777019489372264164651107)
  ·
    refine ⟨19165529234058396246976661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12777019489372264164651107 19165529234058396246976661)
    ·
      refine ⟨898384182846487324077031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19165529234058396246976661 898384182846487324077031)
      ·
        refine ⟨1347576274269730986115547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 898384182846487324077031 1347576274269730986115547)
        ·
          refine ⟨2021364411404596479173321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1347576274269730986115547 2021364411404596479173321)
          ·
            refine ⟨1516023308553447359379991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2021364411404596479173321 1516023308553447359379991)
            ·
              refine ⟨2274034962830171039069987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1516023308553447359379991 2274034962830171039069987)
              ·
                refine ⟨3411052444245256558604981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2274034962830171039069987 3411052444245256558604981)
                ·
                  refine ⟨319786166647992802369217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3411052444245256558604981 319786166647992802369217)
                  ·
                    rfl

theorem cell21_1401258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 5].length) (baseStart_1401258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1401258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1401258 prefixEnd_1401258 := by exact prefixLift 1401258
  have htrace : WordTrace (prefixWord ++ tailWord_1401258) baseStart_1401258 baseEnd_1401258 := by
    simpa [prefixWord, tailWord_1401258, baseEnd_1401258] using wordTrace_append hprefix tailTrace_1401258
  have hstable : (prefixWord ++ tailWord_1401258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401258).length < 2 ^ (prefixWord ++ tailWord_1401258).sum := by decide
  have hdescent : baseEnd_1401258 < baseStart_1401258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401373 : List Nat := [1, 4, 2, 2, 1, 3, 1, 1, 6]
def baseStart_1401373 : Nat := 118140960795 + 1401373 * 2 ^ 59
def prefixEnd_1401373 : Nat := 4983230072969 + 3 ^ 40 * 1401373 * 2
def baseEnd_1401373 : Nat := 319812411214778157952315

theorem tailTrace_1401373 : CollatzResearch.WordTrace tailWord_1401373 prefixEnd_1401373 319812411214778157952315 := by
  unfold tailWord_1401373
  simp only [CollatzResearch.WordTrace]
  refine ⟨51112272352072431299040773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34074848234714954199360515 51112272352072431299040773)
  ·
    refine ⟨9583551066013580868570145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51112272352072431299040773 9583551066013580868570145)
    ·
      refine ⟨7187663299510185651427609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9583551066013580868570145 7187663299510185651427609)
      ·
        refine ⟨5390747474632639238570707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7187663299510185651427609 5390747474632639238570707)
        ·
          refine ⟨8086121211948958857856061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5390747474632639238570707 8086121211948958857856061)
          ·
            refine ⟨3032295454480859571696023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8086121211948958857856061 3032295454480859571696023)
            ·
              refine ⟨4548443181721289357544035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3032295454480859571696023 4548443181721289357544035)
              ·
                refine ⟨6822664772581934036316053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4548443181721289357544035 6822664772581934036316053)
                ·
                  refine ⟨319812411214778157952315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6822664772581934036316053 319812411214778157952315)
                  ·
                    rfl

theorem cell21_1401373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_1401373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1401373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1401373 prefixEnd_1401373 := by exact prefixLift 1401373
  have htrace : WordTrace (prefixWord ++ tailWord_1401373) baseStart_1401373 baseEnd_1401373 := by
    simpa [prefixWord, tailWord_1401373, baseEnd_1401373] using wordTrace_append hprefix tailTrace_1401373
  have hstable : (prefixWord ++ tailWord_1401373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401373).length < 2 ^ (prefixWord ++ tailWord_1401373).sum := by decide
  have hdescent : baseEnd_1401373 < baseStart_1401373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401404 : List Nat := [2, 2, 2, 2, 3, 1, 4, 5]
def baseStart_1401404 : Nat := 118140960795 + 1401404 * 2 ^ 59
def prefixEnd_1401404 : Nat := 4983230072969 + 3 ^ 40 * 1401404 * 2
def baseEnd_1401404 : Nat := 106606495279042997645195

theorem tailTrace_1401404 : CollatzResearch.WordTrace tailWord_1401404 prefixEnd_1401404 106606495279042997645195 := by
  unfold tailWord_1401404
  simp only [CollatzResearch.WordTrace]
  refine ⟨25556701507480061796709633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34075602009973415728946177 25556701507480061796709633)
  ·
    refine ⟨19167526130610046347532225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25556701507480061796709633 19167526130610046347532225)
    ·
      refine ⟨14375644597957534760649169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19167526130610046347532225 14375644597957534760649169)
      ·
        refine ⟨10781733448468151070486877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14375644597957534760649169 10781733448468151070486877)
        ·
          refine ⟨4043150043175556651432579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10781733448468151070486877 4043150043175556651432579)
          ·
            refine ⟨6064725064763334977148869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4043150043175556651432579 6064725064763334977148869)
            ·
              refine ⟨1137135949643125308215413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6064725064763334977148869 1137135949643125308215413)
              ·
                refine ⟨106606495279042997645195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1137135949643125308215413 106606495279042997645195)
                ·
                  rfl

theorem cell21_1401404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 5].length) (baseStart_1401404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1401404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1401404 prefixEnd_1401404 := by exact prefixLift 1401404
  have htrace : WordTrace (prefixWord ++ tailWord_1401404) baseStart_1401404 baseEnd_1401404 := by
    simpa [prefixWord, tailWord_1401404, baseEnd_1401404] using wordTrace_append hprefix tailTrace_1401404
  have hstable : (prefixWord ++ tailWord_1401404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401404).length < 2 ^ (prefixWord ++ tailWord_1401404).sum := by decide
  have hdescent : baseEnd_1401404 < baseStart_1401404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401432 : List Nat := [2, 1, 2, 2, 1, 2, 4, 1, 6]
def baseStart_1401432 : Nat := 118140960795 + 1401432 * 2 ^ 59
def prefixEnd_1401432 : Nat := 4983230072969 + 3 ^ 40 * 1401432 * 2
def baseEnd_1401432 : Nat := 319825875818607166468861

theorem tailTrace_1401432 : CollatzResearch.WordTrace tailWord_1401432 prefixEnd_1401432 319825875818607166468861 := by
  unfold tailWord_1401432
  simp only [CollatzResearch.WordTrace]
  refine ⟨25557212129429342187719275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34076282839239122916959033 25557212129429342187719275)
  ·
    refine ⟨38335818194144013281578913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25557212129429342187719275 38335818194144013281578913)
    ·
      refine ⟨28751863645608009961184185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38335818194144013281578913 28751863645608009961184185)
      ·
        refine ⟨21563897734206007470888139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28751863645608009961184185 21563897734206007470888139)
        ·
          refine ⟨32345846601309011206332209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21563897734206007470888139 32345846601309011206332209)
          ·
            refine ⟨24259384950981758404749157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32345846601309011206332209 24259384950981758404749157)
            ·
              refine ⟨4548634678309079700890467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24259384950981758404749157 4548634678309079700890467)
              ·
                refine ⟨6822952017463619551335701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4548634678309079700890467 6822952017463619551335701)
                ·
                  refine ⟨319825875818607166468861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6822952017463619551335701 319825875818607166468861)
                  ·
                    rfl

theorem cell21_1401432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 6].length) (baseStart_1401432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1401432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1401432 prefixEnd_1401432 := by exact prefixLift 1401432
  have htrace : WordTrace (prefixWord ++ tailWord_1401432) baseStart_1401432 baseEnd_1401432 := by
    simpa [prefixWord, tailWord_1401432, baseEnd_1401432] using wordTrace_append hprefix tailTrace_1401432
  have hstable : (prefixWord ++ tailWord_1401432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401432).length < 2 ^ (prefixWord ++ tailWord_1401432).sum := by decide
  have hdescent : baseEnd_1401432 < baseStart_1401432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401514 : List Nat := [3, 1, 5, 2, 1, 1, 3, 5]
def baseStart_1401514 : Nat := 118140960795 + 1401514 * 2 ^ 59
def prefixEnd_1401514 : Nat := 4983230072969 + 3 ^ 40 * 1401514 * 2
def baseEnd_1401514 : Nat := 106614863111931082034009

theorem tailTrace_1401514 : CollatzResearch.WordTrace tailWord_1401514 prefixEnd_1401514 106614863111931082034009 := by
  unfold tailWord_1401514
  simp only [CollatzResearch.WordTrace]
  refine ⟨12779353761140403094980899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34078276696374408253282397 12779353761140403094980899)
  ·
    refine ⟨19169030641710604642471349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12779353761140403094980899 19169030641710604642471349)
    ·
      refine ⟨1797096622660369185231689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19169030641710604642471349 1797096622660369185231689)
      ·
        refine ⟨1347822466995276888923767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1797096622660369185231689 1347822466995276888923767)
        ·
          refine ⟨2021733700492915333385651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1347822466995276888923767 2021733700492915333385651)
          ·
            refine ⟨3032600550739373000078477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2021733700492915333385651 3032600550739373000078477)
            ·
              refine ⟨1137225206527264875029429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3032600550739373000078477 1137225206527264875029429)
              ·
                refine ⟨106614863111931082034009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1137225206527264875029429 106614863111931082034009)
                ·
                  rfl

theorem cell21_1401514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 5].length) (baseStart_1401514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1401514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1401514 prefixEnd_1401514 := by exact prefixLift 1401514
  have htrace : WordTrace (prefixWord ++ tailWord_1401514) baseStart_1401514 baseEnd_1401514 := by
    simpa [prefixWord, tailWord_1401514, baseEnd_1401514] using wordTrace_append hprefix tailTrace_1401514
  have hstable : (prefixWord ++ tailWord_1401514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401514).length < 2 ^ (prefixWord ++ tailWord_1401514).sum := by decide
  have hdescent : baseEnd_1401514 < baseStart_1401514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401604 : List Nat := [2, 3, 2, 2, 1, 1, 5, 2, 3]
def baseStart_1401604 : Nat := 118140960795 + 1401604 * 2 ^ 59
def prefixEnd_1401604 : Nat := 4983230072969 + 3 ^ 40 * 1401604 * 2
def baseEnd_1401604 : Nat := 319865128561973089601843

theorem tailTrace_1401604 : CollatzResearch.WordTrace tailWord_1401604 prefixEnd_1401604 319865128561973089601843 := by
  unfold tailWord_1401604
  simp only [CollatzResearch.WordTrace]
  refine ⟨25560348807117778875349933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34080465076157038500466577 25560348807117778875349933)
  ·
    refine ⟨9585130802669167078256225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25560348807117778875349933 9585130802669167078256225)
    ·
      refine ⟨7188848102001875308692169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9585130802669167078256225 7188848102001875308692169)
      ·
        refine ⟨5391636076501406481519127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7188848102001875308692169 5391636076501406481519127)
        ·
          refine ⟨8087454114752109722278691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5391636076501406481519127 8087454114752109722278691)
          ·
            refine ⟨12131181172128164583418037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8087454114752109722278691 12131181172128164583418037)
            ·
              refine ⟨1137298234887015429695441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12131181172128164583418037 1137298234887015429695441)
              ·
                refine ⟨852973676165261572271581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1137298234887015429695441 852973676165261572271581)
                ·
                  refine ⟨319865128561973089601843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 852973676165261572271581 319865128561973089601843)
                  ·
                    rfl

theorem cell21_1401604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_1401604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1401604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1401604 prefixEnd_1401604 := by exact prefixLift 1401604
  have htrace : WordTrace (prefixWord ++ tailWord_1401604) baseStart_1401604 baseEnd_1401604 := by
    simpa [prefixWord, tailWord_1401604, baseEnd_1401604] using wordTrace_append hprefix tailTrace_1401604
  have hstable : (prefixWord ++ tailWord_1401604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401604).length < 2 ^ (prefixWord ++ tailWord_1401604).sum := by decide
  have hdescent : baseEnd_1401604 < baseStart_1401604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401663 : List Nat := [1, 1, 2, 2, 5, 2, 1, 4, 3]
def baseStart_1401663 : Nat := 118140960795 + 1401663 * 2 ^ 59
def prefixEnd_1401663 : Nat := 4983230072969 + 3 ^ 40 * 1401663 * 2
def baseEnd_1401663 : Nat := 319878593165802098118389

theorem tailTrace_1401663 : CollatzResearch.WordTrace tailWord_1401663 prefixEnd_1401663 319878593165802098118389 := by
  unfold tailWord_1401663
  simp only [CollatzResearch.WordTrace]
  refine ⟨51122849521021810827097643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34081899680681207218065095 51122849521021810827097643)
  ·
    refine ⟨76684274281532716240646465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51122849521021810827097643 76684274281532716240646465)
    ·
      refine ⟨57513205711149537180484849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76684274281532716240646465 57513205711149537180484849)
      ·
        refine ⟨43134904283362152885363637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57513205711149537180484849 43134904283362152885363637)
        ·
          refine ⟨4043897276565201833002841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43134904283362152885363637 4043897276565201833002841)
          ·
            refine ⟨3032922957423901374752131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4043897276565201833002841 3032922957423901374752131)
            ·
              refine ⟨4549384436135852062128197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3032922957423901374752131 4549384436135852062128197)
              ·
                refine ⟨853009581775472261649037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4549384436135852062128197 853009581775472261649037)
                ·
                  refine ⟨319878593165802098118389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 853009581775472261649037 319878593165802098118389)
                  ·
                    rfl

theorem cell21_1401663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4, 3].length) (baseStart_1401663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1401663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1401663 prefixEnd_1401663 := by exact prefixLift 1401663
  have htrace : WordTrace (prefixWord ++ tailWord_1401663) baseStart_1401663 baseEnd_1401663 := by
    simpa [prefixWord, tailWord_1401663, baseEnd_1401663] using wordTrace_append hprefix tailTrace_1401663
  have hstable : (prefixWord ++ tailWord_1401663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401663).length < 2 ^ (prefixWord ++ tailWord_1401663).sum := by decide
  have hdescent : baseEnd_1401663 < baseStart_1401663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401674 : List Nat := [3, 1, 2, 1, 1, 1, 2, 10]
def baseStart_1401674 : Nat := 118140960795 + 1401674 * 2 ^ 59
def prefixEnd_1401674 : Nat := 4983230072969 + 3 ^ 40 * 1401674 * 2
def baseEnd_1401674 : Nat := 106627034505222841145011

theorem tailTrace_1401674 : CollatzResearch.WordTrace tailWord_1401674 prefixEnd_1401674 106627034505222841145011 := by
  unfold tailWord_1401674
  simp only [CollatzResearch.WordTrace]
  refine ⟨12780812680995489926437019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34082167149321306470498717 12780812680995489926437019)
  ·
    refine ⟨19171219021493234889655529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12780812680995489926437019 19171219021493234889655529)
    ·
      refine ⟨14378414266119926167241647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19171219021493234889655529 14378414266119926167241647)
      ·
        refine ⟨21567621399179889250862471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14378414266119926167241647 21567621399179889250862471)
        ·
          refine ⟨32351432098769833876293707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21567621399179889250862471 32351432098769833876293707)
          ·
            refine ⟨48527148148154750814440561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32351432098769833876293707 48527148148154750814440561)
            ·
              refine ⟨36395361111116063110830421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48527148148154750814440561 36395361111116063110830421)
              ·
                refine ⟨106627034505222841145011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36395361111116063110830421 106627034505222841145011)
                ·
                  rfl

theorem cell21_1401674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 10].length) (baseStart_1401674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1401674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1401674 prefixEnd_1401674 := by exact prefixLift 1401674
  have htrace : WordTrace (prefixWord ++ tailWord_1401674) baseStart_1401674 baseEnd_1401674 := by
    simpa [prefixWord, tailWord_1401674, baseEnd_1401674] using wordTrace_append hprefix tailTrace_1401674
  have hstable : (prefixWord ++ tailWord_1401674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401674).length < 2 ^ (prefixWord ++ tailWord_1401674).sum := by decide
  have hdescent : baseEnd_1401674 < baseStart_1401674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401773 : List Nat := [1, 5, 2, 3, 2, 1, 1, 1, 5]
def baseStart_1401773 : Nat := 118140960795 + 1401773 * 2 ^ 59
def prefixEnd_1401773 : Nat := 4983230072969 + 3 ^ 40 * 1401773 * 2
def baseEnd_1401773 : Nat := 319903696664466351284831

theorem tailTrace_1401773 : CollatzResearch.WordTrace tailWord_1401773 prefixEnd_1401773 319903696664466351284831 := by
  unfold tailWord_1401773
  simp only [CollatzResearch.WordTrace]
  refine ⟨51126861550623299613601973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34084574367082199742401315 51126861550623299613601973)
  ·
    refine ⟨4793143270370934338775185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51126861550623299613601973 4793143270370934338775185)
    ·
      refine ⟨3594857452778200754081389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4793143270370934338775185 3594857452778200754081389)
      ·
        refine ⟨1348071544791825282780521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3594857452778200754081389 1348071544791825282780521)
        ·
          refine ⟨1011053658593868962085391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1348071544791825282780521 1011053658593868962085391)
          ·
            refine ⟨1516580487890803443128087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1011053658593868962085391 1516580487890803443128087)
            ·
              refine ⟨2274870731836205164692131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1516580487890803443128087 2274870731836205164692131)
              ·
                refine ⟨3412306097754307747038197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2274870731836205164692131 3412306097754307747038197)
                ·
                  refine ⟨319903696664466351284831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3412306097754307747038197 319903696664466351284831)
                  ·
                    rfl

theorem cell21_1401773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_1401773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1401773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1401773 prefixEnd_1401773 := by exact prefixLift 1401773
  have htrace : WordTrace (prefixWord ++ tailWord_1401773) baseStart_1401773 baseEnd_1401773 := by
    simpa [prefixWord, tailWord_1401773, baseEnd_1401773] using wordTrace_append hprefix tailTrace_1401773
  have hstable : (prefixWord ++ tailWord_1401773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401773).length < 2 ^ (prefixWord ++ tailWord_1401773).sum := by decide
  have hdescent : baseEnd_1401773 < baseStart_1401773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401857 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 7]
def baseStart_1401857 : Nat := 118140960795 + 1401857 * 2 ^ 59
def prefixEnd_1401857 : Nat := 4983230072969 + 3 ^ 40 * 1401857 * 2
def baseEnd_1401857 : Nat := 319922866608900871884659

theorem tailTrace_1401857 : CollatzResearch.WordTrace tailWord_1401857 prefixEnd_1401857 319922866608900871884659 := by
  unfold tailWord_1401857
  simp only [CollatzResearch.WordTrace]
  refine ⟨51129925282318981959659825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34086616854879321306439883 51129925282318981959659825)
  ·
    refine ⟨38347443961739236469744869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51129925282318981959659825 38347443961739236469744869)
    ·
      refine ⟨7190145742826106838077163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38347443961739236469744869 7190145742826106838077163)
      ·
        refine ⟨10785218614239160257115745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7190145742826106838077163 10785218614239160257115745)
        ·
          refine ⟨8088913960679370192836809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10785218614239160257115745 8088913960679370192836809)
          ·
            refine ⟨6066685470509527644627607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8088913960679370192836809 6066685470509527644627607)
            ·
              refine ⟨9100028205764291466941411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6066685470509527644627607 9100028205764291466941411)
              ·
                refine ⟨13650042308646437200412117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9100028205764291466941411 13650042308646437200412117)
                ·
                  refine ⟨319922866608900871884659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13650042308646437200412117 319922866608900871884659)
                  ·
                    rfl

theorem cell21_1401857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 7].length) (baseStart_1401857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1401857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1401857 prefixEnd_1401857 := by exact prefixLift 1401857
  have htrace : WordTrace (prefixWord ++ tailWord_1401857) baseStart_1401857 baseEnd_1401857 := by
    simpa [prefixWord, tailWord_1401857, baseEnd_1401857] using wordTrace_append hprefix tailTrace_1401857
  have hstable : (prefixWord ++ tailWord_1401857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401857).length < 2 ^ (prefixWord ++ tailWord_1401857).sum := by decide
  have hdescent : baseEnd_1401857 < baseStart_1401857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401905 : List Nat := [1, 2, 2, 3, 1, 2, 5, 1, 4]
def baseStart_1401905 : Nat := 118140960795 + 1401905 * 2 ^ 59
def prefixEnd_1401905 : Nat := 4983230072969 + 3 ^ 40 * 1401905 * 2
def baseEnd_1401905 : Nat := 319933820862863455084561

theorem tailTrace_1401905 : CollatzResearch.WordTrace tailWord_1401905 prefixEnd_1401905 319933820862863455084561 := by
  unfold tailWord_1401905
  simp only [CollatzResearch.WordTrace]
  refine ⟨51131675986145086157407169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34087783990763390771604779 51131675986145086157407169)
  ·
    refine ⟨38348756989608814618055377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51131675986145086157407169 38348756989608814618055377)
    ·
      refine ⟨28761567742206610963541533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38348756989608814618055377 28761567742206610963541533)
      ·
        refine ⟨10785587903327479111328075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28761567742206610963541533 10785587903327479111328075)
        ·
          refine ⟨16178381854991218666992113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10785587903327479111328075 16178381854991218666992113)
          ·
            refine ⟨12133786391243414000244085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16178381854991218666992113 12133786391243414000244085)
            ·
              refine ⟨1137542474179070062522883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12133786391243414000244085 1137542474179070062522883)
              ·
                refine ⟨1706313711268605093784325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1137542474179070062522883 1706313711268605093784325)
                ·
                  refine ⟨319933820862863455084561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1706313711268605093784325 319933820862863455084561)
                  ·
                    rfl

theorem cell21_1401905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 4].length) (baseStart_1401905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1401905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1401905 prefixEnd_1401905 := by exact prefixLift 1401905
  have htrace : WordTrace (prefixWord ++ tailWord_1401905) baseStart_1401905 baseEnd_1401905 := by
    simpa [prefixWord, tailWord_1401905, baseEnd_1401905] using wordTrace_append hprefix tailTrace_1401905
  have hstable : (prefixWord ++ tailWord_1401905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401905).length < 2 ^ (prefixWord ++ tailWord_1401905).sum := by decide
  have hdescent : baseEnd_1401905 < baseStart_1401905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401942 : List Nat := [5, 2, 2, 1, 2, 1, 3, 2, 3]
def baseStart_1401942 : Nat := 118140960795 + 1401942 * 2 ^ 59
def prefixEnd_1401942 : Nat := 4983230072969 + 3 ^ 40 * 1401942 * 2
def baseEnd_1401942 : Nat := 319942264766959612967819

theorem tailTrace_1401942 : CollatzResearch.WordTrace tailWord_1401942 prefixEnd_1401942 319942264766959612967819 := by
  unfold tailWord_1401942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3195814092938190092281505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34088683658007360984336053 3195814092938190092281505)
  ·
    refine ⟨2396860569703642569211129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3195814092938190092281505 2396860569703642569211129)
    ·
      refine ⟨1797645427277731926908347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2396860569703642569211129 1797645427277731926908347)
      ·
        refine ⟨2696468140916597890362521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1797645427277731926908347 2696468140916597890362521)
        ·
          refine ⟨2022351105687448417771891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2696468140916597890362521 2022351105687448417771891)
          ·
            refine ⟨3033526658531172626657837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2022351105687448417771891 3033526658531172626657837)
            ·
              refine ⟨1137572496949189734996689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3033526658531172626657837 1137572496949189734996689)
              ·
                refine ⟨853179372711892301247517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1137572496949189734996689 853179372711892301247517)
                ·
                  refine ⟨319942264766959612967819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 853179372711892301247517 319942264766959612967819)
                  ·
                    rfl

theorem cell21_1401942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_1401942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1401942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1401942 prefixEnd_1401942 := by exact prefixLift 1401942
  have htrace : WordTrace (prefixWord ++ tailWord_1401942) baseStart_1401942 baseEnd_1401942 := by
    simpa [prefixWord, tailWord_1401942, baseEnd_1401942] using wordTrace_append hprefix tailTrace_1401942
  have hstable : (prefixWord ++ tailWord_1401942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401942).length < 2 ^ (prefixWord ++ tailWord_1401942).sum := by decide
  have hdescent : baseEnd_1401942 < baseStart_1401942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401964 : List Nat := [2, 2, 1, 1, 3, 2, 3, 3, 4]
def baseStart_1401964 : Nat := 118140960795 + 1401964 * 2 ^ 59
def prefixEnd_1401964 : Nat := 4983230072969 + 3 ^ 40 * 1401964 * 2
def baseEnd_1401964 : Nat := 319947285466692463601107

theorem tailTrace_1401964 : CollatzResearch.WordTrace tailWord_1401964 prefixEnd_1401964 319947285466692463601107 := by
  unfold tailWord_1401964
  simp only [CollatzResearch.WordTrace]
  refine ⟨25566913946465669616902473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34089218595287559489203297 25566913946465669616902473)
  ·
    refine ⟨19175185459849252212676855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25566913946465669616902473 19175185459849252212676855)
    ·
      refine ⟨28762778189773878319015283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19175185459849252212676855 28762778189773878319015283)
      ·
        refine ⟨43144167284660817478522925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28762778189773878319015283 43144167284660817478522925)
        ·
          refine ⟨16179062731747806554446097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43144167284660817478522925 16179062731747806554446097)
          ·
            refine ⟨12134297048810854915834573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16179062731747806554446097 12134297048810854915834573)
            ·
              refine ⟨4550361393304070593437965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12134297048810854915834573 4550361393304070593437965)
              ·
                refine ⟨1706385522489026472539237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4550361393304070593437965 1706385522489026472539237)
                ·
                  refine ⟨319947285466692463601107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1706385522489026472539237 319947285466692463601107)
                  ·
                    rfl

theorem cell21_1401964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_1401964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1401964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1401964 prefixEnd_1401964 := by exact prefixLift 1401964
  have htrace : WordTrace (prefixWord ++ tailWord_1401964) baseStart_1401964 baseEnd_1401964 := by
    simpa [prefixWord, tailWord_1401964, baseEnd_1401964] using wordTrace_append hprefix tailTrace_1401964
  have hstable : (prefixWord ++ tailWord_1401964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401964).length < 2 ^ (prefixWord ++ tailWord_1401964).sum := by decide
  have hdescent : baseEnd_1401964 < baseStart_1401964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402026 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 7]
def baseStart_1402026 : Nat := 118140960795 + 1402026 * 2 ^ 59
def prefixEnd_1402026 : Nat := 4983230072969 + 3 ^ 40 * 1402026 * 2
def baseEnd_1402026 : Nat := 319961434711394133567647

theorem tailTrace_1402026 : CollatzResearch.WordTrace tailWord_1402026 prefixEnd_1402026 319961434711394133567647 := by
  unfold tailWord_1402026
  simp only [CollatzResearch.WordTrace]
  refine ⟨12784022304676680955640483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34090726145804482548374621 12784022304676680955640483)
  ·
    refine ⟨19176033457015021433460725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12784022304676680955640483 19176033457015021433460725)
    ·
      refine ⟨1797753136595158259386943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19176033457015021433460725 1797753136595158259386943)
      ·
        refine ⟨2696629704892737389080415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1797753136595158259386943 2696629704892737389080415)
        ·
          refine ⟨4044944557339106083620623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2696629704892737389080415 4044944557339106083620623)
          ·
            refine ⟨6067416836008659125430935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4044944557339106083620623 6067416836008659125430935)
            ·
              refine ⟨9101125254012988688146403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6067416836008659125430935 9101125254012988688146403)
              ·
                refine ⟨13651687881019483032219605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9101125254012988688146403 13651687881019483032219605)
                ·
                  refine ⟨319961434711394133567647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13651687881019483032219605 319961434711394133567647)
                  ·
                    rfl

theorem cell21_1402026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_1402026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1402026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1402026 prefixEnd_1402026 := by exact prefixLift 1402026
  have htrace : WordTrace (prefixWord ++ tailWord_1402026) baseStart_1402026 baseEnd_1402026 := by
    simpa [prefixWord, tailWord_1402026, baseEnd_1402026] using wordTrace_append hprefix tailTrace_1402026
  have hstable : (prefixWord ++ tailWord_1402026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402026).length < 2 ^ (prefixWord ++ tailWord_1402026).sum := by decide
  have hdescent : baseEnd_1402026 < baseStart_1402026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402099 : List Nat := [1, 1, 1, 2, 2, 5, 1, 2, 6]
def baseStart_1402099 : Nat := 118140960795 + 1402099 * 2 ^ 59
def prefixEnd_1402099 : Nat := 4983230072969 + 3 ^ 40 * 1402099 * 2
def baseEnd_1402099 : Nat := 319978094305962228850831

theorem tailTrace_1402099 : CollatzResearch.WordTrace tailWord_1402099 prefixEnd_1402099 319978094305962228850831 := by
  unfold tailWord_1402099
  simp only [CollatzResearch.WordTrace]
  refine ⟨51138751747442257289969351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34092501164961504859979567 51138751747442257289969351)
  ·
    refine ⟨76708127621163385934954027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51138751747442257289969351 76708127621163385934954027)
    ·
      refine ⟨115062191431745078902431041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76708127621163385934954027 115062191431745078902431041)
      ·
        refine ⟨86296643573808809176823281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115062191431745078902431041 86296643573808809176823281)
        ·
          refine ⟨64722482680356606882617461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86296643573808809176823281 64722482680356606882617461)
          ·
            refine ⟨6067732751283431895245387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64722482680356606882617461 6067732751283431895245387)
            ·
              refine ⟨9101599126925147842868081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6067732751283431895245387 9101599126925147842868081)
              ·
                refine ⟨6826199345193860882151061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9101599126925147842868081 6826199345193860882151061)
                ·
                  refine ⟨319978094305962228850831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6826199345193860882151061 319978094305962228850831)
                  ·
                    rfl

theorem cell21_1402099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 6].length) (baseStart_1402099 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1402099 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1402099 prefixEnd_1402099 := by exact prefixLift 1402099
  have htrace : WordTrace (prefixWord ++ tailWord_1402099) baseStart_1402099 baseEnd_1402099 := by
    simpa [prefixWord, tailWord_1402099, baseEnd_1402099] using wordTrace_append hprefix tailTrace_1402099
  have hstable : (prefixWord ++ tailWord_1402099).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402099).length < 2 ^ (prefixWord ++ tailWord_1402099).sum := by decide
  have hdescent : baseEnd_1402099 < baseStart_1402099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402116 : List Nat := [2, 3, 2, 2, 2, 1, 2, 1, 6]
def baseStart_1402116 : Nat := 118140960795 + 1402116 * 2 ^ 59
def prefixEnd_1402116 : Nat := 4983230072969 + 3 ^ 40 * 1402116 * 2
def baseEnd_1402116 : Nat := 319981973937573977067463

theorem tailTrace_1402116 : CollatzResearch.WordTrace tailWord_1402116 prefixEnd_1402116 319981973937573977067463 := by
  unfold tailWord_1402116
  simp only [CollatzResearch.WordTrace]
  refine ⟨25569685894190334596669101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34092914525587112795558801 25569685894190334596669101)
  ·
    refine ⟨9588632210321375473750913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25569685894190334596669101 9588632210321375473750913)
    ·
      refine ⟨7191474157741031605313185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9588632210321375473750913 7191474157741031605313185)
      ·
        refine ⟨5393605618305773703984889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7191474157741031605313185 5393605618305773703984889)
        ·
          refine ⟨4045204213729330277988667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5393605618305773703984889 4045204213729330277988667)
          ·
            refine ⟨6067806320593995416983001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4045204213729330277988667 6067806320593995416983001)
            ·
              refine ⟨4550854740445496562737251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6067806320593995416983001 4550854740445496562737251)
              ·
                refine ⟨6826282110668244844105877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4550854740445496562737251 6826282110668244844105877)
                ·
                  refine ⟨319981973937573977067463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6826282110668244844105877 319981973937573977067463)
                  ·
                    rfl

theorem cell21_1402116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_1402116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1402116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1402116 prefixEnd_1402116 := by exact prefixLift 1402116
  have htrace : WordTrace (prefixWord ++ tailWord_1402116) baseStart_1402116 baseEnd_1402116 := by
    simpa [prefixWord, tailWord_1402116, baseEnd_1402116] using wordTrace_append hprefix tailTrace_1402116
  have hstable : (prefixWord ++ tailWord_1402116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402116).length < 2 ^ (prefixWord ++ tailWord_1402116).sum := by decide
  have hdescent : baseEnd_1402116 < baseStart_1402116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402237 : List Nat := [1, 4, 1, 1, 2, 2, 4, 1, 5]
def baseStart_1402237 : Nat := 118140960795 + 1402237 * 2 ^ 59
def prefixEnd_1402237 : Nat := 4983230072969 + 3 ^ 40 * 1402237 * 2
def baseEnd_1402237 : Nat := 320009587786104655550549

theorem tailTrace_1402237 : CollatzResearch.WordTrace tailWord_1402237 prefixEnd_1402237 320009587786104655550549 := by
  unfold tailWord_1402237
  simp only [CollatzResearch.WordTrace]
  refine ⟨51143785020942306858492965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34095856680628204572328643 51143785020942306858492965)
  ·
    refine ⟨9589459691426682535967431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51143785020942306858492965 9589459691426682535967431)
    ·
      refine ⟨14384189537140023803951147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9589459691426682535967431 14384189537140023803951147)
      ·
        refine ⟨21576284305710035705926721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14384189537140023803951147 21576284305710035705926721)
        ·
          refine ⟨16182213229282526779445041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21576284305710035705926721 16182213229282526779445041)
          ·
            refine ⟨12136659921961895084583781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16182213229282526779445041 12136659921961895084583781)
            ·
              refine ⟨2275623735367855328359459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12136659921961895084583781 2275623735367855328359459)
              ·
                refine ⟨3413435603051782992539189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2275623735367855328359459 3413435603051782992539189)
                ·
                  refine ⟨320009587786104655550549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3413435603051782992539189 320009587786104655550549)
                  ·
                    rfl

theorem cell21_1402237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_1402237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1402237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1402237 prefixEnd_1402237 := by exact prefixLift 1402237
  have htrace : WordTrace (prefixWord ++ tailWord_1402237) baseStart_1402237 baseEnd_1402237 := by
    simpa [prefixWord, tailWord_1402237, baseEnd_1402237] using wordTrace_append hprefix tailTrace_1402237
  have hstable : (prefixWord ++ tailWord_1402237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402237).length < 2 ^ (prefixWord ++ tailWord_1402237).sum := by decide
  have hdescent : baseEnd_1402237 < baseStart_1402237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402271 : List Nat := [1, 1, 2, 5, 1, 4, 1, 3, 3]
def baseStart_1402271 : Nat := 118140960795 + 1402271 * 2 ^ 59
def prefixEnd_1402271 : Nat := 4983230072969 + 3 ^ 40 * 1402271 * 2
def baseEnd_1402271 : Nat := 320017347049328151983813

theorem tailTrace_1402271 : CollatzResearch.WordTrace tailWord_1402271 prefixEnd_1402271 320017347049328151983813 := by
  unfold tailWord_1402271
  simp only [CollatzResearch.WordTrace]
  refine ⟨51145025102819130665230667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34096683401879420443487111 51145025102819130665230667)
  ·
    refine ⟨76717537654228695997846001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51145025102819130665230667 76717537654228695997846001)
    ·
      refine ⟨57538153240671521998384501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76717537654228695997846001 57538153240671521998384501)
      ·
        refine ⟨5394201866312955187348547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57538153240671521998384501 5394201866312955187348547)
        ·
          refine ⟨8091302799469432781022821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5394201866312955187348547 8091302799469432781022821)
          ·
            refine ⟨1517119274900518646441779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8091302799469432781022821 1517119274900518646441779)
            ·
              refine ⟨2275678912350777969662669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1517119274900518646441779 2275678912350777969662669)
              ·
                refine ⟨853379592131541738623501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2275678912350777969662669 853379592131541738623501)
                ·
                  refine ⟨320017347049328151983813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 853379592131541738623501 320017347049328151983813)
                  ·
                    rfl

theorem cell21_1402271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3, 3].length) (baseStart_1402271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1402271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1402271 prefixEnd_1402271 := by exact prefixLift 1402271
  have htrace : WordTrace (prefixWord ++ tailWord_1402271) baseStart_1402271 baseEnd_1402271 := by
    simpa [prefixWord, tailWord_1402271, baseEnd_1402271] using wordTrace_append hprefix tailTrace_1402271
  have hstable : (prefixWord ++ tailWord_1402271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402271).length < 2 ^ (prefixWord ++ tailWord_1402271).sum := by decide
  have hdescent : baseEnd_1402271 < baseStart_1402271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402344 : List Nat := [2, 1, 4, 1, 1, 2, 4, 2, 4]
def baseStart_1402344 : Nat := 118140960795 + 1402344 * 2 ^ 59
def prefixEnd_1402344 : Nat := 4983230072969 + 3 ^ 40 * 1402344 * 2
def baseEnd_1402344 : Nat := 320034006643896247266997

theorem tailTrace_1402344 : CollatzResearch.WordTrace tailWord_1402344 prefixEnd_1402344 320034006643896247266997 := by
  unfold tailWord_1402344
  simp only [CollatzResearch.WordTrace]
  refine ⟨25573843815777332066319043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34098458421036442755092057 25573843815777332066319043)
  ·
    refine ⟨38360765723665998099478565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25573843815777332066319043 38360765723665998099478565)
    ·
      refine ⟨7192643573187374643652231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38360765723665998099478565 7192643573187374643652231)
      ·
        refine ⟨10788965359781061965478347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7192643573187374643652231 10788965359781061965478347)
        ·
          refine ⟨16183448039671592948217521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10788965359781061965478347 16183448039671592948217521)
          ·
            refine ⟨12137586029753694711163141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16183448039671592948217521 12137586029753694711163141)
            ·
              refine ⟨2275797380578817758343089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12137586029753694711163141 2275797380578817758343089)
              ·
                refine ⟨1706848035434113318757317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2275797380578817758343089 1706848035434113318757317)
                ·
                  refine ⟨320034006643896247266997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1706848035434113318757317 320034006643896247266997)
                  ·
                    rfl

theorem cell21_1402344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 4].length) (baseStart_1402344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1402344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1402344 prefixEnd_1402344 := by exact prefixLift 1402344
  have htrace : WordTrace (prefixWord ++ tailWord_1402344) baseStart_1402344 baseEnd_1402344 := by
    simpa [prefixWord, tailWord_1402344, baseEnd_1402344] using wordTrace_append hprefix tailTrace_1402344
  have hstable : (prefixWord ++ tailWord_1402344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402344).length < 2 ^ (prefixWord ++ tailWord_1402344).sum := by decide
  have hdescent : baseEnd_1402344 < baseStart_1402344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402375 : List Nat := [1, 1, 4, 3, 2, 2, 3, 5]
def baseStart_1402375 : Nat := 118140960795 + 1402375 * 2 ^ 59
def prefixEnd_1402375 : Nat := 4983230072969 + 3 ^ 40 * 1402375 * 2
def baseEnd_1402375 : Nat := 106680360422082360750089

theorem tailTrace_1402375 : CollatzResearch.WordTrace tailWord_1402375 prefixEnd_1402375 106680360422082360750089 := by
  unfold tailWord_1402375
  simp only [CollatzResearch.WordTrace]
  refine ⟨51148818294442356427016579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34099212196294904284677719 51148818294442356427016579)
  ·
    refine ⟨76723227441663534640524869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51148818294442356427016579 76723227441663534640524869)
    ·
      refine ⟨14385605145311912745098413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76723227441663534640524869 14385605145311912745098413)
      ·
        refine ⟨5394601929491967279411905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14385605145311912745098413 5394601929491967279411905)
        ·
          refine ⟨4045951447118975459558929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5394601929491967279411905 4045951447118975459558929)
          ·
            refine ⟨3034463585339231594669197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4045951447118975459558929 3034463585339231594669197)
            ·
              refine ⟨1137923844502211848000949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3034463585339231594669197 1137923844502211848000949)
              ·
                refine ⟨106680360422082360750089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1137923844502211848000949 106680360422082360750089)
                ·
                  rfl

theorem cell21_1402375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 5].length) (baseStart_1402375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1402375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1402375 prefixEnd_1402375 := by exact prefixLift 1402375
  have htrace : WordTrace (prefixWord ++ tailWord_1402375) baseStart_1402375 baseEnd_1402375 := by
    simpa [prefixWord, tailWord_1402375, baseEnd_1402375] using wordTrace_append hprefix tailTrace_1402375
  have hstable : (prefixWord ++ tailWord_1402375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402375).length < 2 ^ (prefixWord ++ tailWord_1402375).sum := by decide
  have hdescent : baseEnd_1402375 < baseStart_1402375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402381 : List Nat := [1, 7, 1, 1, 2, 1, 2, 3, 3]
def baseStart_1402381 : Nat := 118140960795 + 1402381 * 2 ^ 59
def prefixEnd_1402381 : Nat := 4983230072969 + 3 ^ 40 * 1402381 * 2
def baseEnd_1402381 : Nat := 320042450547992405150255

theorem tailTrace_1402381 : CollatzResearch.WordTrace tailWord_1402381 prefixEnd_1402381 320042450547992405150255 := by
  unfold tailWord_1402381
  simp only [CollatzResearch.WordTrace]
  refine ⟨51149037132420619451734997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34099358088280412967823331 51149037132420619451734997)
  ·
    refine ⟨1198805557791108268400039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 51149037132420619451734997 1198805557791108268400039)
    ·
      refine ⟨1798208336686662402600059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1198805557791108268400039 1798208336686662402600059)
      ·
        refine ⟨2697312505029993603900089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1798208336686662402600059 2697312505029993603900089)
        ·
          refine ⟨2022984378772495202925067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2697312505029993603900089 2022984378772495202925067)
          ·
            refine ⟨3034476568158742804387601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2022984378772495202925067 3034476568158742804387601)
            ·
              refine ⟨2275857426119057103290701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3034476568158742804387601 2275857426119057103290701)
              ·
                refine ⟨853446534794646413734013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2275857426119057103290701 853446534794646413734013)
                ·
                  refine ⟨320042450547992405150255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 853446534794646413734013 320042450547992405150255)
                  ·
                    rfl

theorem cell21_1402381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_1402381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1402381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1402381 prefixEnd_1402381 := by exact prefixLift 1402381
  have htrace : WordTrace (prefixWord ++ tailWord_1402381) baseStart_1402381 baseEnd_1402381 := by
    simpa [prefixWord, tailWord_1402381, baseEnd_1402381] using wordTrace_append hprefix tailTrace_1402381
  have hstable : (prefixWord ++ tailWord_1402381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402381).length < 2 ^ (prefixWord ++ tailWord_1402381).sum := by decide
  have hdescent : baseEnd_1402381 < baseStart_1402381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402417 : List Nat := [1, 2, 2, 3, 1, 1, 1, 10]
def baseStart_1402417 : Nat := 118140960795 + 1402417 * 2 ^ 59
def prefixEnd_1402417 : Nat := 4983230072969 + 3 ^ 40 * 1402417 * 2
def baseEnd_1402417 : Nat := 106683555412821447516727

theorem tailTrace_1402417 : CollatzResearch.WordTrace tailWord_1402417 prefixEnd_1402417 106683555412821447516727 := by
  unfold tailWord_1402417
  simp only [CollatzResearch.WordTrace]
  refine ⟨51150350160290197600045505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34100233440193465066697003 51150350160290197600045505)
  ·
    refine ⟨38362762620217648200034129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51150350160290197600045505 38362762620217648200034129)
    ·
      refine ⟨28772071965163236150025597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38362762620217648200034129 28772071965163236150025597)
      ·
        refine ⟨10789526986936213556259599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28772071965163236150025597 10789526986936213556259599)
        ·
          refine ⟨16184290480404320334389399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10789526986936213556259599 16184290480404320334389399)
          ·
            refine ⟨24276435720606480501584099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16184290480404320334389399 24276435720606480501584099)
            ·
              refine ⟨36414653580909720752376149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24276435720606480501584099 36414653580909720752376149)
              ·
                refine ⟨106683555412821447516727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36414653580909720752376149 106683555412821447516727)
                ·
                  rfl

theorem cell21_1402417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 10].length) (baseStart_1402417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1402417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1402417 prefixEnd_1402417 := by exact prefixLift 1402417
  have htrace : WordTrace (prefixWord ++ tailWord_1402417) baseStart_1402417 baseEnd_1402417 := by
    simpa [prefixWord, tailWord_1402417, baseEnd_1402417] using wordTrace_append hprefix tailTrace_1402417
  have hstable : (prefixWord ++ tailWord_1402417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402417).length < 2 ^ (prefixWord ++ tailWord_1402417).sum := by decide
  have hdescent : baseEnd_1402417 < baseStart_1402417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402541 : List Nat := [1, 5, 2, 1, 1, 1, 3, 2, 5]
def baseStart_1402541 : Nat := 118140960795 + 1402541 * 2 ^ 59
def prefixEnd_1402541 : Nat := 4983230072969 + 3 ^ 40 * 1402541 * 2
def baseEnd_1402541 : Nat := 320078964727867682483261

theorem tailTrace_1402541 : CollatzResearch.WordTrace tailWord_1402541 prefixEnd_1402541 320078964727867682483261 := by
  unfold tailWord_1402541
  simp only [CollatzResearch.WordTrace]
  refine ⟨51154872811840966777559477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34103248541227311185039651 51154872811840966777559477)
  ·
    refine ⟨4795769326110090635396201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51154872811840966777559477 4795769326110090635396201)
    ·
      refine ⟨3596826994582567976547151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4795769326110090635396201 3596826994582567976547151)
      ·
        refine ⟨5395240491873851964820727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3596826994582567976547151 5395240491873851964820727)
        ·
          refine ⟨8092860737810777947231091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5395240491873851964820727 8092860737810777947231091)
          ·
            refine ⟨12139291106716166920846637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8092860737810777947231091 12139291106716166920846637)
            ·
              refine ⟨4552234165018562595317489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12139291106716166920846637 4552234165018562595317489)
              ·
                refine ⟨3414175623763921946488117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4552234165018562595317489 3414175623763921946488117)
                ·
                  refine ⟨320078964727867682483261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3414175623763921946488117 320078964727867682483261)
                  ·
                    rfl

theorem cell21_1402541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_1402541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1402541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1402541 prefixEnd_1402541 := by exact prefixLift 1402541
  have htrace : WordTrace (prefixWord ++ tailWord_1402541) baseStart_1402541 baseEnd_1402541 := by
    simpa [prefixWord, tailWord_1402541, baseEnd_1402541] using wordTrace_append hprefix tailTrace_1402541
  have hstable : (prefixWord ++ tailWord_1402541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402541).length < 2 ^ (prefixWord ++ tailWord_1402541).sum := by decide
  have hdescent : baseEnd_1402541 < baseStart_1402541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402558 : List Nat := [4, 2, 1, 1, 2, 2, 1, 5, 3]
def baseStart_1402558 : Nat := 118140960795 + 1402558 * 2 ^ 59
def prefixEnd_1402558 : Nat := 4983230072969 + 3 ^ 40 * 1402558 * 2
def baseEnd_1402558 : Nat := 320082844359479430699893

theorem tailTrace_1402558 : CollatzResearch.WordTrace tailWord_1402558 prefixEnd_1402558 320082844359479430699893 := by
  unfold tailWord_1402558
  simp only [CollatzResearch.WordTrace]
  refine ⟨6394436606597422335116041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34103661901852919120618885 6394436606597422335116041)
  ·
    refine ⟨4795827454948066751337031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6394436606597422335116041 4795827454948066751337031)
    ·
      refine ⟨7193741182422100127005547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4795827454948066751337031 7193741182422100127005547)
      ·
        refine ⟨10790611773633150190508321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7193741182422100127005547 10790611773633150190508321)
        ·
          refine ⟨8092958830224862642881241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10790611773633150190508321 8092958830224862642881241)
          ·
            refine ⟨6069719122668646982160931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8092958830224862642881241 6069719122668646982160931)
            ·
              refine ⟨9104578684002970473241397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6069719122668646982160931 9104578684002970473241397)
              ·
                refine ⟨853554251625278481866381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9104578684002970473241397 853554251625278481866381)
                ·
                  refine ⟨320082844359479430699893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 853554251625278481866381 320082844359479430699893)
                  ·
                    rfl

theorem cell21_1402558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_1402558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1402558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1402558 prefixEnd_1402558 := by exact prefixLift 1402558
  have htrace : WordTrace (prefixWord ++ tailWord_1402558) baseStart_1402558 baseEnd_1402558 := by
    simpa [prefixWord, tailWord_1402558, baseEnd_1402558] using wordTrace_append hprefix tailTrace_1402558
  have hstable : (prefixWord ++ tailWord_1402558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402558).length < 2 ^ (prefixWord ++ tailWord_1402558).sum := by decide
  have hdescent : baseEnd_1402558 < baseStart_1402558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402572 : List Nat := [2, 2, 1, 5, 2, 1, 1, 1, 6]
def baseStart_1402572 : Nat := 118140960795 + 1402572 * 2 ^ 59
def prefixEnd_1402572 : Nat := 4983230072969 + 3 ^ 40 * 1402572 * 2
def baseEnd_1402572 : Nat := 320086039350218517466531

theorem tailTrace_1402572 : CollatzResearch.WordTrace tailWord_1402572 prefixEnd_1402572 320086039350218517466531 := by
  unfold tailWord_1402572
  simp only [CollatzResearch.WordTrace]
  refine ⟨25578001737364329535968985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34104002316485772714625313 25578001737364329535968985)
  ·
    refine ⟨19183501303023247151976739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25578001737364329535968985 19183501303023247151976739)
    ·
      refine ⟨28775251954534870727965109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19183501303023247151976739 28775251954534870727965109)
      ·
        refine ⟨2697679870737644130746729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28775251954534870727965109 2697679870737644130746729)
        ·
          refine ⟨2023259903053233098060047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2697679870737644130746729 2023259903053233098060047)
          ·
            refine ⟨3034889854579849647090071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2023259903053233098060047 3034889854579849647090071)
            ·
              refine ⟨4552334781869774470635107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3034889854579849647090071 4552334781869774470635107)
              ·
                refine ⟨6828502172804661705952661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4552334781869774470635107 6828502172804661705952661)
                ·
                  refine ⟨320086039350218517466531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6828502172804661705952661 320086039350218517466531)
                  ·
                    rfl

theorem cell21_1402572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_1402572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1402572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1402572 prefixEnd_1402572 := by exact prefixLift 1402572
  have htrace : WordTrace (prefixWord ++ tailWord_1402572) baseStart_1402572 baseEnd_1402572 := by
    simpa [prefixWord, tailWord_1402572, baseEnd_1402572] using wordTrace_append hprefix tailTrace_1402572
  have hstable : (prefixWord ++ tailWord_1402572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402572).length < 2 ^ (prefixWord ++ tailWord_1402572).sum := by decide
  have hdescent : baseEnd_1402572 < baseStart_1402572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402645 : List Nat := [1, 3, 2, 1, 2, 3, 1, 8]
def baseStart_1402645 : Nat := 118140960795 + 1402645 * 2 ^ 59
def prefixEnd_1402645 : Nat := 4983230072969 + 3 ^ 40 * 1402645 * 2
def baseEnd_1402645 : Nat := 106700899648262204249905

theorem tailTrace_1402645 : CollatzResearch.WordTrace tailWord_1402645 prefixEnd_1402645 106700899648262204249905 := by
  unfold tailWord_1402645
  simp only [CollatzResearch.WordTrace]
  refine ⟨51158666003464192539345389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34105777335642795026230259 51158666003464192539345389)
  ·
    refine ⟨19184499751299072202254521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51158666003464192539345389 19184499751299072202254521)
    ·
      refine ⟨14388374813474304151690891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19184499751299072202254521 14388374813474304151690891)
      ·
        refine ⟨21582562220211456227536337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14388374813474304151690891 21582562220211456227536337)
        ·
          refine ⟨16186921665158592170652253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21582562220211456227536337 16186921665158592170652253)
          ·
            refine ⟨6070095624434472063994595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16186921665158592170652253 6070095624434472063994595)
            ·
              refine ⟨9105143436651708095991893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6070095624434472063994595 9105143436651708095991893)
              ·
                refine ⟨106700899648262204249905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9105143436651708095991893 106700899648262204249905)
                ·
                  rfl

theorem cell21_1402645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 8].length) (baseStart_1402645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1402645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1402645 prefixEnd_1402645 := by exact prefixLift 1402645
  have htrace : WordTrace (prefixWord ++ tailWord_1402645) baseStart_1402645 baseEnd_1402645 := by
    simpa [prefixWord, tailWord_1402645, baseEnd_1402645] using wordTrace_append hprefix tailTrace_1402645
  have hstable : (prefixWord ++ tailWord_1402645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402645).length < 2 ^ (prefixWord ++ tailWord_1402645).sum := by decide
  have hdescent : baseEnd_1402645 < baseStart_1402645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402648 : List Nat := [2, 1, 2, 3, 1, 1, 6, 1, 4]
def baseStart_1402648 : Nat := 118140960795 + 1402648 * 2 ^ 59
def prefixEnd_1402648 : Nat := 4983230072969 + 3 ^ 40 * 1402648 * 2
def baseEnd_1402648 : Nat := 320103383585659274199709

theorem tailTrace_1402648 : CollatzResearch.WordTrace tailWord_1402648 prefixEnd_1402648 320103383585659274199709 := by
  unfold tailWord_1402648
  simp only [CollatzResearch.WordTrace]
  refine ⟨25579387711226662025852299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34105850281635549367803065 25579387711226662025852299)
  ·
    refine ⟨38369081566839993038778449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25579387711226662025852299 38369081566839993038778449)
    ·
      refine ⟨28776811175129994779083837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38369081566839993038778449 28776811175129994779083837)
      ·
        refine ⟨10791304190673748042156439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28776811175129994779083837 10791304190673748042156439)
        ·
          refine ⟨16186956286010622063234659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10791304190673748042156439 16186956286010622063234659)
          ·
            refine ⟨24280434429015933094851989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16186956286010622063234659 24280434429015933094851989)
            ·
              refine ⟨1138145363860121863821187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24280434429015933094851989 1138145363860121863821187)
              ·
                refine ⟨1707218045790182795731781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1138145363860121863821187 1707218045790182795731781)
                ·
                  refine ⟨320103383585659274199709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1707218045790182795731781 320103383585659274199709)
                  ·
                    rfl

theorem cell21_1402648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 4].length) (baseStart_1402648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1402648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1402648 prefixEnd_1402648 := by exact prefixLift 1402648
  have htrace : WordTrace (prefixWord ++ tailWord_1402648) baseStart_1402648 baseEnd_1402648 := by
    simpa [prefixWord, tailWord_1402648, baseEnd_1402648] using wordTrace_append hprefix tailTrace_1402648
  have hstable : (prefixWord ++ tailWord_1402648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402648).length < 2 ^ (prefixWord ++ tailWord_1402648).sum := by decide
  have hdescent : baseEnd_1402648 < baseStart_1402648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402693 : List Nat := [1, 3, 1, 1, 1, 2, 5, 4, 3]
def baseStart_1402693 : Nat := 118140960795 + 1402693 * 2 ^ 59
def prefixEnd_1402693 : Nat := 4983230072969 + 3 ^ 40 * 1402693 * 2
def baseEnd_1402693 : Nat := 320113653198749195949617

theorem tailTrace_1402693 : CollatzResearch.WordTrace tailWord_1402693 prefixEnd_1402693 320113653198749195949617 := by
  unfold tailWord_1402693
  simp only [CollatzResearch.WordTrace]
  refine ⟨51160416707290296737092733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34106944471526864491395155 51160416707290296737092733)
  ·
    refine ⟨19185156265233861276409775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51160416707290296737092733 19185156265233861276409775)
    ·
      refine ⟨28777734397850791914614663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19185156265233861276409775 28777734397850791914614663)
      ·
        refine ⟨43166601596776187871921995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28777734397850791914614663 43166601596776187871921995)
        ·
          refine ⟨64749902395164281807882993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43166601596776187871921995 64749902395164281807882993)
          ·
            refine ⟨48562426796373211355912245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64749902395164281807882993 48562426796373211355912245)
            ·
              refine ⟨4552727512159988564616773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48562426796373211355912245 4552727512159988564616773)
              ·
                refine ⟨853636408529997855865645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4552727512159988564616773 853636408529997855865645)
                ·
                  refine ⟨320113653198749195949617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 853636408529997855865645 320113653198749195949617)
                  ·
                    rfl

theorem cell21_1402693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4, 3].length) (baseStart_1402693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1402693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1402693 prefixEnd_1402693 := by exact prefixLift 1402693
  have htrace : WordTrace (prefixWord ++ tailWord_1402693) baseStart_1402693 baseEnd_1402693 := by
    simpa [prefixWord, tailWord_1402693, baseEnd_1402693] using wordTrace_append hprefix tailTrace_1402693
  have hstable : (prefixWord ++ tailWord_1402693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402693).length < 2 ^ (prefixWord ++ tailWord_1402693).sum := by decide
  have hdescent : baseEnd_1402693 < baseStart_1402693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402752 : List Nat := [2, 1, 1, 2, 1, 2, 6, 1, 5]
def baseStart_1402752 : Nat := 118140960795 + 1402752 * 2 ^ 59
def prefixEnd_1402752 : Nat := 4983230072969 + 3 ^ 40 * 1402752 * 2
def baseEnd_1402752 : Nat := 320127117802578204466163

theorem tailTrace_1402752 : CollatzResearch.WordTrace tailWord_1402752 prefixEnd_1402752 320127117802578204466163 := by
  unfold tailWord_1402752
  simp only [CollatzResearch.WordTrace]
  refine ⟨25581284307038274906745255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34108379076051033208993673 25581284307038274906745255)
  ·
    refine ⟨38371926460557412360117883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25581284307038274906745255 38371926460557412360117883)
    ·
      refine ⟨57557889690836118540176825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38371926460557412360117883 57557889690836118540176825)
      ·
        refine ⟨43168417268127088905132619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57557889690836118540176825 43168417268127088905132619)
        ·
          refine ⟨64752625902190633357698929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43168417268127088905132619 64752625902190633357698929)
          ·
            refine ⟨48564469426642975018274197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64752625902190633357698929 48564469426642975018274197)
            ·
              refine ⟨2276459504373889453981603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48564469426642975018274197 2276459504373889453981603)
              ·
                refine ⟨3414689256560834180972405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2276459504373889453981603 3414689256560834180972405)
                ·
                  refine ⟨320127117802578204466163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3414689256560834180972405 320127117802578204466163)
                  ·
                    rfl

theorem cell21_1402752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 5].length) (baseStart_1402752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1402752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1402752 prefixEnd_1402752 := by exact prefixLift 1402752
  have htrace : WordTrace (prefixWord ++ tailWord_1402752) baseStart_1402752 baseEnd_1402752 := by
    simpa [prefixWord, tailWord_1402752, baseEnd_1402752] using wordTrace_append hprefix tailTrace_1402752
  have hstable : (prefixWord ++ tailWord_1402752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402752).length < 2 ^ (prefixWord ++ tailWord_1402752).sum := by decide
  have hdescent : baseEnd_1402752 < baseStart_1402752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402814 : List Nat := [4, 2, 1, 1, 1, 4, 2, 6]
def baseStart_1402814 : Nat := 118140960795 + 1402814 * 2 ^ 59
def prefixEnd_1402814 : Nat := 4983230072969 + 3 ^ 40 * 1402814 * 2
def baseEnd_1402814 : Nat := 106713755682426624810901

theorem tailTrace_1402814 : CollatzResearch.WordTrace tailWord_1402814 prefixEnd_1402814 106713755682426624810901 := by
  unfold tailWord_1402814
  simp only [CollatzResearch.WordTrace]
  refine ⟨6395603742481491800280937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34109886626567956268164997 6395603742481491800280937)
  ·
    refine ⟨4796702806861118850210703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6395603742481491800280937 4796702806861118850210703)
    ·
      refine ⟨7195054210291678275316055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4796702806861118850210703 7195054210291678275316055)
      ·
        refine ⟨10792581315437517412974083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7195054210291678275316055 10792581315437517412974083)
        ·
          refine ⟨16188871973156276119461125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10792581315437517412974083 16188871973156276119461125)
          ·
            refine ⟨3035413494966801772398961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16188871973156276119461125 3035413494966801772398961)
            ·
              refine ⟨2276560121225101329299221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3035413494966801772398961 2276560121225101329299221)
              ·
                refine ⟨106713755682426624810901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2276560121225101329299221 106713755682426624810901)
                ·
                  rfl

theorem cell21_1402814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_1402814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1402814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1402814 prefixEnd_1402814 := by exact prefixLift 1402814
  have htrace : WordTrace (prefixWord ++ tailWord_1402814) baseStart_1402814 baseEnd_1402814 := by
    simpa [prefixWord, tailWord_1402814, baseEnd_1402814] using wordTrace_append hprefix tailTrace_1402814
  have hstable : (prefixWord ++ tailWord_1402814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402814).length < 2 ^ (prefixWord ++ tailWord_1402814).sum := by decide
  have hdescent : baseEnd_1402814 < baseStart_1402814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402862 : List Nat := [4, 1, 2, 1, 3, 2, 1, 4, 3]
def baseStart_1402862 : Nat := 118140960795 + 1402862 * 2 ^ 59
def prefixEnd_1402862 : Nat := 4983230072969 + 3 ^ 40 * 1402862 * 2
def baseEnd_1402862 : Nat := 320152221301242457632605

theorem tailTrace_1402862 : CollatzResearch.WordTrace tailWord_1402862 prefixEnd_1402862 320152221301242457632605 := by
  unfold tailWord_1402862
  simp only [CollatzResearch.WordTrace]
  refine ⟨6395822580459754824999355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34111053762452025733329893 6395822580459754824999355)
  ·
    refine ⟨9593733870689632237499033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6395822580459754824999355 9593733870689632237499033)
    ·
      refine ⟨7195300403017224178124275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9593733870689632237499033 7195300403017224178124275)
      ·
        refine ⟨10792950604525836267186413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7195300403017224178124275 10792950604525836267186413)
        ·
          refine ⟨4047356476697188600194905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10792950604525836267186413 4047356476697188600194905)
          ·
            refine ⟨3035517357522891450146179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4047356476697188600194905 3035517357522891450146179)
            ·
              refine ⟨4553276036284337175219269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3035517357522891450146179 4553276036284337175219269)
              ·
                refine ⟨853739256803313220353613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4553276036284337175219269 853739256803313220353613)
                ·
                  refine ⟨320152221301242457632605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 853739256803313220353613 320152221301242457632605)
                  ·
                    rfl

theorem cell21_1402862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_1402862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1402862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1402862 prefixEnd_1402862 := by exact prefixLift 1402862
  have htrace : WordTrace (prefixWord ++ tailWord_1402862) baseStart_1402862 baseEnd_1402862 := by
    simpa [prefixWord, tailWord_1402862, baseEnd_1402862] using wordTrace_append hprefix tailTrace_1402862
  have hstable : (prefixWord ++ tailWord_1402862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402862).length < 2 ^ (prefixWord ++ tailWord_1402862).sum := by decide
  have hdescent : baseEnd_1402862 < baseStart_1402862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402873 : List Nat := [1, 2, 1, 3, 1, 4, 3, 6]
def baseStart_1402873 : Nat := 118140960795 + 1402873 * 2 ^ 59
def prefixEnd_1402873 : Nat := 4983230072969 + 3 ^ 40 * 1402873 * 2
def baseEnd_1402873 : Nat := 106718243883702960983083

theorem tailTrace_1402873 : CollatzResearch.WordTrace tailWord_1402873 prefixEnd_1402873 106718243883702960983083 := by
  unfold tailWord_1402873
  simp only [CollatzResearch.WordTrace]
  refine ⟨51166981846638187478645273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34111321231092124985763515 51166981846638187478645273)
  ·
    refine ⟨38375236384978640608983955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51166981846638187478645273 38375236384978640608983955)
    ·
      refine ⟨57562854577467960913475933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38375236384978640608983955 57562854577467960913475933)
      ·
        refine ⟨21586070466550485342553475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57562854577467960913475933 21586070466550485342553475)
        ·
          refine ⟨32379105699825728013830213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21586070466550485342553475 32379105699825728013830213)
          ·
            refine ⟨6071082318717324002593165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32379105699825728013830213 6071082318717324002593165)
            ·
              refine ⟨2276655869518996500972437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6071082318717324002593165 2276655869518996500972437)
              ·
                refine ⟨106718243883702960983083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2276655869518996500972437 106718243883702960983083)
                ·
                  rfl

theorem cell21_1402873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 6].length) (baseStart_1402873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1402873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1402873 prefixEnd_1402873 := by exact prefixLift 1402873
  have htrace : WordTrace (prefixWord ++ tailWord_1402873) baseStart_1402873 baseEnd_1402873 := by
    simpa [prefixWord, tailWord_1402873, baseEnd_1402873] using wordTrace_append hprefix tailTrace_1402873
  have hstable : (prefixWord ++ tailWord_1402873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402873).length < 2 ^ (prefixWord ++ tailWord_1402873).sum := by decide
  have hdescent : baseEnd_1402873 < baseStart_1402873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402980 : List Nat := [2, 3, 1, 1, 2, 1, 5, 1, 5]
def baseStart_1402980 : Nat := 118140960795 + 1402980 * 2 ^ 59
def prefixEnd_1402980 : Nat := 4983230072969 + 3 ^ 40 * 1402980 * 2
def baseEnd_1402980 : Nat := 320179150508900474665697

theorem tailTrace_1402980 : CollatzResearch.WordTrace tailWord_1402980 prefixEnd_1402980 320179150508900474665697 := by
  unfold tailWord_1402980
  simp only [CollatzResearch.WordTrace]
  refine ⟨25585442228625272376395197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34113922971500363168526929 25585442228625272376395197)
  ·
    refine ⟨9594540835734477141148199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25585442228625272376395197 9594540835734477141148199)
    ·
      refine ⟨14391811253601715711722299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9594540835734477141148199 14391811253601715711722299)
      ·
        refine ⟨21587716880402573567583449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14391811253601715711722299 21587716880402573567583449)
        ·
          refine ⟨16190787660301930175687587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21587716880402573567583449 16190787660301930175687587)
          ·
            refine ⟨24286181490452895263531381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16190787660301930175687587 24286181490452895263531381)
            ·
              refine ⟨2276829514729958930956067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24286181490452895263531381 2276829514729958930956067)
              ·
                refine ⟨3415244272094938396434101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2276829514729958930956067 3415244272094938396434101)
                ·
                  refine ⟨320179150508900474665697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3415244272094938396434101 320179150508900474665697)
                  ·
                    rfl

theorem cell21_1402980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_1402980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1402980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1402980 prefixEnd_1402980 := by exact prefixLift 1402980
  have htrace : WordTrace (prefixWord ++ tailWord_1402980) baseStart_1402980 baseEnd_1402980 := by
    simpa [prefixWord, tailWord_1402980, baseEnd_1402980] using wordTrace_append hprefix tailTrace_1402980
  have hstable : (prefixWord ++ tailWord_1402980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402980).length < 2 ^ (prefixWord ++ tailWord_1402980).sum := by decide
  have hdescent : baseEnd_1402980 < baseStart_1402980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402986 : List Nat := [3, 1, 3, 2, 4, 1, 2, 1, 4]
def baseStart_1402986 : Nat := 118140960795 + 1402986 * 2 ^ 59
def prefixEnd_1402986 : Nat := 4983230072969 + 3 ^ 40 * 1402986 * 2
def baseEnd_1402986 : Nat := 320180519790645797565685

theorem tailTrace_1402986 : CollatzResearch.WordTrace tailWord_1402986 prefixEnd_1402986 320180519790645797565685 := by
  unfold tailWord_1402986
  simp only [CollatzResearch.WordTrace]
  refine ⟨12792775823807201944377203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34114068863485871851672541 12792775823807201944377203)
  ·
    refine ⟨19189163735710802916565805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12792775823807201944377203 19189163735710802916565805)
    ·
      refine ⟨7195936400891551093712177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19189163735710802916565805 7195936400891551093712177)
      ·
        refine ⟨5396952300668663320284133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7195936400891551093712177 5396952300668663320284133)
        ·
          refine ⟨1011928556375374372553275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5396952300668663320284133 1011928556375374372553275)
          ·
            refine ⟨1517892834563061558829913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1011928556375374372553275 1517892834563061558829913)
            ·
              refine ⟨1138419625922296169122435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1517892834563061558829913 1138419625922296169122435)
              ·
                refine ⟨1707629438883444253683653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1138419625922296169122435 1707629438883444253683653)
                ·
                  refine ⟨320180519790645797565685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1707629438883444253683653 320180519790645797565685)
                  ·
                    rfl

theorem cell21_1402986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 4].length) (baseStart_1402986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1402986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1402986 prefixEnd_1402986 := by exact prefixLift 1402986
  have htrace : WordTrace (prefixWord ++ tailWord_1402986) baseStart_1402986 baseEnd_1402986 := by
    simpa [prefixWord, tailWord_1402986, baseEnd_1402986] using wordTrace_append hprefix tailTrace_1402986
  have hstable : (prefixWord ++ tailWord_1402986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402986).length < 2 ^ (prefixWord ++ tailWord_1402986).sum := by decide
  have hdescent : baseEnd_1402986 < baseStart_1402986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403031 : List Nat := [1, 1, 3, 3, 4, 2, 2, 2, 3]
def baseStart_1403031 : Nat := 118140960795 + 1403031 * 2 ^ 59
def prefixEnd_1403031 : Nat := 4983230072969 + 3 ^ 40 * 1403031 * 2
def baseEnd_1403031 : Nat := 320190789403735719315593

theorem tailTrace_1403031 : CollatzResearch.WordTrace tailWord_1403031 prefixEnd_1403031 320190789403735719315593 := by
  unfold tailWord_1403031
  simp only [CollatzResearch.WordTrace]
  refine ⟨51172744580065780462896947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34115163053377186975264631 51172744580065780462896947)
  ·
    refine ⟨76759116870098670694345421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51172744580065780462896947 76759116870098670694345421)
    ·
      refine ⟨28784668826287001510379533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76759116870098670694345421 28784668826287001510379533)
      ·
        refine ⟨10794250809857625566392325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28784668826287001510379533 10794250809857625566392325)
        ·
          refine ⟨2023922026848304793698561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10794250809857625566392325 2023922026848304793698561)
          ·
            refine ⟨1517941520136228595273921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2023922026848304793698561 1517941520136228595273921)
            ·
              refine ⟨1138456140102171446455441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1517941520136228595273921 1138456140102171446455441)
              ·
                refine ⟨853842105076628584841581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1138456140102171446455441 853842105076628584841581)
                ·
                  refine ⟨320190789403735719315593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 853842105076628584841581 320190789403735719315593)
                  ·
                    rfl

theorem cell21_1403031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2, 3].length) (baseStart_1403031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1403031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1403031 prefixEnd_1403031 := by exact prefixLift 1403031
  have htrace : WordTrace (prefixWord ++ tailWord_1403031) baseStart_1403031 baseEnd_1403031 := by
    simpa [prefixWord, tailWord_1403031, baseEnd_1403031] using wordTrace_append hprefix tailTrace_1403031
  have hstable : (prefixWord ++ tailWord_1403031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403031).length < 2 ^ (prefixWord ++ tailWord_1403031).sum := by decide
  have hdescent : baseEnd_1403031 < baseStart_1403031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403042 : List Nat := [3, 3, 1, 3, 1, 1, 3, 6]
def baseStart_1403042 : Nat := 118140960795 + 1403042 * 2 ^ 59
def prefixEnd_1403042 : Nat := 4983230072969 + 3 ^ 40 * 1403042 * 2
def baseEnd_1403042 : Nat := 106731099917867381544079

theorem tailTrace_1403042 : CollatzResearch.WordTrace tailWord_1403042 prefixEnd_1403042 106731099917867381544079 := by
  unfold tailWord_1403042
  simp only [CollatzResearch.WordTrace]
  refine ⟨12793286445756482335386845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34115430522017286227698253 12793286445756482335386845)
  ·
    refine ⟨4797482417158680875770067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12793286445756482335386845 4797482417158680875770067)
    ·
      refine ⟨7196223625738021313655101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4797482417158680875770067 7196223625738021313655101)
      ·
        refine ⟨2698583859651757992620663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7196223625738021313655101 2698583859651757992620663)
        ·
          refine ⟨4047875789477636988930995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2698583859651757992620663 4047875789477636988930995)
          ·
            refine ⟨6071813684216455483396493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4047875789477636988930995 6071813684216455483396493)
            ·
              refine ⟨2276930131581170806273685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6071813684216455483396493 2276930131581170806273685)
              ·
                refine ⟨106731099917867381544079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2276930131581170806273685 106731099917867381544079)
                ·
                  rfl

theorem cell21_1403042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 6].length) (baseStart_1403042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1403042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1403042 prefixEnd_1403042 := by exact prefixLift 1403042
  have htrace : WordTrace (prefixWord ++ tailWord_1403042) baseStart_1403042 baseEnd_1403042 := by
    simpa [prefixWord, tailWord_1403042, baseEnd_1403042] using wordTrace_append hprefix tailTrace_1403042
  have hstable : (prefixWord ++ tailWord_1403042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403042).length < 2 ^ (prefixWord ++ tailWord_1403042).sum := by decide
  have hdescent : baseEnd_1403042 < baseStart_1403042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403115 : List Nat := [1, 1, 1, 1, 2, 5, 1, 4, 5]
def baseStart_1403115 : Nat := 118140960795 + 1403115 * 2 ^ 59
def prefixEnd_1403115 : Nat := 4983230072969 + 3 ^ 40 * 1403115 * 2
def baseEnd_1403115 : Nat := 320209959348170239915421

theorem tailTrace_1403115 : CollatzResearch.WordTrace tailWord_1403115 prefixEnd_1403115 320209959348170239915421 := by
  unfold tailWord_1403115
  simp only [CollatzResearch.WordTrace]
  refine ⟨51175808311761462808954799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34117205541174308539303199 51175808311761462808954799)
  ·
    refine ⟨76763712467642194213432199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51175808311761462808954799 76763712467642194213432199)
    ·
      refine ⟨115145568701463291320148299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76763712467642194213432199 115145568701463291320148299)
      ·
        refine ⟨172718353052194936980222449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115145568701463291320148299 172718353052194936980222449)
        ·
          refine ⟨129538764789146202735166837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172718353052194936980222449 129538764789146202735166837)
          ·
            refine ⟨12144259198982456506421891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129538764789146202735166837 12144259198982456506421891)
            ·
              refine ⟨18216388798473684759632837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12144259198982456506421891 18216388798473684759632837)
              ·
                refine ⟨3415572899713815892431157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18216388798473684759632837 3415572899713815892431157)
                ·
                  refine ⟨320209959348170239915421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3415572899713815892431157 320209959348170239915421)
                  ·
                    rfl

theorem cell21_1403115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 5].length) (baseStart_1403115 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1403115 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1403115 prefixEnd_1403115 := by exact prefixLift 1403115
  have htrace : WordTrace (prefixWord ++ tailWord_1403115) baseStart_1403115 baseEnd_1403115 := by
    simpa [prefixWord, tailWord_1403115, baseEnd_1403115] using wordTrace_append hprefix tailTrace_1403115
  have hstable : (prefixWord ++ tailWord_1403115).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403115).length < 2 ^ (prefixWord ++ tailWord_1403115).sum := by decide
  have hdescent : baseEnd_1403115 < baseStart_1403115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403146 : List Nat := [3, 1, 2, 2, 1, 1, 4, 1, 6]
def baseStart_1403146 : Nat := 118140960795 + 1403146 * 2 ^ 59
def prefixEnd_1403146 : Nat := 4983230072969 + 3 ^ 40 * 1403146 * 2
def baseEnd_1403146 : Nat := 320217033970521074898691

theorem tailTrace_1403146 : CollatzResearch.WordTrace tailWord_1403146 prefixEnd_1403146 320217033970521074898691 := by
  unfold tailWord_1403146
  simp only [CollatzResearch.WordTrace]
  refine ⟨12794234743662288775833323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34117959316432770068888861 12794234743662288775833323)
  ·
    refine ⟨19191352115493433163749985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12794234743662288775833323 19191352115493433163749985)
    ·
      refine ⟨14393514086620074872812489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19191352115493433163749985 14393514086620074872812489)
      ·
        refine ⟨10795135564965056154609367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14393514086620074872812489 10795135564965056154609367)
        ·
          refine ⟨16192703347447584231914051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10795135564965056154609367 16192703347447584231914051)
          ·
            refine ⟨24289055021171376347871077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16192703347447584231914051 24289055021171376347871077)
            ·
              refine ⟨4554197816469633065225827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24289055021171376347871077 4554197816469633065225827)
              ·
                refine ⟨6831296724704449597838741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4554197816469633065225827 6831296724704449597838741)
                ·
                  refine ⟨320217033970521074898691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6831296724704449597838741 320217033970521074898691)
                  ·
                    rfl

theorem cell21_1403146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_1403146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1403146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1403146 prefixEnd_1403146 := by exact prefixLift 1403146
  have htrace : WordTrace (prefixWord ++ tailWord_1403146) baseStart_1403146 baseEnd_1403146 := by
    simpa [prefixWord, tailWord_1403146, baseEnd_1403146] using wordTrace_append hprefix tailTrace_1403146
  have hstable : (prefixWord ++ tailWord_1403146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403146).length < 2 ^ (prefixWord ++ tailWord_1403146).sum := by decide
  have hdescent : baseEnd_1403146 < baseStart_1403146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403163 : List Nat := [1, 1, 1, 1, 1, 1, 10, 1, 4]
def baseStart_1403163 : Nat := 118140960795 + 1403163 * 2 ^ 59
def prefixEnd_1403163 : Nat := 4983230072969 + 3 ^ 40 * 1403163 * 2
def baseEnd_1403163 : Nat := 320220913602132823115323

theorem tailTrace_1403163 : CollatzResearch.WordTrace tailWord_1403163 prefixEnd_1403163 320220913602132823115323 := by
  unfold tailWord_1403163
  simp only [CollatzResearch.WordTrace]
  refine ⟨51177559015587567006702143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34118372677058378004468095 51177559015587567006702143)
  ·
    refine ⟨76766338523381350510053215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51177559015587567006702143 76766338523381350510053215)
    ·
      refine ⟨115149507785072025765079823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76766338523381350510053215 115149507785072025765079823)
      ·
        refine ⟨172724261677608038647619735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115149507785072025765079823 172724261677608038647619735)
        ·
          refine ⟨259086392516412057971429603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172724261677608038647619735 259086392516412057971429603)
          ·
            refine ⟨388629588774618086957144405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259086392516412057971429603 388629588774618086957144405)
            ·
              refine ⟨1138563248363138926632259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 388629588774618086957144405 1138563248363138926632259)
              ·
                refine ⟨1707844872544708389948389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1138563248363138926632259 1707844872544708389948389)
                ·
                  refine ⟨320220913602132823115323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1707844872544708389948389 320220913602132823115323)
                  ·
                    rfl

theorem cell21_1403163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 4].length) (baseStart_1403163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1403163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1403163 prefixEnd_1403163 := by exact prefixLift 1403163
  have htrace : WordTrace (prefixWord ++ tailWord_1403163) baseStart_1403163 baseEnd_1403163 := by
    simpa [prefixWord, tailWord_1403163, baseEnd_1403163] using wordTrace_append hprefix tailTrace_1403163
  have hstable : (prefixWord ++ tailWord_1403163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403163).length < 2 ^ (prefixWord ++ tailWord_1403163).sum := by decide
  have hdescent : baseEnd_1403163 < baseStart_1403163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403242 : List Nat := [3, 1, 3, 3, 1, 2, 2, 3, 3]
def baseStart_1403242 : Nat := 118140960795 + 1403242 * 2 ^ 59
def prefixEnd_1403242 : Nat := 4983230072969 + 3 ^ 40 * 1403242 * 2
def baseEnd_1403242 : Nat := 320238942478446241298495

theorem tailTrace_1403242 : CollatzResearch.WordTrace tailWord_1403242 prefixEnd_1403242 320238942478446241298495 := by
  unfold tailWord_1403242
  simp only [CollatzResearch.WordTrace]
  refine ⟨12795110095575340874706995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34120293588200908999218653 12795110095575340874706995)
  ·
    refine ⟨19192665143363011312060493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12795110095575340874706995 19192665143363011312060493)
    ·
      refine ⟨7197249428761129242022685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19192665143363011312060493 7197249428761129242022685)
      ·
        refine ⟨2698968535785423465758507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7197249428761129242022685 2698968535785423465758507)
        ·
          refine ⟨4048452803678135198637761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2698968535785423465758507 4048452803678135198637761)
          ·
            refine ⟨3036339602758601398978321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4048452803678135198637761 3036339602758601398978321)
            ·
              refine ⟨2277254702068951049233741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3036339602758601398978321 2277254702068951049233741)
              ·
                refine ⟨853970513275856643462653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2277254702068951049233741 853970513275856643462653)
                ·
                  refine ⟨320238942478446241298495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 853970513275856643462653 320238942478446241298495)
                  ·
                    rfl

theorem cell21_1403242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3, 3].length) (baseStart_1403242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1403242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1403242 prefixEnd_1403242 := by exact prefixLift 1403242
  have htrace : WordTrace (prefixWord ++ tailWord_1403242) baseStart_1403242 baseEnd_1403242 := by
    simpa [prefixWord, tailWord_1403242, baseEnd_1403242] using wordTrace_append hprefix tailTrace_1403242
  have hstable : (prefixWord ++ tailWord_1403242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403242).length < 2 ^ (prefixWord ++ tailWord_1403242).sum := by decide
  have hdescent : baseEnd_1403242 < baseStart_1403242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403253 : List Nat := [1, 3, 4, 1, 2, 2, 8]
def baseStart_1403253 : Nat := 118140960795 + 1403253 * 2 ^ 59
def prefixEnd_1403253 : Nat := 4983230072969 + 3 ^ 40 * 1403253 * 2
def baseEnd_1403253 : Nat := 35582383647590296290571

theorem tailTrace_1403253 : CollatzResearch.WordTrace tailWord_1403253 prefixEnd_1403253 35582383647590296290571 := by
  unfold tailWord_1403253
  simp only [CollatzResearch.WordTrace]
  refine ⟨51180841585261512377478413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34120561056841008251652275 51180841585261512377478413)
  ·
    refine ⟨19192815594473067141554405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51180841585261512377478413 19192815594473067141554405)
    ·
      refine ⟨3598652923963700089041451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19192815594473067141554405 3598652923963700089041451)
      ·
        refine ⟨5397979385945550133562177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3598652923963700089041451 5397979385945550133562177)
        ·
          refine ⟨4048484539459162600171633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5397979385945550133562177 4048484539459162600171633)
          ·
            refine ⟨3036363404594371950128725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4048484539459162600171633 3036363404594371950128725)
            ·
              refine ⟨35582383647590296290571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3036363404594371950128725 35582383647590296290571)
              ·
                rfl

theorem cell21_1403253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 8].length) (baseStart_1403253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1403253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1403253 prefixEnd_1403253 := by exact prefixLift 1403253
  have htrace : WordTrace (prefixWord ++ tailWord_1403253) baseStart_1403253 baseEnd_1403253 := by
    simpa [prefixWord, tailWord_1403253, baseEnd_1403253] using wordTrace_append hprefix tailTrace_1403253
  have hstable : (prefixWord ++ tailWord_1403253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403253).length < 2 ^ (prefixWord ++ tailWord_1403253).sum := by decide
  have hdescent : baseEnd_1403253 < baseStart_1403253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403281 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 10]
def baseStart_1403281 : Nat := 118140960795 + 1403281 * 2 ^ 59
def prefixEnd_1403281 : Nat := 4983230072969 + 3 ^ 40 * 1403281 * 2
def baseEnd_1403281 : Nat := 320247842809790840148415

theorem tailTrace_1403281 : CollatzResearch.WordTrace tailWord_1403281 prefixEnd_1403281 320247842809790840148415 := by
  unfold tailWord_1403281
  simp only [CollatzResearch.WordTrace]
  refine ⟨51181862829160073159497697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34121241886106715439665131 51181862829160073159497697)
  ·
    refine ⟨38386397121870054869623273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51181862829160073159497697 38386397121870054869623273)
    ·
      refine ⟨28789797841402541152217455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38386397121870054869623273 28789797841402541152217455)
      ·
        refine ⟨43184696762103811728326183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28789797841402541152217455 43184696762103811728326183)
        ·
          refine ⟨64777045143155717592489275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43184696762103811728326183 64777045143155717592489275)
          ·
            refine ⟨97165567714733576388733913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64777045143155717592489275 97165567714733576388733913)
            ·
              refine ⟨72874175786050182291550435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97165567714733576388733913 72874175786050182291550435)
              ·
                refine ⟨109311263679075273437325653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72874175786050182291550435 109311263679075273437325653)
                ·
                  refine ⟨320247842809790840148415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 109311263679075273437325653 320247842809790840148415)
                  ·
                    rfl

theorem cell21_1403281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 10].length) (baseStart_1403281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1403281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1403281 prefixEnd_1403281 := by exact prefixLift 1403281
  have htrace : WordTrace (prefixWord ++ tailWord_1403281) baseStart_1403281 baseEnd_1403281 := by
    simpa [prefixWord, tailWord_1403281, baseEnd_1403281] using wordTrace_append hprefix tailTrace_1403281
  have hstable : (prefixWord ++ tailWord_1403281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403281).length < 2 ^ (prefixWord ++ tailWord_1403281).sum := by decide
  have hdescent : baseEnd_1403281 < baseStart_1403281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403298 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 8]
def baseStart_1403298 : Nat := 118140960795 + 1403298 * 2 ^ 59
def prefixEnd_1403298 : Nat := 4983230072969 + 3 ^ 40 * 1403298 * 2
def baseEnd_1403298 : Nat := 320251722441402588365047

theorem tailTrace_1403298 : CollatzResearch.WordTrace tailWord_1403298 prefixEnd_1403298 320251722441402588365047 := by
  unfold tailWord_1403298
  simp only [CollatzResearch.WordTrace]
  refine ⟨12795620717524621265716637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34121655246732323375244365 12795620717524621265716637)
  ·
    refine ⟨4798357769071732974643739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12795620717524621265716637 4798357769071732974643739)
    ·
      refine ⟨7197536653607599461965609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4798357769071732974643739 7197536653607599461965609)
      ·
        refine ⟨5398152490205699596474207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7197536653607599461965609 5398152490205699596474207)
        ·
          refine ⟨8097228735308549394711311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5398152490205699596474207 8097228735308549394711311)
          ·
            refine ⟨12145843102962824092066967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8097228735308549394711311 12145843102962824092066967)
            ·
              refine ⟨18218764654444236138100451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12145843102962824092066967 18218764654444236138100451)
              ·
                refine ⟨27328146981666354207150677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18218764654444236138100451 27328146981666354207150677)
                ·
                  refine ⟨320251722441402588365047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27328146981666354207150677 320251722441402588365047)
                  ·
                    rfl

theorem cell21_1403298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_1403298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1403298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1403298 prefixEnd_1403298 := by exact prefixLift 1403298
  have htrace : WordTrace (prefixWord ++ tailWord_1403298) baseStart_1403298 baseEnd_1403298 := by
    simpa [prefixWord, tailWord_1403298, baseEnd_1403298] using wordTrace_append hprefix tailTrace_1403298
  have hstable : (prefixWord ++ tailWord_1403298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403298).length < 2 ^ (prefixWord ++ tailWord_1403298).sum := by decide
  have hdescent : baseEnd_1403298 < baseStart_1403298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403332 : List Nat := [2, 3, 3, 2, 2, 1, 1, 3, 4]
def baseStart_1403332 : Nat := 118140960795 + 1403332 * 2 ^ 59
def prefixEnd_1403332 : Nat := 4983230072969 + 3 ^ 40 * 1403332 * 2
def baseEnd_1403332 : Nat := 320259481704626084798311

theorem tailTrace_1403332 : CollatzResearch.WordTrace tailWord_1403332 prefixEnd_1403332 320259481704626084798311 := by
  unfold tailWord_1403332
  simp only [CollatzResearch.WordTrace]
  refine ⟨25591861475987654434802125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34122481967983539246402833 25591861475987654434802125)
  ·
    refine ⟨9596948053495370413050797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25591861475987654434802125 9596948053495370413050797)
    ·
      refine ⟨3598855520060763904894049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9596948053495370413050797 3598855520060763904894049)
      ·
        refine ⟨2699141640045572928670537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3598855520060763904894049 2699141640045572928670537)
        ·
          refine ⟨2024356230034179696502903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2699141640045572928670537 2024356230034179696502903)
          ·
            refine ⟨3036534345051269544754355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2024356230034179696502903 3036534345051269544754355)
            ·
              refine ⟨4554801517576904317131533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3036534345051269544754355 4554801517576904317131533)
              ·
                refine ⟨1708050569091339118924325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4554801517576904317131533 1708050569091339118924325)
                ·
                  refine ⟨320259481704626084798311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1708050569091339118924325 320259481704626084798311)
                  ·
                    rfl

theorem cell21_1403332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_1403332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1403332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1403332 prefixEnd_1403332 := by exact prefixLift 1403332
  have htrace : WordTrace (prefixWord ++ tailWord_1403332) baseStart_1403332 baseEnd_1403332 := by
    simpa [prefixWord, tailWord_1403332, baseEnd_1403332] using wordTrace_append hprefix tailTrace_1403332
  have hstable : (prefixWord ++ tailWord_1403332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403332).length < 2 ^ (prefixWord ++ tailWord_1403332).sum := by decide
  have hdescent : baseEnd_1403332 < baseStart_1403332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403360 : List Nat := [2, 1, 1, 3, 1, 1, 4, 5, 3]
def baseStart_1403360 : Nat := 118140960795 + 1403360 * 2 ^ 59
def prefixEnd_1403360 : Nat := 4983230072969 + 3 ^ 40 * 1403360 * 2
def baseEnd_1403360 : Nat := 320265871686104258331587

theorem tailTrace_1403360 : CollatzResearch.WordTrace tailWord_1403360 prefixEnd_1403360 320265871686104258331587 := by
  unfold tailWord_1403360
  simp only [CollatzResearch.WordTrace]
  refine ⟨25592372097936934825811767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34123162797249246434415689 25592372097936934825811767)
  ·
    refine ⟨38388558146905402238717651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25592372097936934825811767 38388558146905402238717651)
    ·
      refine ⟨57582837220358103358076477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38388558146905402238717651 57582837220358103358076477)
      ·
        refine ⟨21593563957634288759278679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57582837220358103358076477 21593563957634288759278679)
        ·
          refine ⟨32390345936451433138918019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21593563957634288759278679 32390345936451433138918019)
          ·
            refine ⟨48585518904677149708377029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32390345936451433138918019 48585518904677149708377029)
            ·
              refine ⟨9109784794626965570320693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48585518904677149708377029 9109784794626965570320693)
              ·
                refine ⟨854042324496278022217565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9109784794626965570320693 854042324496278022217565)
                ·
                  refine ⟨320265871686104258331587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 854042324496278022217565 320265871686104258331587)
                  ·
                    rfl

theorem cell21_1403360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 3].length) (baseStart_1403360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1403360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1403360 prefixEnd_1403360 := by exact prefixLift 1403360
  have htrace : WordTrace (prefixWord ++ tailWord_1403360) baseStart_1403360 baseEnd_1403360 := by
    simpa [prefixWord, tailWord_1403360, baseEnd_1403360] using wordTrace_append hprefix tailTrace_1403360
  have hstable : (prefixWord ++ tailWord_1403360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403360).length < 2 ^ (prefixWord ++ tailWord_1403360).sum := by decide
  have hdescent : baseEnd_1403360 < baseStart_1403360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403546 : List Nat := [3, 1, 1, 6, 1, 1, 1, 4, 3]
def baseStart_1403546 : Nat := 118140960795 + 1403546 * 2 ^ 59
def prefixEnd_1403546 : Nat := 4983230072969 + 3 ^ 40 * 1403546 * 2
def baseEnd_1403546 : Nat := 320308319420209268231207

theorem tailTrace_1403546 : CollatzResearch.WordTrace tailWord_1403546 prefixEnd_1403546 320308319420209268231207 := by
  unfold tailWord_1403546
  simp only [CollatzResearch.WordTrace]
  refine ⟨12797882043300005854473623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34127685448800015611929661 12797882043300005854473623)
  ·
    refine ⟨19196823064950008781710435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12797882043300005854473623 19196823064950008781710435)
    ·
      refine ⟨28795234597425013172565653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19196823064950008781710435 28795234597425013172565653)
      ·
        refine ⟨1349776621754297492464015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28795234597425013172565653 1349776621754297492464015)
        ·
          refine ⟨2024664932631446238696023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1349776621754297492464015 2024664932631446238696023)
          ·
            refine ⟨3036997398947169358044035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2024664932631446238696023 3036997398947169358044035)
            ·
              refine ⟨4555496098420754037066053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3036997398947169358044035 4555496098420754037066053)
              ·
                refine ⟨854155518453891381949885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4555496098420754037066053 854155518453891381949885)
                ·
                  refine ⟨320308319420209268231207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 854155518453891381949885 320308319420209268231207)
                  ·
                    rfl

theorem cell21_1403546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4, 3].length) (baseStart_1403546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1403546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1403546 prefixEnd_1403546 := by exact prefixLift 1403546
  have htrace : WordTrace (prefixWord ++ tailWord_1403546) baseStart_1403546 baseEnd_1403546 := by
    simpa [prefixWord, tailWord_1403546, baseEnd_1403546] using wordTrace_append hprefix tailTrace_1403546
  have hstable : (prefixWord ++ tailWord_1403546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403546).length < 2 ^ (prefixWord ++ tailWord_1403546).sum := by decide
  have hdescent : baseEnd_1403546 < baseStart_1403546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403571 : List Nat := [1, 1, 1, 2, 3, 5, 1, 2, 5]
def baseStart_1403571 : Nat := 118140960795 + 1403571 * 2 ^ 59
def prefixEnd_1403571 : Nat := 4983230072969 + 3 ^ 40 * 1403571 * 2
def baseEnd_1403571 : Nat := 320314024760814780314489

theorem tailTrace_1403571 : CollatzResearch.WordTrace tailWord_1403571 prefixEnd_1403571 320314024760814780314489 := by
  unfold tailWord_1403571
  simp only [CollatzResearch.WordTrace]
  refine ⟨51192439998109452687554567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34128293332072968458369711 51192439998109452687554567)
  ·
    refine ⟨76788659997164179031331851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51192439998109452687554567 76788659997164179031331851)
    ·
      refine ⟨115182989995746268546997777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76788659997164179031331851 115182989995746268546997777)
      ·
        refine ⟨86387242496809701410248333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115182989995746268546997777 86387242496809701410248333)
        ·
          refine ⟨32395215936303638028843125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86387242496809701410248333 32395215936303638028843125)
          ·
            refine ⟨3037051494028466065204043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32395215936303638028843125 3037051494028466065204043)
            ·
              refine ⟨4555577241042699097806065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3037051494028466065204043 4555577241042699097806065)
              ·
                refine ⟨3416682930782024323354549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4555577241042699097806065 3416682930782024323354549)
                ·
                  refine ⟨320314024760814780314489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3416682930782024323354549 320314024760814780314489)
                  ·
                    rfl

theorem cell21_1403571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 5].length) (baseStart_1403571 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1403571 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1403571 prefixEnd_1403571 := by exact prefixLift 1403571
  have htrace : WordTrace (prefixWord ++ tailWord_1403571) baseStart_1403571 baseEnd_1403571 := by
    simpa [prefixWord, tailWord_1403571, baseEnd_1403571] using wordTrace_append hprefix tailTrace_1403571
  have hstable : (prefixWord ++ tailWord_1403571).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403571).length < 2 ^ (prefixWord ++ tailWord_1403571).sum := by decide
  have hdescent : baseEnd_1403571 < baseStart_1403571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403605 : List Nat := [1, 3, 2, 5, 1, 1, 2, 1, 5]
def baseStart_1403605 : Nat := 118140960795 + 1403605 * 2 ^ 59
def prefixEnd_1403605 : Nat := 4983230072969 + 3 ^ 40 * 1403605 * 2
def baseEnd_1403605 : Nat := 320321784024038276747753

theorem tailTrace_1403605 : CollatzResearch.WordTrace tailWord_1403605 prefixEnd_1403605 320321784024038276747753 := by
  unfold tailWord_1403605
  simp only [CollatzResearch.WordTrace]
  refine ⟨51193680079986276494292269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34129120053324184329528179 51193680079986276494292269)
  ·
    refine ⟨19197630029994853685359601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51193680079986276494292269 19197630029994853685359601)
    ·
      refine ⟨14398222522496140264019701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19197630029994853685359601 14398222522496140264019701)
      ·
        refine ⟨1349833361484013149751847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14398222522496140264019701 1349833361484013149751847)
        ·
          refine ⟨2024750042226019724627771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1349833361484013149751847 2024750042226019724627771)
          ·
            refine ⟨3037125063339029586941657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2024750042226019724627771 3037125063339029586941657)
            ·
              refine ⟨2277843797504272190206243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3037125063339029586941657 2277843797504272190206243)
              ·
                refine ⟨3416765696256408285309365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2277843797504272190206243 3416765696256408285309365)
                ·
                  refine ⟨320321784024038276747753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3416765696256408285309365 320321784024038276747753)
                  ·
                    rfl

theorem cell21_1403605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_1403605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1403605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1403605 prefixEnd_1403605 := by exact prefixLift 1403605
  have htrace : WordTrace (prefixWord ++ tailWord_1403605) baseStart_1403605 baseEnd_1403605 := by
    simpa [prefixWord, tailWord_1403605, baseEnd_1403605] using wordTrace_append hprefix tailTrace_1403605
  have hstable : (prefixWord ++ tailWord_1403605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403605).length < 2 ^ (prefixWord ++ tailWord_1403605).sum := by decide
  have hdescent : baseEnd_1403605 < baseStart_1403605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403709 : List Nat := [1, 4, 1, 4, 3, 8]
def baseStart_1403709 : Nat := 118140960795 + 1403709 * 2 ^ 59
def prefixEnd_1403709 : Nat := 4983230072969 + 3 ^ 40 * 1403709 * 2
def baseEnd_1403709 : Nat := 11864648823739155815341

theorem tailTrace_1403709 : CollatzResearch.WordTrace tailWord_1403709 prefixEnd_1403709 11864648823739155815341 := by
  unfold tailWord_1403709
  simp only [CollatzResearch.WordTrace]
  refine ⟨51197473271609502256078181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34131648847739668170718787 51197473271609502256078181)
  ·
    refine ⟨9599526238426781673014659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51197473271609502256078181 9599526238426781673014659)
    ·
      refine ⟨14399289357640172509521989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9599526238426781673014659 14399289357640172509521989)
      ·
        refine ⟨2699866754557532345535373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14399289357640172509521989 2699866754557532345535373)
        ·
          refine ⟨1012450032959074629575765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2699866754557532345535373 1012450032959074629575765)
          ·
            refine ⟨11864648823739155815341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1012450032959074629575765 11864648823739155815341)
            ·
              rfl

theorem cell21_1403709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 8].length) (baseStart_1403709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1403709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1403709 prefixEnd_1403709 := by exact prefixLift 1403709
  have htrace : WordTrace (prefixWord ++ tailWord_1403709) baseStart_1403709 baseEnd_1403709 := by
    simpa [prefixWord, tailWord_1403709, baseEnd_1403709] using wordTrace_append hprefix tailTrace_1403709
  have hstable : (prefixWord ++ tailWord_1403709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403709).length < 2 ^ (prefixWord ++ tailWord_1403709).sum := by decide
  have hdescent : baseEnd_1403709 < baseStart_1403709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403740 : List Nat := [2, 2, 4, 2, 1, 2, 1, 2, 5]
def baseStart_1403740 : Nat := 118140960795 + 1403740 * 2 ^ 59
def prefixEnd_1403740 : Nat := 4983230072969 + 3 ^ 40 * 1403740 * 2
def baseEnd_1403740 : Nat := 320352592863308041997477

theorem tailTrace_1403740 : CollatzResearch.WordTrace tailWord_1403740 prefixEnd_1403740 320352592863308041997477 := by
  unfold tailWord_1403740
  simp only [CollatzResearch.WordTrace]
  refine ⟨25599301967248597275228337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34132402622998129700304449 25599301967248597275228337)
  ·
    refine ⟨19199476475436447956421253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25599301967248597275228337 19199476475436447956421253)
    ·
      refine ⟨3599901839144333991828985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19199476475436447956421253 3599901839144333991828985)
      ·
        refine ⟨2699926379358250493871739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3599901839144333991828985 2699926379358250493871739)
        ·
          refine ⟨4049889569037375740807609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2699926379358250493871739 4049889569037375740807609)
          ·
            refine ⟨3037417176778031805605707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4049889569037375740807609 3037417176778031805605707)
            ·
              refine ⟨4556125765167047708408561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3037417176778031805605707 4556125765167047708408561)
              ·
                refine ⟨3417094323875285781306421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4556125765167047708408561 3417094323875285781306421)
                ·
                  refine ⟨320352592863308041997477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3417094323875285781306421 320352592863308041997477)
                  ·
                    rfl

theorem cell21_1403740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_1403740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1403740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1403740 prefixEnd_1403740 := by exact prefixLift 1403740
  have htrace : WordTrace (prefixWord ++ tailWord_1403740) baseStart_1403740 baseEnd_1403740 := by
    simpa [prefixWord, tailWord_1403740, baseEnd_1403740] using wordTrace_append hprefix tailTrace_1403740
  have hstable : (prefixWord ++ tailWord_1403740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403740).length < 2 ^ (prefixWord ++ tailWord_1403740).sum := by decide
  have hdescent : baseEnd_1403740 < baseStart_1403740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403802 : List Nat := [3, 1, 1, 4, 3, 2, 2, 5]
def baseStart_1403802 : Nat := 118140960795 + 1403802 * 2 ^ 59
def prefixEnd_1403802 : Nat := 4983230072969 + 3 ^ 40 * 1403802 * 2
def baseEnd_1403802 : Nat := 106788914036003237321339

theorem tailTrace_1403802 : CollatzResearch.WordTrace tailWord_1403802 prefixEnd_1403802 106788914036003237321339 := by
  unfold tailWord_1403802
  simp only [CollatzResearch.WordTrace]
  refine ⟨12800216315068144784803415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34133910173515052759475773 12800216315068144784803415)
  ·
    refine ⟨19200324472602217177205123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12800216315068144784803415 19200324472602217177205123)
    ·
      refine ⟨28800486708903325765807685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19200324472602217177205123 28800486708903325765807685)
      ·
        refine ⟨5400091257919373581088941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28800486708903325765807685 5400091257919373581088941)
        ·
          refine ⟨2025034221719765092908353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5400091257919373581088941 2025034221719765092908353)
          ·
            refine ⟨1518775666289823819681265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2025034221719765092908353 1518775666289823819681265)
            ·
              refine ⟨1139081749717367864760949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1518775666289823819681265 1139081749717367864760949)
              ·
                refine ⟨106788914036003237321339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1139081749717367864760949 106788914036003237321339)
                ·
                  rfl

theorem cell21_1403802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 5].length) (baseStart_1403802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1403802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1403802 prefixEnd_1403802 := by exact prefixLift 1403802
  have htrace : WordTrace (prefixWord ++ tailWord_1403802) baseStart_1403802 baseEnd_1403802 := by
    simpa [prefixWord, tailWord_1403802, baseEnd_1403802] using wordTrace_append hprefix tailTrace_1403802
  have hstable : (prefixWord ++ tailWord_1403802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403802).length < 2 ^ (prefixWord ++ tailWord_1403802).sum := by decide
  have hdescent : baseEnd_1403802 < baseStart_1403802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403833 : List Nat := [1, 2, 1, 4, 2, 3, 3, 2, 3]
def baseStart_1403833 : Nat := 118140960795 + 1403833 * 2 ^ 59
def prefixEnd_1403833 : Nat := 4983230072969 + 3 ^ 40 * 1403833 * 2
def baseEnd_1403833 : Nat := 320373816730360546947287

theorem tailTrace_1403833 : CollatzResearch.WordTrace tailWord_1403833 prefixEnd_1403833 320373816730360546947287 := by
  unfold tailWord_1403833
  simp only [CollatzResearch.WordTrace]
  refine ⟨51201995923160271433592153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34134663948773514289061435 51201995923160271433592153)
  ·
    refine ⟨38401496942370203575194115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51201995923160271433592153 38401496942370203575194115)
    ·
      refine ⟨57602245413555305362791173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38401496942370203575194115 57602245413555305362791173)
      ·
        refine ⟨10800421015041619755523345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57602245413555305362791173 10800421015041619755523345)
        ·
          refine ⟨8100315761281214816642509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10800421015041619755523345 8100315761281214816642509)
          ·
            refine ⟨3037618410480455556240941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8100315761281214816642509 3037618410480455556240941)
            ·
              refine ⟨1139106903930170833590353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3037618410480455556240941 1139106903930170833590353)
              ·
                refine ⟨854330177947628125192765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1139106903930170833590353 854330177947628125192765)
                ·
                  refine ⟨320373816730360546947287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 854330177947628125192765 320373816730360546947287)
                  ·
                    rfl

theorem cell21_1403833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2, 3].length) (baseStart_1403833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1403833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1403833 prefixEnd_1403833 := by exact prefixLift 1403833
  have htrace : WordTrace (prefixWord ++ tailWord_1403833) baseStart_1403833 baseEnd_1403833 := by
    simpa [prefixWord, tailWord_1403833, baseEnd_1403833] using wordTrace_append hprefix tailTrace_1403833
  have hstable : (prefixWord ++ tailWord_1403833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403833).length < 2 ^ (prefixWord ++ tailWord_1403833).sum := by decide
  have hdescent : baseEnd_1403833 < baseStart_1403833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404002 : List Nat := [3, 3, 2, 2, 1, 2, 3, 2, 3]
def baseStart_1404002 : Nat := 118140960795 + 1404002 * 2 ^ 59
def prefixEnd_1404002 : Nat := 4983230072969 + 3 ^ 40 * 1404002 * 2
def baseEnd_1404002 : Nat := 320412384832853808630275

theorem tailTrace_1404002 : CollatzResearch.WordTrace tailWord_1404002 prefixEnd_1404002 320412384832853808630275 := by
  unfold tailWord_1404002
  simp only [CollatzResearch.WordTrace]
  refine ⟨12802039964887003324123565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34138773239698675530996173 12802039964887003324123565)
  ·
    refine ⟨4800764986832626246546337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12802039964887003324123565 4800764986832626246546337)
    ·
      refine ⟨3600573740124469684909753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4800764986832626246546337 3600573740124469684909753)
      ·
        refine ⟨2700430305093352263682315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3600573740124469684909753 2700430305093352263682315)
        ·
          refine ⟨4050645457640028395523473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2700430305093352263682315 4050645457640028395523473)
          ·
            refine ⟨3037984093230021296642605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4050645457640028395523473 3037984093230021296642605)
            ·
              refine ⟨1139244034961257986240977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3037984093230021296642605 1139244034961257986240977)
              ·
                refine ⟨854433026220943489680733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1139244034961257986240977 854433026220943489680733)
                ·
                  refine ⟨320412384832853808630275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 854433026220943489680733 320412384832853808630275)
                  ·
                    rfl

theorem cell21_1404002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_1404002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1404002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1404002 prefixEnd_1404002 := by exact prefixLift 1404002
  have htrace : WordTrace (prefixWord ++ tailWord_1404002) baseStart_1404002 baseEnd_1404002 := by
    simpa [prefixWord, tailWord_1404002, baseEnd_1404002] using wordTrace_append hprefix tailTrace_1404002
  have hstable : (prefixWord ++ tailWord_1404002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404002).length < 2 ^ (prefixWord ++ tailWord_1404002).sum := by decide
  have hdescent : baseEnd_1404002 < baseStart_1404002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404055 : List Nat := [1, 1, 3, 3, 3, 10]
def baseStart_1404055 : Nat := 118140960795 + 1404055 * 2 ^ 59
def prefixEnd_1404055 : Nat := 4983230072969 + 3 ^ 40 * 1404055 * 2
def baseEnd_1404055 : Nat := 11867573339071759046179

theorem tailTrace_1404055 : CollatzResearch.WordTrace tailWord_1404055 prefixEnd_1404055 11867573339071759046179 := by
  unfold tailWord_1404055
  simp only [CollatzResearch.WordTrace]
  refine ⟨51210092928356003348173619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34140061952237335565449079 51210092928356003348173619)
  ·
    refine ⟨76815139392534005022260429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51210092928356003348173619 76815139392534005022260429)
    ·
      refine ⟨28805677272200251883347661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76815139392534005022260429 28805677272200251883347661)
      ·
        refine ⟨10802128977075094456255373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28805677272200251883347661 10802128977075094456255373)
        ·
          refine ⟨4050798366403160421095765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10802128977075094456255373 4050798366403160421095765)
          ·
            refine ⟨11867573339071759046179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4050798366403160421095765 11867573339071759046179)
            ·
              rfl

theorem cell21_1404055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 10].length) (baseStart_1404055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1404055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1404055 prefixEnd_1404055 := by exact prefixLift 1404055
  have htrace : WordTrace (prefixWord ++ tailWord_1404055) baseStart_1404055 baseEnd_1404055 := by
    simpa [prefixWord, tailWord_1404055, baseEnd_1404055] using wordTrace_append hprefix tailTrace_1404055
  have hstable : (prefixWord ++ tailWord_1404055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404055).length < 2 ^ (prefixWord ++ tailWord_1404055).sum := by decide
  have hdescent : baseEnd_1404055 < baseStart_1404055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404058 : List Nat := [3, 1, 1, 5, 1, 1, 1, 4, 4]
def baseStart_1404058 : Nat := 118140960795 + 1404058 * 2 ^ 59
def prefixEnd_1404058 : Nat := 4983230072969 + 3 ^ 40 * 1404058 * 2
def baseEnd_1404058 : Nat := 320425164795810155696827

theorem tailTrace_1404058 : CollatzResearch.WordTrace tailWord_1404058 prefixEnd_1404058 320425164795810155696827 := by
  unfold tailWord_1404058
  simp only [CollatzResearch.WordTrace]
  refine ⟨12802550586836283715133207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34140134898230089907021885 12802550586836283715133207)
  ·
    refine ⟨19203825880254425572699811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12802550586836283715133207 19203825880254425572699811)
    ·
      refine ⟨28805738820381638359049717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19203825880254425572699811 28805738820381638359049717)
      ·
        refine ⟨2700538014410778596160911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28805738820381638359049717 2700538014410778596160911)
        ·
          refine ⟨4050807021616167894241367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2700538014410778596160911 4050807021616167894241367)
          ·
            refine ⟨6076210532424251841362051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4050807021616167894241367 6076210532424251841362051)
            ·
              refine ⟨9114315798636377762043077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6076210532424251841362051 9114315798636377762043077)
              ·
                refine ⟨1708934212244320830383077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9114315798636377762043077 1708934212244320830383077)
                ·
                  refine ⟨320425164795810155696827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1708934212244320830383077 320425164795810155696827)
                  ·
                    rfl

theorem cell21_1404058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_1404058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1404058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1404058 prefixEnd_1404058 := by exact prefixLift 1404058
  have htrace : WordTrace (prefixWord ++ tailWord_1404058) baseStart_1404058 baseEnd_1404058 := by
    simpa [prefixWord, tailWord_1404058, baseEnd_1404058] using wordTrace_append hprefix tailTrace_1404058
  have hstable : (prefixWord ++ tailWord_1404058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404058).length < 2 ^ (prefixWord ++ tailWord_1404058).sum := by decide
  have hdescent : baseEnd_1404058 < baseStart_1404058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404109 : List Nat := [1, 6, 2, 2, 1, 2, 1, 2, 4]
def baseStart_1404109 : Nat := 118140960795 + 1404109 * 2 ^ 59
def prefixEnd_1404109 : Nat := 4983230072969 + 3 ^ 40 * 1404109 * 2
def baseEnd_1404109 : Nat := 320436803690645400346723

theorem tailTrace_1404109 : CollatzResearch.WordTrace tailWord_1404109 prefixEnd_1404109 320436803690645400346723 := by
  unfold tailWord_1404109
  simp only [CollatzResearch.WordTrace]
  refine ⟨51212062470160370570639381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34141374980106913713759587 51212062470160370570639381)
  ·
    refine ⟨2400565428288767370498721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51212062470160370570639381 2400565428288767370498721)
    ·
      refine ⟨1800424071216575527874041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2400565428288767370498721 1800424071216575527874041)
      ·
        refine ⟨1350318053412431645905531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1800424071216575527874041 1350318053412431645905531)
        ·
          refine ⟨2025477080118647468858297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1350318053412431645905531 2025477080118647468858297)
          ·
            refine ⟨1519107810088985601643723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2025477080118647468858297 1519107810088985601643723)
            ·
              refine ⟨2278661715133478402465585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1519107810088985601643723 2278661715133478402465585)
              ·
                refine ⟨1708996286350108801849189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2278661715133478402465585 1708996286350108801849189)
                ·
                  refine ⟨320436803690645400346723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1708996286350108801849189 320436803690645400346723)
                  ·
                    rfl

theorem cell21_1404109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_1404109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1404109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1404109 prefixEnd_1404109 := by exact prefixLift 1404109
  have htrace : WordTrace (prefixWord ++ tailWord_1404109) baseStart_1404109 baseEnd_1404109 := by
    simpa [prefixWord, tailWord_1404109, baseEnd_1404109] using wordTrace_append hprefix tailTrace_1404109
  have hstable : (prefixWord ++ tailWord_1404109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404109).length < 2 ^ (prefixWord ++ tailWord_1404109).sum := by decide
  have hdescent : baseEnd_1404109 < baseStart_1404109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404238 : List Nat := [4, 1, 1, 1, 1, 1, 4, 3, 5]
def baseStart_1404238 : Nat := 118140960795 + 1404238 * 2 ^ 59
def prefixEnd_1404238 : Nat := 4983230072969 + 3 ^ 40 * 1404238 * 2
def baseEnd_1404238 : Nat := 320466243248169842696459

theorem tailTrace_1404238 : CollatzResearch.WordTrace tailWord_1404238 prefixEnd_1404238 320466243248169842696459 := by
  unfold tailWord_1404238
  simp only [CollatzResearch.WordTrace]
  refine ⟨6402095935836628200260671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34144511657795350401390245 6402095935836628200260671)
  ·
    refine ⟨9603143903754942300391007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6402095935836628200260671 9603143903754942300391007)
    ·
      refine ⟨14404715855632413450586511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9603143903754942300391007 14404715855632413450586511)
      ·
        refine ⟨21607073783448620175879767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14404715855632413450586511 21607073783448620175879767)
        ·
          refine ⟨32410610675172930263819651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21607073783448620175879767 32410610675172930263819651)
          ·
            refine ⟨48615916012759395395729477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32410610675172930263819651 48615916012759395395729477)
            ·
              refine ⟨9115484252392386636699277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48615916012759395395729477 9115484252392386636699277)
              ·
                refine ⟨3418306594647144988762229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9115484252392386636699277 3418306594647144988762229)
                ·
                  refine ⟨320466243248169842696459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3418306594647144988762229 320466243248169842696459)
                  ·
                    rfl

theorem cell21_1404238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_1404238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1404238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1404238 prefixEnd_1404238 := by exact prefixLift 1404238
  have htrace : WordTrace (prefixWord ++ tailWord_1404238) baseStart_1404238 baseEnd_1404238 := by
    simpa [prefixWord, tailWord_1404238, baseEnd_1404238] using wordTrace_append hprefix tailTrace_1404238
  have hstable : (prefixWord ++ tailWord_1404238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404238).length < 2 ^ (prefixWord ++ tailWord_1404238).sum := by decide
  have hdescent : baseEnd_1404238 < baseStart_1404238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404314 : List Nat := [3, 1, 1, 4, 1, 1, 1, 4, 5]
def baseStart_1404314 : Nat := 118140960795 + 1404314 * 2 ^ 59
def prefixEnd_1404314 : Nat := 4983230072969 + 3 ^ 40 * 1404314 * 2
def baseEnd_1404314 : Nat := 320483587483610599429637

theorem tailTrace_1404314 : CollatzResearch.WordTrace tailWord_1404314 prefixEnd_1404314 320483587483610599429637 := by
  unfold tailWord_1404314
  simp only [CollatzResearch.WordTrace]
  refine ⟨12804884858604422645462999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34146359622945127054567997 12804884858604422645462999)
  ·
    refine ⟨19207327287906633968194499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12804884858604422645462999 19207327287906633968194499)
    ·
      refine ⟨28810990931859950952291749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19207327287906633968194499 28810990931859950952291749)
      ·
        refine ⟨5402060799723740803554703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28810990931859950952291749 5402060799723740803554703)
        ·
          refine ⟨8103091199585611205332055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5402060799723740803554703 8103091199585611205332055)
          ·
            refine ⟨12154636799378416807998083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8103091199585611205332055 12154636799378416807998083)
            ·
              refine ⟨18231955199067625211997125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12154636799378416807998083 18231955199067625211997125)
              ·
                refine ⟨3418491599825179727249461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18231955199067625211997125 3418491599825179727249461)
                ·
                  refine ⟨320483587483610599429637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3418491599825179727249461 320483587483610599429637)
                  ·
                    rfl

theorem cell21_1404314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_1404314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1404314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1404314 prefixEnd_1404314 := by exact prefixLift 1404314
  have htrace : WordTrace (prefixWord ++ tailWord_1404314) baseStart_1404314 baseEnd_1404314 := by
    simpa [prefixWord, tailWord_1404314, baseEnd_1404314] using wordTrace_append hprefix tailTrace_1404314
  have hstable : (prefixWord ++ tailWord_1404314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404314).length < 2 ^ (prefixWord ++ tailWord_1404314).sum := by decide
  have hdescent : baseEnd_1404314 < baseStart_1404314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404317 : List Nat := [1, 4, 2, 1, 3, 3, 2, 5]
def baseStart_1404317 : Nat := 118140960795 + 1404317 * 2 ^ 59
def prefixEnd_1404317 : Nat := 4983230072969 + 3 ^ 40 * 1404317 * 2
def baseEnd_1404317 : Nat := 106828090708161086959877

theorem tailTrace_1404317 : CollatzResearch.WordTrace tailWord_1404317 prefixEnd_1404317 106828090708161086959877 := by
  unfold tailWord_1404317
  simp only [CollatzResearch.WordTrace]
  refine ⟨51219648853406822094211205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34146432568937881396140803 51219648853406822094211205)
  ·
    refine ⟨9603684160013779142664601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51219648853406822094211205 9603684160013779142664601)
    ·
      refine ⟨7202763120010334356998451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9603684160013779142664601 7202763120010334356998451)
      ·
        refine ⟨10804144680015501535497677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7202763120010334356998451 10804144680015501535497677)
        ·
          refine ⟨4051554255005813075811629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10804144680015501535497677 4051554255005813075811629)
          ·
            refine ⟨1519332845627179903429361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4051554255005813075811629 1519332845627179903429361)
            ·
              refine ⟨1139499634220384927572021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1519332845627179903429361 1139499634220384927572021)
              ·
                refine ⟨106828090708161086959877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1139499634220384927572021 106828090708161086959877)
                ·
                  rfl

theorem cell21_1404317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 5].length) (baseStart_1404317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1404317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1404317 prefixEnd_1404317 := by exact prefixLift 1404317
  have htrace : WordTrace (prefixWord ++ tailWord_1404317) baseStart_1404317 baseEnd_1404317 := by
    simpa [prefixWord, tailWord_1404317, baseEnd_1404317] using wordTrace_append hprefix tailTrace_1404317
  have hstable : (prefixWord ++ tailWord_1404317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404317).length < 2 ^ (prefixWord ++ tailWord_1404317).sum := by decide
  have hdescent : baseEnd_1404317 < baseStart_1404317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404348 : List Nat := [2, 2, 2, 4, 2, 2, 1, 1, 5]
def baseStart_1404348 : Nat := 118140960795 + 1404348 * 2 ^ 59
def prefixEnd_1404348 : Nat := 4983230072969 + 3 ^ 40 * 1404348 * 2
def baseEnd_1404348 : Nat := 320491346746834095862901

theorem tailTrace_1404348 : CollatzResearch.WordTrace tailWord_1404348 prefixEnd_1404348 320491346746834095862901 := by
  unfold tailWord_1404348
  simp only [CollatzResearch.WordTrace]
  refine ⟨25610389758147257194294849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34147186344196342925726465 25610389758147257194294849)
  ·
    refine ⟨19207792318610442895721137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25610389758147257194294849 19207792318610442895721137)
    ·
      refine ⟨14405844238957832171790853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19207792318610442895721137 14405844238957832171790853)
      ·
        refine ⟨2701095794804593532210785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14405844238957832171790853 2701095794804593532210785)
        ·
          refine ⟨2025821846103445149158089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2701095794804593532210785 2025821846103445149158089)
          ·
            refine ⟨1519366384577583861868567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2025821846103445149158089 1519366384577583861868567)
            ·
              refine ⟨2279049576866375792802851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1519366384577583861868567 2279049576866375792802851)
              ·
                refine ⟨3418574365299563689204277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2279049576866375792802851 3418574365299563689204277)
                ·
                  refine ⟨320491346746834095862901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3418574365299563689204277 320491346746834095862901)
                  ·
                    rfl

theorem cell21_1404348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_1404348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1404348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1404348 prefixEnd_1404348 := by exact prefixLift 1404348
  have htrace : WordTrace (prefixWord ++ tailWord_1404348) baseStart_1404348 baseEnd_1404348 := by
    simpa [prefixWord, tailWord_1404348, baseEnd_1404348] using wordTrace_append hprefix tailTrace_1404348
  have hstable : (prefixWord ++ tailWord_1404348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404348).length < 2 ^ (prefixWord ++ tailWord_1404348).sum := by decide
  have hdescent : baseEnd_1404348 < baseStart_1404348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404359 : List Nat := [1, 1, 4, 1, 1, 3, 4, 6]
def baseStart_1404359 : Nat := 118140960795 + 1404359 * 2 ^ 59
def prefixEnd_1404359 : Nat := 4983230072969 + 3 ^ 40 * 1404359 * 2
def baseEnd_1404359 : Nat := 106831285698900173726515

theorem tailTrace_1404359 : CollatzResearch.WordTrace tailWord_1404359 prefixEnd_1404359 106831285698900173726515 := by
  unfold tailWord_1404359
  simp only [CollatzResearch.WordTrace]
  refine ⟨51221180719254663267240131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34147453812836442178160087 51221180719254663267240131)
  ·
    refine ⟨76831771078881994900860197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51221180719254663267240131 76831771078881994900860197)
    ·
      refine ⟨14405957077290374043911287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76831771078881994900860197 14405957077290374043911287)
      ·
        refine ⟨21608935615935561065866931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14405957077290374043911287 21608935615935561065866931)
        ·
          refine ⟨32413403423903341598800397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21608935615935561065866931 32413403423903341598800397)
          ·
            refine ⟨12155026283963753099550149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32413403423903341598800397 12155026283963753099550149)
            ·
              refine ⟨2279067428243203706165653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12155026283963753099550149 2279067428243203706165653)
              ·
                refine ⟨106831285698900173726515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2279067428243203706165653 106831285698900173726515)
                ·
                  rfl

theorem cell21_1404359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 6].length) (baseStart_1404359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1404359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1404359 prefixEnd_1404359 := by exact prefixLift 1404359
  have htrace : WordTrace (prefixWord ++ tailWord_1404359) baseStart_1404359 baseEnd_1404359 := by
    simpa [prefixWord, tailWord_1404359, baseEnd_1404359] using wordTrace_append hprefix tailTrace_1404359
  have hstable : (prefixWord ++ tailWord_1404359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404359).length < 2 ^ (prefixWord ++ tailWord_1404359).sum := by decide
  have hdescent : baseEnd_1404359 < baseStart_1404359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404362 : List Nat := [3, 1, 2, 1, 2, 3, 4, 1, 4]
def baseStart_1404362 : Nat := 118140960795 + 1404362 * 2 ^ 59
def prefixEnd_1404362 : Nat := 4983230072969 + 3 ^ 40 * 1404362 * 2
def baseEnd_1404362 : Nat := 320494541737573182629539

theorem tailTrace_1404362 : CollatzResearch.WordTrace tailWord_1404362 prefixEnd_1404362 320494541737573182629539 := by
  unfold tailWord_1404362
  simp only [CollatzResearch.WordTrace]
  refine ⟨12805322534560948694899835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34147526758829196519732893 12805322534560948694899835)
  ·
    refine ⟨19207983801841423042349753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12805322534560948694899835 19207983801841423042349753)
    ·
      refine ⟨14405987851381067281762315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19207983801841423042349753 14405987851381067281762315)
      ·
        refine ⟨21608981777071600922643473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14405987851381067281762315 21608981777071600922643473)
        ·
          refine ⟨16206736332803700691982605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21608981777071600922643473 16206736332803700691982605)
          ·
            refine ⟨6077526124801387759493477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16206736332803700691982605 6077526124801387759493477)
            ·
              refine ⟨1139536148400260204905027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6077526124801387759493477 1139536148400260204905027)
              ·
                refine ⟨1709304222600390307357541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1139536148400260204905027 1709304222600390307357541)
                ·
                  refine ⟨320494541737573182629539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1709304222600390307357541 320494541737573182629539)
                  ·
                    rfl

theorem cell21_1404362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_1404362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1404362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1404362 prefixEnd_1404362 := by exact prefixLift 1404362
  have htrace : WordTrace (prefixWord ++ tailWord_1404362) baseStart_1404362 baseEnd_1404362 := by
    simpa [prefixWord, tailWord_1404362, baseEnd_1404362] using wordTrace_append hprefix tailTrace_1404362
  have hstable : (prefixWord ++ tailWord_1404362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404362).length < 2 ^ (prefixWord ++ tailWord_1404362).sum := by decide
  have hdescent : baseEnd_1404362 < baseStart_1404362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404570 : List Nat := [3, 1, 1, 16]
def baseStart_1404570 : Nat := 118140960795 + 1404570 * 2 ^ 59
def prefixEnd_1404570 : Nat := 4983230072969 + 3 ^ 40 * 1404570 * 2
def baseEnd_1404570 : Nat := 1319102922516094827829

theorem tailTrace_1404570 : CollatzResearch.WordTrace tailWord_1404570 prefixEnd_1404570 1319102922516094827829 := by
  unfold tailWord_1404570
  simp only [CollatzResearch.WordTrace]
  refine ⟨12807219130372561575792791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34152584347660164202114109 12807219130372561575792791)
  ·
    refine ⟨19210828695558842363689187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12807219130372561575792791 19210828695558842363689187)
    ·
      refine ⟨28816243043338263545533781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19210828695558842363689187 28816243043338263545533781)
      ·
        refine ⟨1319102922516094827829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 28816243043338263545533781 1319102922516094827829)
        ·
          rfl

theorem cell21_1404570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 16].length) (baseStart_1404570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1404570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1404570 prefixEnd_1404570 := by exact prefixLift 1404570
  have htrace : WordTrace (prefixWord ++ tailWord_1404570) baseStart_1404570 baseEnd_1404570 := by
    simpa [prefixWord, tailWord_1404570, baseEnd_1404570] using wordTrace_append hprefix tailTrace_1404570
  have hstable : (prefixWord ++ tailWord_1404570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404570).length < 2 ^ (prefixWord ++ tailWord_1404570).sum := by decide
  have hdescent : baseEnd_1404570 < baseStart_1404570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404576 : List Nat := [2, 1, 1, 4, 3, 1, 4, 2, 3]
def baseStart_1404576 : Nat := 118140960795 + 1404576 * 2 ^ 59
def prefixEnd_1404576 : Nat := 4983230072969 + 3 ^ 40 * 1404576 * 2
def baseEnd_1404576 : Nat := 320543379453156366062435

theorem tailTrace_1404576 : CollatzResearch.WordTrace tailWord_1404576 prefixEnd_1404576 320543379453156366062435 := by
  unfold tailWord_1404576
  simp only [CollatzResearch.WordTrace]
  refine ⟨25614547679734254663944791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34152730239645672885259721 25614547679734254663944791)
  ·
    refine ⟨38421821519601381995917187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25614547679734254663944791 38421821519601381995917187)
    ·
      refine ⟨57632732279402072993875781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38421821519601381995917187 57632732279402072993875781)
      ·
        refine ⟨10806137302387888686351709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57632732279402072993875781 10806137302387888686351709)
        ·
          refine ⟨4052301488395458257381891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10806137302387888686351709 4052301488395458257381891)
          ·
            refine ⟨6078452232593187386072837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4052301488395458257381891 6078452232593187386072837)
            ·
              refine ⟨1139709793611222634888657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6078452232593187386072837 1139709793611222634888657)
              ·
                refine ⟨854782345208416976166493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1139709793611222634888657 854782345208416976166493)
                ·
                  refine ⟨320543379453156366062435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 854782345208416976166493 320543379453156366062435)
                  ·
                    rfl

theorem cell21_1404576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2, 3].length) (baseStart_1404576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1404576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1404576 prefixEnd_1404576 := by exact prefixLift 1404576
  have htrace : WordTrace (prefixWord ++ tailWord_1404576) baseStart_1404576 baseEnd_1404576 := by
    simpa [prefixWord, tailWord_1404576, baseEnd_1404576] using wordTrace_append hprefix tailTrace_1404576
  have hstable : (prefixWord ++ tailWord_1404576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404576).length < 2 ^ (prefixWord ++ tailWord_1404576).sum := by decide
  have hdescent : baseEnd_1404576 < baseStart_1404576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404601 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 7]
def baseStart_1404601 : Nat := 118140960795 + 1404601 * 2 ^ 59
def prefixEnd_1404601 : Nat := 4983230072969 + 3 ^ 40 * 1404601 * 2
def baseEnd_1404601 : Nat := 320549084793761878145717

theorem tailTrace_1404601 : CollatzResearch.WordTrace tailWord_1404601 prefixEnd_1404601 320549084793761878145717 := by
  unfold tailWord_1404601
  simp only [CollatzResearch.WordTrace]
  refine ⟨51230007184377938597549657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34153338122918625731699771 51230007184377938597549657)
  ·
    refine ⟨38422505388283453948162243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51230007184377938597549657 38422505388283453948162243)
    ·
      refine ⟨57633758082425180922243365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38422505388283453948162243 57633758082425180922243365)
      ·
        refine ⟨10806329640454721422920631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57633758082425180922243365 10806329640454721422920631)
        ·
          refine ⟨16209494460682082134380947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10806329640454721422920631 16209494460682082134380947)
          ·
            refine ⟨24314241691023123201571421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16209494460682082134380947 24314241691023123201571421)
            ·
              refine ⟨9117840634133671200589283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24314241691023123201571421 9117840634133671200589283)
              ·
                refine ⟨13676760951200506800883925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9117840634133671200589283 13676760951200506800883925)
                ·
                  refine ⟨320549084793761878145717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13676760951200506800883925 320549084793761878145717)
                  ·
                    rfl

theorem cell21_1404601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 7].length) (baseStart_1404601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1404601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1404601 prefixEnd_1404601 := by exact prefixLift 1404601
  have htrace : WordTrace (prefixWord ++ tailWord_1404601) baseStart_1404601 baseEnd_1404601 := by
    simpa [prefixWord, tailWord_1404601, baseEnd_1404601] using wordTrace_append hprefix tailTrace_1404601
  have hstable : (prefixWord ++ tailWord_1404601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404601).length < 2 ^ (prefixWord ++ tailWord_1404601).sum := by decide
  have hdescent : baseEnd_1404601 < baseStart_1404601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404604 : List Nat := [2, 2, 2, 3, 1, 3, 3, 5]
def baseStart_1404604 : Nat := 118140960795 + 1404604 * 2 ^ 59
def prefixEnd_1404604 : Nat := 4983230072969 + 3 ^ 40 * 1404604 * 2
def baseEnd_1404604 : Nat := 106849923144878179865237

theorem tailTrace_1404604 : CollatzResearch.WordTrace tailWord_1404604 prefixEnd_1404604 106849923144878179865237 := by
  unfold tailWord_1404604
  simp only [CollatzResearch.WordTrace]
  refine ⟨25615058301683535054954433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34153411068911380073272577 25615058301683535054954433)
  ·
    refine ⟨19211293726262651291215825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25615058301683535054954433 19211293726262651291215825)
    ·
      refine ⟨14408470294696988468411869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19211293726262651291215825 14408470294696988468411869)
      ·
        refine ⟨5403176360511370675654451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14408470294696988468411869 5403176360511370675654451)
        ·
          refine ⟨8104764540767056013481677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5403176360511370675654451 8104764540767056013481677)
          ·
            refine ⟨3039286702787646005055629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8104764540767056013481677 3039286702787646005055629)
            ·
              refine ⟨1139732513545367251895861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3039286702787646005055629 1139732513545367251895861)
              ·
                refine ⟨106849923144878179865237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1139732513545367251895861 106849923144878179865237)
                ·
                  rfl

theorem cell21_1404604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 5].length) (baseStart_1404604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1404604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1404604 prefixEnd_1404604 := by exact prefixLift 1404604
  have htrace : WordTrace (prefixWord ++ tailWord_1404604) baseStart_1404604 baseEnd_1404604 := by
    simpa [prefixWord, tailWord_1404604, baseEnd_1404604] using wordTrace_append hprefix tailTrace_1404604
  have hstable : (prefixWord ++ tailWord_1404604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404604).length < 2 ^ (prefixWord ++ tailWord_1404604).sum := by decide
  have hdescent : baseEnd_1404604 < baseStart_1404604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404632 : List Nat := [2, 1, 2, 2, 3, 1, 3, 1, 6]
def baseStart_1404632 : Nat := 118140960795 + 1404632 * 2 ^ 59
def prefixEnd_1404632 : Nat := 4983230072969 + 3 ^ 40 * 1404632 * 2
def baseEnd_1404632 : Nat := 320556159416112713128987

theorem tailTrace_1404632 : CollatzResearch.WordTrace tailWord_1404632 prefixEnd_1404632 320556159416112713128987 := by
  unfold tailWord_1404632
  simp only [CollatzResearch.WordTrace]
  refine ⟨25615568923632815445964075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34154091898177087261285433 25615568923632815445964075)
  ·
    refine ⟨38423353385449223168946113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25615568923632815445964075 38423353385449223168946113)
    ·
      refine ⟨28817515039086917376709585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38423353385449223168946113 28817515039086917376709585)
      ·
        refine ⟨21613136279315188032532189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28817515039086917376709585 21613136279315188032532189)
        ·
          refine ⟨8104926104743195512199571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21613136279315188032532189 8104926104743195512199571)
          ·
            refine ⟨12157389157114793268299357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8104926104743195512199571 12157389157114793268299357)
            ·
              refine ⟨4559020933918047475612259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12157389157114793268299357 4559020933918047475612259)
              ·
                refine ⟨6838531400877071213418389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4559020933918047475612259 6838531400877071213418389)
                ·
                  refine ⟨320556159416112713128987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6838531400877071213418389 320556159416112713128987)
                  ·
                    rfl

theorem cell21_1404632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 6].length) (baseStart_1404632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1404632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1404632 prefixEnd_1404632 := by exact prefixLift 1404632
  have htrace : WordTrace (prefixWord ++ tailWord_1404632) baseStart_1404632 baseEnd_1404632 := by
    simpa [prefixWord, tailWord_1404632, baseEnd_1404632] using wordTrace_append hprefix tailTrace_1404632
  have hstable : (prefixWord ++ tailWord_1404632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404632).length < 2 ^ (prefixWord ++ tailWord_1404632).sum := by decide
  have hdescent : baseEnd_1404632 < baseStart_1404632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404663 : List Nat := [1, 1, 3, 1, 1, 1, 8, 5]
def baseStart_1404663 : Nat := 118140960795 + 1404663 * 2 ^ 59
def prefixEnd_1404663 : Nat := 4983230072969 + 3 ^ 40 * 1404663 * 2
def baseEnd_1404663 : Nat := 106854411346154516037419

theorem tailTrace_1404663 : CollatzResearch.WordTrace tailWord_1404663 prefixEnd_1404663 106854411346154516037419 := by
  unfold tailWord_1404663
  simp only [CollatzResearch.WordTrace]
  refine ⟨51232268510153323186306643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34154845673435548790871095 51232268510153323186306643)
  ·
    refine ⟨76848402765229984779459965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51232268510153323186306643 76848402765229984779459965)
    ·
      refine ⟨28818151036961244292297487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76848402765229984779459965 28818151036961244292297487)
      ·
        refine ⟨43227226555441866438446231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28818151036961244292297487 43227226555441866438446231)
        ·
          refine ⟨64840839833162799657669347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43227226555441866438446231 64840839833162799657669347)
          ·
            refine ⟨97261259749744199486504021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64840839833162799657669347 97261259749744199486504021)
            ·
              refine ⟨1139780387692314837732469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 97261259749744199486504021 1139780387692314837732469)
              ·
                refine ⟨106854411346154516037419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1139780387692314837732469 106854411346154516037419)
                ·
                  rfl

theorem cell21_1404663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 5].length) (baseStart_1404663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1404663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1404663 prefixEnd_1404663 := by exact prefixLift 1404663
  have htrace : WordTrace (prefixWord ++ tailWord_1404663) baseStart_1404663 baseEnd_1404663 := by
    simpa [prefixWord, tailWord_1404663, baseEnd_1404663] using wordTrace_append hprefix tailTrace_1404663
  have hstable : (prefixWord ++ tailWord_1404663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404663).length < 2 ^ (prefixWord ++ tailWord_1404663).sum := by decide
  have hdescent : baseEnd_1404663 < baseStart_1404663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404756 : List Nat := [2, 4, 1, 1, 3, 3, 1, 6]
def baseStart_1404756 : Nat := 118140960795 + 1404756 * 2 ^ 59
def prefixEnd_1404756 : Nat := 4983230072969 + 3 ^ 40 * 1404756 * 2
def baseEnd_1404756 : Nat := 106861485968505351020689

theorem tailTrace_1404756 : CollatzResearch.WordTrace tailWord_1404756 prefixEnd_1404756 106861485968505351020689 := by
  unfold tailWord_1404756
  simp only [CollatzResearch.WordTrace]
  refine ⟨25617830249408200034721061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34157106999210933379628081 25617830249408200034721061)
  ·
    refine ⟨4803343171764037506510199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25617830249408200034721061 4803343171764037506510199)
    ·
      refine ⟨7205014757646056259765299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4803343171764037506510199 7205014757646056259765299)
      ·
        refine ⟨10807522136469084389647949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7205014757646056259765299 10807522136469084389647949)
        ·
          refine ⟨4052820801175906646117981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10807522136469084389647949 4052820801175906646117981)
          ·
            refine ⟨1519807800440964992294243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4052820801175906646117981 1519807800440964992294243)
            ·
              refine ⟨2279711700661447488441365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1519807800440964992294243 2279711700661447488441365)
              ·
                refine ⟨106861485968505351020689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2279711700661447488441365 106861485968505351020689)
                ·
                  rfl

theorem cell21_1404756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 6].length) (baseStart_1404756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1404756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1404756 prefixEnd_1404756 := by exact prefixLift 1404756
  have htrace : WordTrace (prefixWord ++ tailWord_1404756) baseStart_1404756 baseEnd_1404756 := by
    simpa [prefixWord, tailWord_1404756, baseEnd_1404756] using wordTrace_append hprefix tailTrace_1404756
  have hstable : (prefixWord ++ tailWord_1404756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404756).length < 2 ^ (prefixWord ++ tailWord_1404756).sum := by decide
  have hdescent : baseEnd_1404756 < baseStart_1404756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404770 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 7]
def baseStart_1404770 : Nat := 118140960795 + 1404770 * 2 ^ 59
def prefixEnd_1404770 : Nat := 4983230072969 + 3 ^ 40 * 1404770 * 2
def baseEnd_1404770 : Nat := 320587652896255139828705

theorem tailTrace_1404770 : CollatzResearch.WordTrace tailWord_1404770 prefixEnd_1404770 320587652896255139828705 := by
  unfold tailWord_1404770
  simp only [CollatzResearch.WordTrace]
  refine ⟨12809042780191420115112941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34157447413843786973634509 12809042780191420115112941)
  ·
    refine ⟨4803391042571782543167353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12809042780191420115112941 4803391042571782543167353)
    ·
      refine ⟨3602543281928836907375515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4803391042571782543167353 3602543281928836907375515)
      ·
        refine ⟨5403814922893255361063273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3602543281928836907375515 5403814922893255361063273)
        ·
          refine ⟨4052861192169941520797455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5403814922893255361063273 4052861192169941520797455)
          ·
            refine ⟨6079291788254912281196183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4052861192169941520797455 6079291788254912281196183)
            ·
              refine ⟨9118937682382368421794275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6079291788254912281196183 9118937682382368421794275)
              ·
                refine ⟨13678406523573552632691413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9118937682382368421794275 13678406523573552632691413)
                ·
                  refine ⟨320587652896255139828705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13678406523573552632691413 320587652896255139828705)
                  ·
                    rfl

theorem cell21_1404770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_1404770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1404770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1404770 prefixEnd_1404770 := by exact prefixLift 1404770
  have htrace : WordTrace (prefixWord ++ tailWord_1404770) baseStart_1404770 baseEnd_1404770 := by
    simpa [prefixWord, tailWord_1404770, baseEnd_1404770] using wordTrace_append hprefix tailTrace_1404770
  have hstable : (prefixWord ++ tailWord_1404770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404770).length < 2 ^ (prefixWord ++ tailWord_1404770).sum := by decide
  have hdescent : baseEnd_1404770 < baseStart_1404770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404863 : List Nat := [1, 1, 2, 2, 2, 1, 7, 2, 3]
def baseStart_1404863 : Nat := 118140960795 + 1404863 * 2 ^ 59
def prefixEnd_1404863 : Nat := 4983230072969 + 3 ^ 40 * 1404863 * 2
def baseEnd_1404863 : Nat := 320608876763307644778515

theorem tailTrace_1404863 : CollatzResearch.WordTrace tailWord_1404863 prefixEnd_1404863 320608876763307644778515 := by
  unfold tailWord_1404863
  simp only [CollatzResearch.WordTrace]
  refine ⟨51239563109428757343587243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34159708739619171562391495 51239563109428757343587243)
  ·
    refine ⟨76859344664143136015380865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51239563109428757343587243 76859344664143136015380865)
    ·
      refine ⟨57644508498107352011535649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76859344664143136015380865 57644508498107352011535649)
      ·
        refine ⟨43233381373580514008651737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57644508498107352011535649 43233381373580514008651737)
        ·
          refine ⟨32425036030185385506488803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43233381373580514008651737 32425036030185385506488803)
          ·
            refine ⟨48637554045278078259733205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32425036030185385506488803 48637554045278078259733205)
            ·
              refine ⟨1139942672936204959212497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 48637554045278078259733205 1139942672936204959212497)
              ·
                refine ⟨854957004702153719409373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1139942672936204959212497 854957004702153719409373)
                ·
                  refine ⟨320608876763307644778515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 854957004702153719409373 320608876763307644778515)
                  ·
                    rfl

theorem cell21_1404863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2, 3].length) (baseStart_1404863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1404863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1404863 prefixEnd_1404863 := by exact prefixLift 1404863
  have htrace : WordTrace (prefixWord ++ tailWord_1404863) baseStart_1404863 baseEnd_1404863 := by
    simpa [prefixWord, tailWord_1404863, baseEnd_1404863] using wordTrace_append hprefix tailTrace_1404863
  have hstable : (prefixWord ++ tailWord_1404863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404863).length < 2 ^ (prefixWord ++ tailWord_1404863).sum := by decide
  have hdescent : baseEnd_1404863 < baseStart_1404863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404874 : List Nat := [3, 1, 2, 1, 2, 1, 3, 8]
def baseStart_1404874 : Nat := 118140960795 + 1404874 * 2 ^ 59
def prefixEnd_1404874 : Nat := 4983230072969 + 3 ^ 40 * 1404874 * 2
def baseEnd_1404874 : Nat := 106870462371058023365053

theorem tailTrace_1404874 : CollatzResearch.WordTrace tailWord_1404874 prefixEnd_1404874 106870462371058023365053 := by
  unfold tailWord_1404874
  simp only [CollatzResearch.WordTrace]
  refine ⟨12809991078097226555559419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34159976208259270814825117 12809991078097226555559419)
  ·
    refine ⟨19214986617145839833339129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12809991078097226555559419 19214986617145839833339129)
    ·
      refine ⟨14411239962859379875004347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19214986617145839833339129 14411239962859379875004347)
      ·
        refine ⟨21616859944289069812506521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14411239962859379875004347 21616859944289069812506521)
        ·
          refine ⟨16212644958216802359379891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21616859944289069812506521 16212644958216802359379891)
          ·
            refine ⟨24318967437325203539069837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16212644958216802359379891 24318967437325203539069837)
            ·
              refine ⟨9119612788996951327151189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24318967437325203539069837 9119612788996951327151189)
              ·
                refine ⟨106870462371058023365053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9119612788996951327151189 106870462371058023365053)
                ·
                  rfl

theorem cell21_1404874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 8].length) (baseStart_1404874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1404874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1404874 prefixEnd_1404874 := by exact prefixLift 1404874
  have htrace : WordTrace (prefixWord ++ tailWord_1404874) baseStart_1404874 baseEnd_1404874 := by
    simpa [prefixWord, tailWord_1404874, baseEnd_1404874] using wordTrace_append hprefix tailTrace_1404874
  have hstable : (prefixWord ++ tailWord_1404874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404874).length < 2 ^ (prefixWord ++ tailWord_1404874).sum := by decide
  have hdescent : baseEnd_1404874 < baseStart_1404874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404936 : List Nat := [2, 1, 3, 2, 1, 2, 1, 5, 4]
def baseStart_1404936 : Nat := 118140960795 + 1404936 * 2 ^ 59
def prefixEnd_1404936 : Nat := 4983230072969 + 3 ^ 40 * 1404936 * 2
def baseEnd_1404936 : Nat := 320625536357875740061699

theorem tailTrace_1404936 : CollatzResearch.WordTrace tailWord_1404936 prefixEnd_1404936 320625536357875740061699 := by
  unfold tailWord_1404936
  simp only [CollatzResearch.WordTrace]
  refine ⟨25621112819082145405497331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34161483758776193873996441 25621112819082145405497331)
  ·
    refine ⟨38431669228623218108245997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25621112819082145405497331 38431669228623218108245997)
    ·
      refine ⟨14411875960733706790592249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38431669228623218108245997 14411875960733706790592249)
      ·
        refine ⟨10808906970550280092944187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14411875960733706790592249 10808906970550280092944187)
        ·
          refine ⟨16213360455825420139416281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10808906970550280092944187 16213360455825420139416281)
          ·
            refine ⟨12160020341869065104562211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16213360455825420139416281 12160020341869065104562211)
            ·
              refine ⟨18240030512803597656843317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12160020341869065104562211 18240030512803597656843317)
              ·
                refine ⟨1710002860575337280329061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18240030512803597656843317 1710002860575337280329061)
                ·
                  refine ⟨320625536357875740061699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1710002860575337280329061 320625536357875740061699)
                  ·
                    rfl

theorem cell21_1404936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 4].length) (baseStart_1404936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1404936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1404936 prefixEnd_1404936 := by exact prefixLift 1404936
  have htrace : WordTrace (prefixWord ++ tailWord_1404936) baseStart_1404936 baseEnd_1404936 := by
    simpa [prefixWord, tailWord_1404936, baseEnd_1404936] using wordTrace_append hprefix tailTrace_1404936
  have hstable : (prefixWord ++ tailWord_1404936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404936).length < 2 ^ (prefixWord ++ tailWord_1404936).sum := by decide
  have hdescent : baseEnd_1404936 < baseStart_1404936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404970 : List Nat := [3, 1, 4, 1, 2, 3, 1, 2, 4]
def baseStart_1404970 : Nat := 118140960795 + 1404970 * 2 ^ 59
def prefixEnd_1404970 : Nat := 4983230072969 + 3 ^ 40 * 1404970 * 2
def baseEnd_1404970 : Nat := 320633295621099236494963

theorem tailTrace_1404970 : CollatzResearch.WordTrace tailWord_1404970 prefixEnd_1404970 320633295621099236494963 := by
  unfold tailWord_1404970
  simp only [CollatzResearch.WordTrace]
  refine ⟨12810866430010278654433091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34162310480027409745154909 12810866430010278654433091)
  ·
    refine ⟨19216299645015417981649637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12810866430010278654433091 19216299645015417981649637)
    ·
      refine ⟨3603056183440390871559307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19216299645015417981649637 3603056183440390871559307)
      ·
        refine ⟨5404584275160586307338961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3603056183440390871559307 5404584275160586307338961)
        ·
          refine ⟨4053438206370439730504221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5404584275160586307338961 4053438206370439730504221)
          ·
            refine ⟨1520039327388914898939083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4053438206370439730504221 1520039327388914898939083)
            ·
              refine ⟨2280058991083372348408625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1520039327388914898939083 2280058991083372348408625)
              ·
                refine ⟨1710044243312529261306469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2280058991083372348408625 1710044243312529261306469)
                ·
                  refine ⟨320633295621099236494963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1710044243312529261306469 320633295621099236494963)
                  ·
                    rfl

theorem cell21_1404970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_1404970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1404970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1404970 prefixEnd_1404970 := by exact prefixLift 1404970
  have htrace : WordTrace (prefixWord ++ tailWord_1404970) baseStart_1404970 baseEnd_1404970 := by
    simpa [prefixWord, tailWord_1404970, baseEnd_1404970] using wordTrace_append hprefix tailTrace_1404970
  have hstable : (prefixWord ++ tailWord_1404970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404970).length < 2 ^ (prefixWord ++ tailWord_1404970).sum := by decide
  have hdescent : baseEnd_1404970 < baseStart_1404970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404981 : List Nat := [1, 3, 3, 1, 1, 1, 3, 3, 5]
def baseStart_1404981 : Nat := 118140960795 + 1404981 * 2 ^ 59
def prefixEnd_1404981 : Nat := 4983230072969 + 3 ^ 40 * 1404981 * 2
def baseEnd_1404981 : Nat := 320635805970965661811607

theorem tailTrace_1404981 : CollatzResearch.WordTrace tailWord_1404981 prefixEnd_1404981 320635805970965661811607 := by
  unfold tailWord_1404981
  simp only [CollatzResearch.WordTrace]
  refine ⟨51243866923001263496382797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34162577948667508997588531 51243866923001263496382797)
  ·
    refine ⟨19216450096125473811143549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51243866923001263496382797 19216450096125473811143549)
    ·
      refine ⟨7206168786047052679178831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19216450096125473811143549 7206168786047052679178831)
      ·
        refine ⟨10809253179070579018768247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7206168786047052679178831 10809253179070579018768247)
        ·
          refine ⟨16213879768605868528152371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10809253179070579018768247 16213879768605868528152371)
          ·
            refine ⟨24320819652908802792228557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16213879768605868528152371 24320819652908802792228557)
            ·
              refine ⟨9120307369840801047085709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24320819652908802792228557 9120307369840801047085709)
              ·
                refine ⟨3420115263690300392657141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9120307369840801047085709 3420115263690300392657141)
                ·
                  refine ⟨320635805970965661811607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3420115263690300392657141 320635805970965661811607)
                  ·
                    rfl

theorem cell21_1404981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_1404981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1404981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1404981 prefixEnd_1404981 := by exact prefixLift 1404981
  have htrace : WordTrace (prefixWord ++ tailWord_1404981) baseStart_1404981 baseEnd_1404981 := by
    simpa [prefixWord, tailWord_1404981, baseEnd_1404981] using wordTrace_append hprefix tailTrace_1404981
  have hstable : (prefixWord ++ tailWord_1404981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404981).length < 2 ^ (prefixWord ++ tailWord_1404981).sum := by decide
  have hdescent : baseEnd_1404981 < baseStart_1404981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405046 : List Nat := [5, 1, 1, 2, 1, 2, 4, 1, 4]
def baseStart_1405046 : Nat := 118140960795 + 1405046 * 2 ^ 59
def prefixEnd_1405046 : Nat := 4983230072969 + 3 ^ 40 * 1405046 * 2
def baseEnd_1405046 : Nat := 320650639856539993228141

theorem tailTrace_1405046 : CollatzResearch.WordTrace tailWord_1405046 prefixEnd_1405046 320650639856539993228141 := by
  unfold tailWord_1405046
  simp only [CollatzResearch.WordTrace]
  refine ⟨3202889854235361224843687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34164158445177186398332661 3202889854235361224843687)
  ·
    refine ⟨4804334781353041837265531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3202889854235361224843687 4804334781353041837265531)
    ·
      refine ⟨7206502172029562755898297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4804334781353041837265531 7206502172029562755898297)
      ·
        refine ⟨5404876629022172066923723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7206502172029562755898297 5404876629022172066923723)
        ·
          refine ⟨8107314943533258100385585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5404876629022172066923723 8107314943533258100385585)
          ·
            refine ⟨6080486207649943575289189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8107314943533258100385585 6080486207649943575289189)
            ·
              refine ⟨1140091163934364420366723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6080486207649943575289189 1140091163934364420366723)
              ·
                refine ⟨1710136745901546630550085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1140091163934364420366723 1710136745901546630550085)
                ·
                  refine ⟨320650639856539993228141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1710136745901546630550085 320650639856539993228141)
                  ·
                    rfl

theorem cell21_1405046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_1405046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1405046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1405046 prefixEnd_1405046 := by exact prefixLift 1405046
  have htrace : WordTrace (prefixWord ++ tailWord_1405046) baseStart_1405046 baseEnd_1405046 := by
    simpa [prefixWord, tailWord_1405046, baseEnd_1405046] using wordTrace_append hprefix tailTrace_1405046
  have hstable : (prefixWord ++ tailWord_1405046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405046).length < 2 ^ (prefixWord ++ tailWord_1405046).sum := by decide
  have hdescent : baseEnd_1405046 < baseStart_1405046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405088 : List Nat := [2, 1, 1, 4, 2, 2, 1, 4, 4]
def baseStart_1405088 : Nat := 118140960795 + 1405088 * 2 ^ 59
def prefixEnd_1405088 : Nat := 4983230072969 + 3 ^ 40 * 1405088 * 2
def baseEnd_1405088 : Nat := 320660224828757253528055

theorem tailTrace_1405088 : CollatzResearch.WordTrace tailWord_1405088 prefixEnd_1405088 320660224828757253528055 := by
  unfold tailWord_1405088
  simp only [CollatzResearch.WordTrace]
  refine ⟨25623884766806810385263959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34165179689075747180351945 25623884766806810385263959)
  ·
    refine ⟨38435827150210215577895939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25623884766806810385263959 38435827150210215577895939)
    ·
      refine ⟨57653740725315323366843909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38435827150210215577895939 57653740725315323366843909)
      ·
        refine ⟨10810076385996623131283233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57653740725315323366843909 10810076385996623131283233)
        ·
          refine ⟨8107557289497467348462425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10810076385996623131283233 8107557289497467348462425)
          ·
            refine ⟨6080667967123100511346819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8107557289497467348462425 6080667967123100511346819)
            ·
              refine ⟨9121001950684650767020229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6080667967123100511346819 9121001950684650767020229)
              ·
                refine ⟨1710187865753372018816293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9121001950684650767020229 1710187865753372018816293)
                ·
                  refine ⟨320660224828757253528055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1710187865753372018816293 320660224828757253528055)
                  ·
                    rfl

theorem cell21_1405088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 4].length) (baseStart_1405088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1405088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1405088 prefixEnd_1405088 := by exact prefixLift 1405088
  have htrace : WordTrace (prefixWord ++ tailWord_1405088) baseStart_1405088 baseEnd_1405088 := by
    simpa [prefixWord, tailWord_1405088, baseEnd_1405088] using wordTrace_append hprefix tailTrace_1405088
  have hstable : (prefixWord ++ tailWord_1405088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405088).length < 2 ^ (prefixWord ++ tailWord_1405088).sum := by decide
  have hdescent : baseEnd_1405088 < baseStart_1405088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405178 : List Nat := [3, 1, 1, 1, 1, 6, 1, 7]
def baseStart_1405178 : Nat := 118140960795 + 1405178 * 2 ^ 59
def prefixEnd_1405178 : Nat := 4983230072969 + 3 ^ 40 * 1405178 * 2
def baseEnd_1405178 : Nat := 106893588018312365675957

theorem tailTrace_1405178 : CollatzResearch.WordTrace tailWord_1405178 prefixEnd_1405178 106893588018312365675957 := by
  unfold tailWord_1405178
  simp only [CollatzResearch.WordTrace]
  refine ⟨12812763025821891535326047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34167368068858377427536125 12812763025821891535326047)
  ·
    refine ⟨19219144538732837302989071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12812763025821891535326047 19219144538732837302989071)
    ·
      refine ⟨28828716808099255954483607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19219144538732837302989071 28828716808099255954483607)
      ·
        refine ⟨43243075212148883931725411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28828716808099255954483607 43243075212148883931725411)
        ·
          refine ⟨64864612818223325897588117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43243075212148883931725411 64864612818223325897588117)
          ·
            refine ⟨3040528725854218401449443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 64864612818223325897588117 3040528725854218401449443)
            ·
              refine ⟨4560793088781327602174165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3040528725854218401449443 4560793088781327602174165)
              ·
                refine ⟨106893588018312365675957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4560793088781327602174165 106893588018312365675957)
                ·
                  rfl

theorem cell21_1405178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 7].length) (baseStart_1405178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1405178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1405178 prefixEnd_1405178 := by exact prefixLift 1405178
  have htrace : WordTrace (prefixWord ++ tailWord_1405178) baseStart_1405178 baseEnd_1405178 := by
    simpa [prefixWord, tailWord_1405178, baseEnd_1405178] using wordTrace_append hprefix tailTrace_1405178
  have hstable : (prefixWord ++ tailWord_1405178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405178).length < 2 ^ (prefixWord ++ tailWord_1405178).sum := by decide
  have hdescent : baseEnd_1405178 < baseStart_1405178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405285 : List Nat := [1, 3, 1, 3, 1, 4, 1, 2, 5]
def baseStart_1405285 : Nat := 118140960795 + 1405285 * 2 ^ 59
def prefixEnd_1405285 : Nat := 4983230072969 + 3 ^ 40 * 1405285 * 2
def baseEnd_1405285 : Nat := 320705182912728688744319

theorem tailTrace_1405285 : CollatzResearch.WordTrace tailWord_1405285 prefixEnd_1405285 320705182912728688744319 := by
  unfold tailWord_1405285
  simp only [CollatzResearch.WordTrace]
  refine ⟨51254954713899923415449309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34169969809266615610299539 51254954713899923415449309)
  ·
    refine ⟨19220608017712471280793491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51254954713899923415449309 19220608017712471280793491)
    ·
      refine ⟨28830912026568706921190237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19220608017712471280793491 28830912026568706921190237)
      ·
        refine ⟨10811592009963265095446339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28830912026568706921190237 10811592009963265095446339)
        ·
          refine ⟨16217388014944897643169509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10811592009963265095446339 16217388014944897643169509)
          ·
            refine ⟨3040760252802168308094283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16217388014944897643169509 3040760252802168308094283)
            ·
              refine ⟨4561140379203252462141425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3040760252802168308094283 4561140379203252462141425)
              ·
                refine ⟨3420855284402439346606069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4561140379203252462141425 3420855284402439346606069)
                ·
                  refine ⟨320705182912728688744319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3420855284402439346606069 320705182912728688744319)
                  ·
                    rfl

theorem cell21_1405285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_1405285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1405285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1405285 prefixEnd_1405285 := by exact prefixLift 1405285
  have htrace : WordTrace (prefixWord ++ tailWord_1405285) baseStart_1405285 baseEnd_1405285 := by
    simpa [prefixWord, tailWord_1405285, baseEnd_1405285] using wordTrace_append hprefix tailTrace_1405285
  have hstable : (prefixWord ++ tailWord_1405285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405285).length < 2 ^ (prefixWord ++ tailWord_1405285).sum := by decide
  have hdescent : baseEnd_1405285 < baseStart_1405285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405347 : List Nat := [1, 1, 1, 4, 1, 6, 2, 5]
def baseStart_1405347 : Nat := 118140960795 + 1405347 * 2 ^ 59
def prefixEnd_1405347 : Nat := 4983230072969 + 3 ^ 40 * 1405347 * 2
def baseEnd_1405347 : Nat := 106906444052476786236953

theorem tailTrace_1405347 : CollatzResearch.WordTrace tailWord_1405347 prefixEnd_1405347 106906444052476786236953 := by
  unfold tailWord_1405347
  simp only [CollatzResearch.WordTrace]
  refine ⟨51257216039675308004206295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34171477359783538669470863 51257216039675308004206295)
  ·
    refine ⟨76885824059512962006309443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51257216039675308004206295 76885824059512962006309443)
    ·
      refine ⟨115328736089269443009464165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76885824059512962006309443 115328736089269443009464165)
      ·
        refine ⟨21624138016738020564274531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115328736089269443009464165 21624138016738020564274531)
        ·
          refine ⟨32436207025107030846411797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21624138016738020564274531 32436207025107030846411797)
          ·
            refine ⟨1520447204301892070925553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32436207025107030846411797 1520447204301892070925553)
            ·
              refine ⟨1140335403226419053194165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1520447204301892070925553 1140335403226419053194165)
              ·
                refine ⟨106906444052476786236953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1140335403226419053194165 106906444052476786236953)
                ·
                  rfl

theorem cell21_1405347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 5].length) (baseStart_1405347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1405347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1405347 prefixEnd_1405347 := by exact prefixLift 1405347
  have htrace : WordTrace (prefixWord ++ tailWord_1405347) baseStart_1405347 baseEnd_1405347 := by
    simpa [prefixWord, tailWord_1405347, baseEnd_1405347] using wordTrace_append hprefix tailTrace_1405347
  have hstable : (prefixWord ++ tailWord_1405347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405347).length < 2 ^ (prefixWord ++ tailWord_1405347).sum := by decide
  have hdescent : baseEnd_1405347 < baseStart_1405347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405429 : List Nat := [1, 3, 5, 1, 2, 2, 2, 2, 3]
def baseStart_1405429 : Nat := 118140960795 + 1405429 * 2 ^ 59
def prefixEnd_1405429 : Nat := 4983230072969 + 3 ^ 40 * 1405429 * 2
def baseEnd_1405429 : Nat := 320738045674616438344025

theorem tailTrace_1405429 : CollatzResearch.WordTrace tailWord_1405429 prefixEnd_1405429 320738045674616438344025 := by
  unfold tailWord_1405429
  simp only [CollatzResearch.WordTrace]
  refine ⟨51260206825378236008691341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34173471216918824005794227 51260206825378236008691341)
  ·
    refine ⟨19222577559516838503259253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51260206825378236008691341 19222577559516838503259253)
    ·
      refine ⟨1802116646204703609680555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19222577559516838503259253 1802116646204703609680555)
      ·
        refine ⟨2703174969307055414520833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1802116646204703609680555 2703174969307055414520833)
        ·
          refine ⟨2027381226980291560890625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2703174969307055414520833 2027381226980291560890625)
          ·
            refine ⟨1520535920235218670667969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2027381226980291560890625 1520535920235218670667969)
            ·
              refine ⟨1140401940176414003000977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1520535920235218670667969 1140401940176414003000977)
              ·
                refine ⟨855301455132310502250733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1140401940176414003000977 855301455132310502250733)
                ·
                  refine ⟨320738045674616438344025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 855301455132310502250733 320738045674616438344025)
                  ·
                    rfl

theorem cell21_1405429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2, 3].length) (baseStart_1405429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1405429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1405429 prefixEnd_1405429 := by exact prefixLift 1405429
  have htrace : WordTrace (prefixWord ++ tailWord_1405429) baseStart_1405429 baseEnd_1405429 := by
    simpa [prefixWord, tailWord_1405429, baseEnd_1405429] using wordTrace_append hprefix tailTrace_1405429
  have hstable : (prefixWord ++ tailWord_1405429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405429).length < 2 ^ (prefixWord ++ tailWord_1405429).sum := by decide
  have hdescent : baseEnd_1405429 < baseStart_1405429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405482 : List Nat := [3, 1, 4, 1, 1, 3, 8]
def baseStart_1405482 : Nat := 118140960795 + 1405482 * 2 ^ 59
def prefixEnd_1405482 : Nat := 4983230072969 + 3 ^ 40 * 1405482 * 2
def baseEnd_1405482 : Nat := 35638904555188902662287

theorem tailTrace_1405482 : CollatzResearch.WordTrace tailWord_1405482 prefixEnd_1405482 35638904555188902662287 := by
  unfold tailWord_1405482
  simp only [CollatzResearch.WordTrace]
  refine ⟨12815534973546556515092675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34174759929457484040247133 12815534973546556515092675)
  ·
    refine ⟨19223302460319834772639013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12815534973546556515092675 19223302460319834772639013)
    ·
      refine ⟨3604369211309969019869815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19223302460319834772639013 3604369211309969019869815)
      ·
        refine ⟨5406553816964953529804723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3604369211309969019869815 5406553816964953529804723)
        ·
          refine ⟨8109830725447430294707085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5406553816964953529804723 8109830725447430294707085)
          ·
            refine ⟨3041186522042786360515157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8109830725447430294707085 3041186522042786360515157)
            ·
              refine ⟨35638904555188902662287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3041186522042786360515157 35638904555188902662287)
              ·
                rfl

theorem cell21_1405482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 8].length) (baseStart_1405482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1405482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1405482 prefixEnd_1405482 := by exact prefixLift 1405482
  have htrace : WordTrace (prefixWord ++ tailWord_1405482) baseStart_1405482 baseEnd_1405482 := by
    simpa [prefixWord, tailWord_1405482, baseEnd_1405482] using wordTrace_append hprefix tailTrace_1405482
  have hstable : (prefixWord ++ tailWord_1405482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405482).length < 2 ^ (prefixWord ++ tailWord_1405482).sum := by decide
  have hdescent : baseEnd_1405482 < baseStart_1405482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405561 : List Nat := [1, 2, 1, 3, 3, 4, 2, 1, 4]
def baseStart_1405561 : Nat := 118140960795 + 1405561 * 2 ^ 59
def prefixEnd_1405561 : Nat := 4983230072969 + 3 ^ 40 * 1405561 * 2
def baseEnd_1405561 : Nat := 320768169873013542143755

theorem tailTrace_1405561 : CollatzResearch.WordTrace tailWord_1405561 prefixEnd_1405561 320768169873013542143755 := by
  unfold tailWord_1405561
  simp only [CollatzResearch.WordTrace]
  refine ⟨51265021260900022552496537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34176680840600015034997691 51265021260900022552496537)
  ·
    refine ⟨38448765945675016914372403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51265021260900022552496537 38448765945675016914372403)
    ·
      refine ⟨57673148918512525371558605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38448765945675016914372403 57673148918512525371558605)
      ·
        refine ⟨21627430844442197014334477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57673148918512525371558605 21627430844442197014334477)
        ·
          refine ⟨8110286566665823880375429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21627430844442197014334477 8110286566665823880375429)
          ·
            refine ⟨1520678731249841977570393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8110286566665823880375429 1520678731249841977570393)
            ·
              refine ⟨1140509048437381483177795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1520678731249841977570393 1140509048437381483177795)
              ·
                refine ⟨1710763572656072224766693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1140509048437381483177795 1710763572656072224766693)
                ·
                  refine ⟨320768169873013542143755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1710763572656072224766693 320768169873013542143755)
                  ·
                    rfl

theorem cell21_1405561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 4].length) (baseStart_1405561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1405561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1405561 prefixEnd_1405561 := by exact prefixLift 1405561
  have htrace : WordTrace (prefixWord ++ tailWord_1405561) baseStart_1405561 baseEnd_1405561 := by
    simpa [prefixWord, tailWord_1405561, baseEnd_1405561] using wordTrace_append hprefix tailTrace_1405561
  have hstable : (prefixWord ++ tailWord_1405561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405561).length < 2 ^ (prefixWord ++ tailWord_1405561).sum := by decide
  have hdescent : baseEnd_1405561 < baseStart_1405561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405665 : List Nat := [1, 2, 3, 1, 4, 2, 2, 1, 5]
def baseStart_1405665 : Nat := 118140960795 + 1405665 * 2 ^ 59
def prefixEnd_1405665 : Nat := 4983230072969 + 3 ^ 40 * 1405665 * 2
def baseEnd_1405665 : Nat := 320791904089932472410209

theorem tailTrace_1405665 : CollatzResearch.WordTrace tailWord_1405665 prefixEnd_1405665 320791904089932472410209 := by
  unfold tailWord_1405665
  simp only [CollatzResearch.WordTrace]
  refine ⟨51268814452523248314282449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34179209635015498876188299 51268814452523248314282449)
  ·
    refine ⟨38451610839392436235711837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51268814452523248314282449 38451610839392436235711837)
    ·
      refine ⟨14419354064772163588391939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38451610839392436235711837 14419354064772163588391939)
      ·
        refine ⟨21629031097158245382587909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14419354064772163588391939 21629031097158245382587909)
        ·
          refine ⟨4055443330717171009235233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21629031097158245382587909 4055443330717171009235233)
          ·
            refine ⟨3041582498037878256926425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4055443330717171009235233 3041582498037878256926425)
            ·
              refine ⟨2281186873528408692694819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3041582498037878256926425 2281186873528408692694819)
              ·
                refine ⟨3421780310292613039042229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2281186873528408692694819 3421780310292613039042229)
                ·
                  refine ⟨320791904089932472410209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3421780310292613039042229 320791904089932472410209)
                  ·
                    rfl

theorem cell21_1405665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 5].length) (baseStart_1405665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1405665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1405665 prefixEnd_1405665 := by exact prefixLift 1405665
  have htrace : WordTrace (prefixWord ++ tailWord_1405665) baseStart_1405665 baseEnd_1405665 := by
    simpa [prefixWord, tailWord_1405665, baseEnd_1405665] using wordTrace_append hprefix tailTrace_1405665
  have hstable : (prefixWord ++ tailWord_1405665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405665).length < 2 ^ (prefixWord ++ tailWord_1405665).sum := by decide
  have hdescent : baseEnd_1405665 < baseStart_1405665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405693 : List Nat := [1, 4, 1, 1, 1, 1, 5, 7]
def baseStart_1405693 : Nat := 118140960795 + 1405693 * 2 ^ 59
def prefixEnd_1405693 : Nat := 4983230072969 + 3 ^ 40 * 1405693 * 2
def baseEnd_1405693 : Nat := 106932764690470215314495

theorem tailTrace_1405693 : CollatzResearch.WordTrace tailWord_1405693 prefixEnd_1405693 106932764690470215314495 := by
  unfold tailWord_1405693
  simp only [CollatzResearch.WordTrace]
  refine ⟨51269835696421809096301733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34179890464281206064201155 51269835696421809096301733)
  ·
    refine ⟨9613094193079089205556575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51269835696421809096301733 9613094193079089205556575)
    ·
      refine ⟨14419641289618633808334863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9613094193079089205556575 14419641289618633808334863)
      ·
        refine ⟨21629461934427950712502295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14419641289618633808334863 21629461934427950712502295)
        ·
          refine ⟨32444192901641926068753443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21629461934427950712502295 32444192901641926068753443)
          ·
            refine ⟨48666289352462889103130165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32444192901641926068753443 48666289352462889103130165)
            ·
              refine ⟨4562464626793395853418453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48666289352462889103130165 4562464626793395853418453)
              ·
                refine ⟨106932764690470215314495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4562464626793395853418453 106932764690470215314495)
                ·
                  rfl

theorem cell21_1405693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 7].length) (baseStart_1405693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1405693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1405693 prefixEnd_1405693 := by exact prefixLift 1405693
  have htrace : WordTrace (prefixWord ++ tailWord_1405693) baseStart_1405693 baseEnd_1405693 := by
    simpa [prefixWord, tailWord_1405693, baseEnd_1405693] using wordTrace_append hprefix tailTrace_1405693
  have hstable : (prefixWord ++ tailWord_1405693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405693).length < 2 ^ (prefixWord ++ tailWord_1405693).sum := by decide
  have hdescent : baseEnd_1405693 < baseStart_1405693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405772 : List Nat := [2, 2, 1, 3, 3, 2, 2, 2, 4]
def baseStart_1405772 : Nat := 118140960795 + 1405772 * 2 ^ 59
def prefixEnd_1405772 : Nat := 4983230072969 + 3 ^ 40 * 1405772 * 2
def baseEnd_1405772 : Nat := 320816322947724064126657

theorem tailTrace_1405772 : CollatzResearch.WordTrace tailWord_1405772 prefixEnd_1405772 320816322947724064126657 := by
  unfold tailWord_1405772
  simp only [CollatzResearch.WordTrace]
  refine ⟨25636358531567802794213785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34181811375423737058951713 25636358531567802794213785)
  ·
    refine ⟨19227268898675852095660339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25636358531567802794213785 19227268898675852095660339)
    ·
      refine ⟨28840903348013778143490509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19227268898675852095660339 28840903348013778143490509)
      ·
        refine ⟨10815338755505166803808941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28840903348013778143490509 10815338755505166803808941)
        ·
          refine ⟨4055752033314437551428353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10815338755505166803808941 4055752033314437551428353)
          ·
            refine ⟨3041814024985828163571265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4055752033314437551428353 3041814024985828163571265)
            ·
              refine ⟨2281360518739371122678449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3041814024985828163571265 2281360518739371122678449)
              ·
                refine ⟨1711020389054528342008837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2281360518739371122678449 1711020389054528342008837)
                ·
                  refine ⟨320816322947724064126657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1711020389054528342008837 320816322947724064126657)
                  ·
                    rfl

theorem cell21_1405772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_1405772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1405772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1405772 prefixEnd_1405772 := by exact prefixLift 1405772
  have htrace : WordTrace (prefixWord ++ tailWord_1405772) baseStart_1405772 baseEnd_1405772 := by
    simpa [prefixWord, tailWord_1405772, baseEnd_1405772] using wordTrace_append hprefix tailTrace_1405772
  have hstable : (prefixWord ++ tailWord_1405772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405772).length < 2 ^ (prefixWord ++ tailWord_1405772).sum := by decide
  have hdescent : baseEnd_1405772 < baseStart_1405772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405786 : List Nat := [3, 1, 1, 2, 1, 6, 1, 6]
def baseStart_1405786 : Nat := 118140960795 + 1405786 * 2 ^ 59
def prefixEnd_1405786 : Nat := 4983230072969 + 3 ^ 40 * 1405786 * 2
def baseEnd_1405786 : Nat := 106939839312821050297765

theorem tailTrace_1405786 : CollatzResearch.WordTrace tailWord_1405786 prefixEnd_1405786 106939839312821050297765 := by
  unfold tailWord_1405786
  simp only [CollatzResearch.WordTrace]
  refine ⟨12818306921271221494859303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34182151790056590652958141 12818306921271221494859303)
  ·
    refine ⟨19227460381906832242288955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12818306921271221494859303 19227460381906832242288955)
    ·
      refine ⟨28841190572860248363433433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19227460381906832242288955 28841190572860248363433433)
      ·
        refine ⟨21630892929645186272575075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28841190572860248363433433 21630892929645186272575075)
        ·
          refine ⟨32446339394467779408862613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21630892929645186272575075 32446339394467779408862613)
          ·
            refine ⟨1520922159115677159790435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32446339394467779408862613 1520922159115677159790435)
            ·
              refine ⟨2281383238673515739685653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1520922159115677159790435 2281383238673515739685653)
              ·
                refine ⟨106939839312821050297765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2281383238673515739685653 106939839312821050297765)
                ·
                  rfl

theorem cell21_1405786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 6].length) (baseStart_1405786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1405786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1405786 prefixEnd_1405786 := by exact prefixLift 1405786
  have htrace : WordTrace (prefixWord ++ tailWord_1405786) baseStart_1405786 baseEnd_1405786 := by
    simpa [prefixWord, tailWord_1405786, baseEnd_1405786] using wordTrace_append hprefix tailTrace_1405786
  have hstable : (prefixWord ++ tailWord_1405786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405786).length < 2 ^ (prefixWord ++ tailWord_1405786).sum := by decide
  have hdescent : baseEnd_1405786 < baseStart_1405786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405800 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 7]
def baseStart_1405800 : Nat := 118140960795 + 1405800 * 2 ^ 59
def prefixEnd_1405800 : Nat := 4983230072969 + 3 ^ 40 * 1405800 * 2
def baseEnd_1405800 : Nat := 320822712929202237659933

theorem tailTrace_1405800 : CollatzResearch.WordTrace tailWord_1405800 prefixEnd_1405800 320822712929202237659933 := by
  unfold tailWord_1405800
  simp only [CollatzResearch.WordTrace]
  refine ⟨25636869153517083185223427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34182492204689444246964569 25636869153517083185223427)
  ·
    refine ⟨38455303730275624777835141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25636869153517083185223427 38455303730275624777835141)
    ·
      refine ⟨7210369449426679645844089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38455303730275624777835141 7210369449426679645844089)
      ·
        refine ⟨5407777087070009734383067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7210369449426679645844089 5407777087070009734383067)
        ·
          refine ⟨8111665630605014601574601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5407777087070009734383067 8111665630605014601574601)
          ·
            refine ⟨6083749222953760951180951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8111665630605014601574601 6083749222953760951180951)
            ·
              refine ⟨9125623834430641426771427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6083749222953760951180951 9125623834430641426771427)
              ·
                refine ⟨13688435751645962140157141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9125623834430641426771427 13688435751645962140157141)
                ·
                  refine ⟨320822712929202237659933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13688435751645962140157141 320822712929202237659933)
                  ·
                    rfl

theorem cell21_1405800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 7].length) (baseStart_1405800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1405800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1405800 prefixEnd_1405800 := by exact prefixLift 1405800
  have htrace : WordTrace (prefixWord ++ tailWord_1405800) baseStart_1405800 baseEnd_1405800 := by
    simpa [prefixWord, tailWord_1405800, baseEnd_1405800] using wordTrace_append hprefix tailTrace_1405800
  have hstable : (prefixWord ++ tailWord_1405800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405800).length < 2 ^ (prefixWord ++ tailWord_1405800).sum := by decide
  have hdescent : baseEnd_1405800 < baseStart_1405800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405817 : List Nat := [1, 2, 1, 3, 2, 3, 1, 5, 3]
def baseStart_1405817 : Nat := 118140960795 + 1405817 * 2 ^ 59
def prefixEnd_1405817 : Nat := 4983230072969 + 3 ^ 40 * 1405817 * 2
def baseEnd_1405817 : Nat := 320826592560813985876565

theorem tailTrace_1405817 : CollatzResearch.WordTrace tailWord_1405817 prefixEnd_1405817 320826592560813985876565 := by
  unfold tailWord_1405817
  simp only [CollatzResearch.WordTrace]
  refine ⟨51274358347972578273815705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34182905565315052182543803 51274358347972578273815705)
  ·
    refine ⟨38455768760979433705361779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51274358347972578273815705 38455768760979433705361779)
    ·
      refine ⟨57683653141469150558042669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38455768760979433705361779 57683653141469150558042669)
      ·
        refine ⟨21631369928050931459266001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57683653141469150558042669 21631369928050931459266001)
        ·
          refine ⟨16223527446038198594449501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21631369928050931459266001 16223527446038198594449501)
          ·
            refine ⟨6083822792264324472918563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16223527446038198594449501 6083822792264324472918563)
            ·
              refine ⟨9125734188396486709377845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6083822792264324472918563 9125734188396486709377845)
              ·
                refine ⟨855537580162170629004173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9125734188396486709377845 855537580162170629004173)
                ·
                  refine ⟨320826592560813985876565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 855537580162170629004173 320826592560813985876565)
                  ·
                    rfl

theorem cell21_1405817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5, 3].length) (baseStart_1405817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1405817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1405817 prefixEnd_1405817 := by exact prefixLift 1405817
  have htrace : WordTrace (prefixWord ++ tailWord_1405817) baseStart_1405817 baseEnd_1405817 := by
    simpa [prefixWord, tailWord_1405817, baseEnd_1405817] using wordTrace_append hprefix tailTrace_1405817
  have hstable : (prefixWord ++ tailWord_1405817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405817).length < 2 ^ (prefixWord ++ tailWord_1405817).sum := by decide
  have hdescent : baseEnd_1405817 < baseStart_1405817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405831 : List Nat := [1, 1, 4, 2, 3, 2, 1, 1, 6]
def baseStart_1405831 : Nat := 118140960795 + 1405831 * 2 ^ 59
def prefixEnd_1405831 : Nat := 4983230072969 + 3 ^ 40 * 1405831 * 2
def baseEnd_1405831 : Nat := 320829787551553072643203

theorem tailTrace_1405831 : CollatzResearch.WordTrace tailWord_1405831 prefixEnd_1405831 320829787551553072643203 := by
  unfold tailWord_1405831
  simp only [CollatzResearch.WordTrace]
  refine ⟨51274868969921858664825347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34183245979947905776550231 51274868969921858664825347)
  ·
    refine ⟨76912303454882787997238021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51274868969921858664825347 76912303454882787997238021)
    ·
      refine ⟨14421056897790522749482129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76912303454882787997238021 14421056897790522749482129)
      ·
        refine ⟨10815792673342892062111597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14421056897790522749482129 10815792673342892062111597)
        ·
          refine ⟨4055922252503584523291849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10815792673342892062111597 4055922252503584523291849)
          ·
            refine ⟨3041941689377688392468887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4055922252503584523291849 3041941689377688392468887)
            ·
              refine ⟨4562912534066532588703331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3041941689377688392468887 4562912534066532588703331)
              ·
                refine ⟨6844368801099798883054997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4562912534066532588703331 6844368801099798883054997)
                ·
                  refine ⟨320829787551553072643203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6844368801099798883054997 320829787551553072643203)
                  ·
                    rfl

theorem cell21_1405831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 6].length) (baseStart_1405831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1405831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1405831 prefixEnd_1405831 := by exact prefixLift 1405831
  have htrace : WordTrace (prefixWord ++ tailWord_1405831) baseStart_1405831 baseEnd_1405831 := by
    simpa [prefixWord, tailWord_1405831, baseEnd_1405831] using wordTrace_append hprefix tailTrace_1405831
  have hstable : (prefixWord ++ tailWord_1405831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405831).length < 2 ^ (prefixWord ++ tailWord_1405831).sum := by decide
  have hdescent : baseEnd_1405831 < baseStart_1405831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405834 : List Nat := [3, 1, 2, 4, 1, 1, 2, 4, 3]
def baseStart_1405834 : Nat := 118140960795 + 1405834 * 2 ^ 59
def prefixEnd_1405834 : Nat := 4983230072969 + 3 ^ 40 * 1405834 * 2
def baseEnd_1405834 : Nat := 320830472192425734093197

theorem tailTrace_1405834 : CollatzResearch.WordTrace tailWord_1405834 prefixEnd_1405834 320830472192425734093197 := by
  unfold tailWord_1405834
  simp only [CollatzResearch.WordTrace]
  refine ⟨12818744597227747544296139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34183318925940660118123037 12818744597227747544296139)
  ·
    refine ⟨19228116895841621316444209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12818744597227747544296139 19228116895841621316444209)
    ·
      refine ⟨14421087671881215987333157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19228116895841621316444209 14421087671881215987333157)
      ·
        refine ⟨2703953938477727997624967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14421087671881215987333157 2703953938477727997624967)
        ·
          refine ⟨4055930907716591996437451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2703953938477727997624967 4055930907716591996437451)
          ·
            refine ⟨6083896361574887994656177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4055930907716591996437451 6083896361574887994656177)
            ·
              refine ⟨4562922271181165995992133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6083896361574887994656177 4562922271181165995992133)
              ·
                refine ⟨855547925846468624248525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4562922271181165995992133 855547925846468624248525)
                ·
                  refine ⟨320830472192425734093197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 855547925846468624248525 320830472192425734093197)
                  ·
                    rfl

theorem cell21_1405834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4, 3].length) (baseStart_1405834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1405834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1405834 prefixEnd_1405834 := by exact prefixLift 1405834
  have htrace : WordTrace (prefixWord ++ tailWord_1405834) baseStart_1405834 baseEnd_1405834 := by
    simpa [prefixWord, tailWord_1405834, baseEnd_1405834] using wordTrace_append hprefix tailTrace_1405834
  have hstable : (prefixWord ++ tailWord_1405834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405834).length < 2 ^ (prefixWord ++ tailWord_1405834).sum := by decide
  have hdescent : baseEnd_1405834 < baseStart_1405834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405938 : List Nat := [3, 2, 1, 5, 1, 9]
def baseStart_1405938 : Nat := 118140960795 + 1405938 * 2 ^ 59
def prefixEnd_1405938 : Nat := 4983230072969 + 3 ^ 40 * 1405938 * 2
def baseEnd_1405938 : Nat := 11883489126272024605913

theorem tailTrace_1405938 : CollatzResearch.WordTrace tailWord_1405938 prefixEnd_1405938 11883489126272024605913 := by
  unfold tailWord_1405938
  simp only [CollatzResearch.WordTrace]
  refine ⟨12819692895133553984742617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34185847720356143959313645 12819692895133553984742617)
  ·
    refine ⟨9614769671350165488556963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12819692895133553984742617 9614769671350165488556963)
    ·
      refine ⟨14422154507025248232835445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9614769671350165488556963 14422154507025248232835445)
      ·
        refine ⟨1352076985033617021828323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14422154507025248232835445 1352076985033617021828323)
        ·
          refine ⟨2028115477550425532742485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1352076985033617021828323 2028115477550425532742485)
          ·
            refine ⟨11883489126272024605913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2028115477550425532742485 11883489126272024605913)
            ·
              rfl

theorem cell21_1405938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 9].length) (baseStart_1405938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1405938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1405938 prefixEnd_1405938 := by exact prefixLift 1405938
  have htrace : WordTrace (prefixWord ++ tailWord_1405938) baseStart_1405938 baseEnd_1405938 := by
    simpa [prefixWord, tailWord_1405938, baseEnd_1405938] using wordTrace_append hprefix tailTrace_1405938
  have hstable : (prefixWord ++ tailWord_1405938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405938).length < 2 ^ (prefixWord ++ tailWord_1405938).sum := by decide
  have hdescent : baseEnd_1405938 < baseStart_1405938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405986 : List Nat := [3, 3, 1, 1, 1, 4, 2, 3, 3]
def baseStart_1405986 : Nat := 118140960795 + 1405986 * 2 ^ 59
def prefixEnd_1405986 : Nat := 4983230072969 + 3 ^ 40 * 1405986 * 2
def baseEnd_1405986 : Nat := 320865160663307247559553

theorem tailTrace_1405986 : CollatzResearch.WordTrace tailWord_1405986 prefixEnd_1405986 320865160663307247559553 := by
  unfold tailWord_1405986
  simp only [CollatzResearch.WordTrace]
  refine ⟨12820130571090080034179453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34187014856240213424478541 12820130571090080034179453)
  ·
    refine ⟨4807548964158780012817295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12820130571090080034179453 4807548964158780012817295)
    ·
      refine ⟨7211323446238170019225943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4807548964158780012817295 7211323446238170019225943)
      ·
        refine ⟨10816985169357255028838915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7211323446238170019225943 10816985169357255028838915)
        ·
          refine ⟨16225477754035882543258373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10816985169357255028838915 16225477754035882543258373)
          ·
            refine ⟨3042277078881727976860945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16225477754035882543258373 3042277078881727976860945)
            ·
              refine ⟨2281707809161295982645709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3042277078881727976860945 2281707809161295982645709)
              ·
                refine ⟨855640428435485993492141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2281707809161295982645709 855640428435485993492141)
                ·
                  refine ⟨320865160663307247559553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 855640428435485993492141 320865160663307247559553)
                  ·
                    rfl

theorem cell21_1405986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_1405986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1405986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1405986 prefixEnd_1405986 := by exact prefixLift 1405986
  have htrace : WordTrace (prefixWord ++ tailWord_1405986) baseStart_1405986 baseEnd_1405986 := by
    simpa [prefixWord, tailWord_1405986, baseEnd_1405986] using wordTrace_append hprefix tailTrace_1405986
  have hstable : (prefixWord ++ tailWord_1405986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405986).length < 2 ^ (prefixWord ++ tailWord_1405986).sum := by decide
  have hdescent : baseEnd_1405986 < baseStart_1405986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406017 : List Nat := [1, 2, 5, 1, 3, 1, 3, 1, 4]
def baseStart_1406017 : Nat := 118140960795 + 1406017 * 2 ^ 59
def prefixEnd_1406017 : Nat := 4983230072969 + 3 ^ 40 * 1406017 * 2
def baseEnd_1406017 : Nat := 320872235285658082542823

theorem tailTrace_1406017 : CollatzResearch.WordTrace tailWord_1406017 prefixEnd_1406017 320872235285658082542823 := by
  unfold tailWord_1406017
  simp only [CollatzResearch.WordTrace]
  refine ⟨51281652947248012431096305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34187768631498674954064203 51281652947248012431096305)
  ·
    refine ⟨38461239710436009323322229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51281652947248012431096305 38461239710436009323322229)
    ·
      refine ⟨3605741222853375874061459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38461239710436009323322229 3605741222853375874061459)
      ·
        refine ⟨5408611834280063811092189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3605741222853375874061459 5408611834280063811092189)
        ·
          refine ⟨2028229437855023929159571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5408611834280063811092189 2028229437855023929159571)
          ·
            refine ⟨3042344156782535893739357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2028229437855023929159571 3042344156782535893739357)
            ·
              refine ⟨1140879058793450960152259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3042344156782535893739357 1140879058793450960152259)
              ·
                refine ⟨1711318588190176440228389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1140879058793450960152259 1711318588190176440228389)
                ·
                  refine ⟨320872235285658082542823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1711318588190176440228389 320872235285658082542823)
                  ·
                    rfl

theorem cell21_1406017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 4].length) (baseStart_1406017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1406017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1406017 prefixEnd_1406017 := by exact prefixLift 1406017
  have htrace : WordTrace (prefixWord ++ tailWord_1406017) baseStart_1406017 baseEnd_1406017 := by
    simpa [prefixWord, tailWord_1406017, baseEnd_1406017] using wordTrace_append hprefix tailTrace_1406017
  have hstable : (prefixWord ++ tailWord_1406017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406017).length < 2 ^ (prefixWord ++ tailWord_1406017).sum := by decide
  have hdescent : baseEnd_1406017 < baseStart_1406017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406087 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 7]
def baseStart_1406087 : Nat := 118140960795 + 1406087 * 2 ^ 59
def prefixEnd_1406087 : Nat := 4983230072969 + 3 ^ 40 * 1406087 * 2
def baseEnd_1406087 : Nat := 320888210239353516376013

theorem tailTrace_1406087 : CollatzResearch.WordTrace tailWord_1406087 prefixEnd_1406087 320888210239353516376013 := by
  unfold tailWord_1406087
  simp only [CollatzResearch.WordTrace]
  refine ⟨51284206056994414386144515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34189470704662942924096343 51284206056994414386144515)
  ·
    refine ⟨76926309085491621579216773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51284206056994414386144515 76926309085491621579216773)
    ·
      refine ⟨14423682953529679046103145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76926309085491621579216773 14423682953529679046103145)
      ·
        refine ⟨10817762215147259284577359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14423682953529679046103145 10817762215147259284577359)
        ·
          refine ⟨16226643322720888926866039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10817762215147259284577359 16226643322720888926866039)
          ·
            refine ⟨24339964984081333390299059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16226643322720888926866039 24339964984081333390299059)
            ·
              refine ⟨36509947476122000085448589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24339964984081333390299059 36509947476122000085448589)
              ·
                refine ⟨13691230303545750032043221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36509947476122000085448589 13691230303545750032043221)
                ·
                  refine ⟨320888210239353516376013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13691230303545750032043221 320888210239353516376013)
                  ·
                    rfl

theorem cell21_1406087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 7].length) (baseStart_1406087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1406087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1406087 prefixEnd_1406087 := by exact prefixLift 1406087
  have htrace : WordTrace (prefixWord ++ tailWord_1406087) baseStart_1406087 baseEnd_1406087 := by
    simpa [prefixWord, tailWord_1406087, baseEnd_1406087] using wordTrace_append hprefix tailTrace_1406087
  have hstable : (prefixWord ++ tailWord_1406087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406087).length < 2 ^ (prefixWord ++ tailWord_1406087).sum := by decide
  have hdescent : baseEnd_1406087 < baseStart_1406087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406242 : List Nat := [3, 3, 1, 1, 4, 1, 2, 6]
def baseStart_1406242 : Nat := 118140960795 + 1406242 * 2 ^ 59
def prefixEnd_1406242 : Nat := 4983230072969 + 3 ^ 40 * 1406242 * 2
def baseEnd_1406242 : Nat := 106974527783702563764121

theorem tailTrace_1406242 : CollatzResearch.WordTrace tailWord_1406242 prefixEnd_1406242 106974527783702563764121 := by
  unfold tailWord_1406242
  simp only [CollatzResearch.WordTrace]
  refine ⟨12822464842858218964509245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34193239580955250572024653 12822464842858218964509245)
  ·
    refine ⟨4808424316071832111690967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12822464842858218964509245 4808424316071832111690967)
    ·
      refine ⟨7212636474107748167536451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4808424316071832111690967 7212636474107748167536451)
      ·
        refine ⟨10818954711161622251304677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7212636474107748167536451 10818954711161622251304677)
        ·
          refine ⟨2028554008342804172119627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10818954711161622251304677 2028554008342804172119627)
          ·
            refine ⟨3042831012514206258179441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2028554008342804172119627 3042831012514206258179441)
            ·
              refine ⟨2282123259385654693634581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3042831012514206258179441 2282123259385654693634581)
              ·
                refine ⟨106974527783702563764121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2282123259385654693634581 106974527783702563764121)
                ·
                  rfl

theorem cell21_1406242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 6].length) (baseStart_1406242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1406242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1406242 prefixEnd_1406242 := by exact prefixLift 1406242
  have htrace : WordTrace (prefixWord ++ tailWord_1406242) baseStart_1406242 baseEnd_1406242 := by
    simpa [prefixWord, tailWord_1406242, baseEnd_1406242] using wordTrace_append hprefix tailTrace_1406242
  have hstable : (prefixWord ++ tailWord_1406242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406242).length < 2 ^ (prefixWord ++ tailWord_1406242).sum := by decide
  have hdescent : baseEnd_1406242 < baseStart_1406242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406284 : List Nat := [2, 2, 1, 3, 2, 11]
def baseStart_1406284 : Nat := 118140960795 + 1406284 * 2 ^ 59
def prefixEnd_1406284 : Nat := 4983230072969 + 3 ^ 40 * 1406284 * 2
def baseEnd_1406284 : Nat := 11886413641604627836751

theorem tailTrace_1406284 : CollatzResearch.WordTrace tailWord_1406284 prefixEnd_1406284 11886413641604627836751 := by
  unfold tailWord_1406284
  simp only [CollatzResearch.WordTrace]
  refine ⟨25645695618640358515532953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34194260824853811354043937 25645695618640358515532953)
  ·
    refine ⟨19234271713980268886649715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25645695618640358515532953 19234271713980268886649715)
    ·
      refine ⟨28851407570970403329974573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19234271713980268886649715 28851407570970403329974573)
      ·
        refine ⟨10819277839113901248740465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28851407570970403329974573 10819277839113901248740465)
        ·
          refine ⟨8114458379335425936555349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10819277839113901248740465 8114458379335425936555349)
          ·
            refine ⟨11886413641604627836751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8114458379335425936555349 11886413641604627836751)
            ·
              rfl

theorem cell21_1406284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 11].length) (baseStart_1406284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1406284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1406284 prefixEnd_1406284 := by exact prefixLift 1406284
  have htrace : WordTrace (prefixWord ++ tailWord_1406284) baseStart_1406284 baseEnd_1406284 := by
    simpa [prefixWord, tailWord_1406284, baseEnd_1406284] using wordTrace_append hprefix tailTrace_1406284
  have hstable : (prefixWord ++ tailWord_1406284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406284).length < 2 ^ (prefixWord ++ tailWord_1406284).sum := by decide
  have hdescent : baseEnd_1406284 < baseStart_1406284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406453 : List Nat := [1, 3, 5, 1, 1, 10]
def baseStart_1406453 : Nat := 118140960795 + 1406453 * 2 ^ 59
def prefixEnd_1406453 : Nat := 4983230072969 + 3 ^ 40 * 1406453 * 2
def baseEnd_1406453 : Nat := 11887842089845119010195

theorem tailTrace_1406453 : CollatzResearch.WordTrace tailWord_1406453 prefixEnd_1406453 11887842089845119010195 := by
  unfold tailWord_1406453
  simp only [CollatzResearch.WordTrace]
  refine ⟨51297555173668458893968013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34198370115778972595978675 51297555173668458893968013)
  ·
    refine ⟨19236583190125672085238005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51297555173668458893968013 19236583190125672085238005)
    ·
      refine ⟨1803429674074281757991063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19236583190125672085238005 1803429674074281757991063)
      ·
        refine ⟨2705144511111422636986595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1803429674074281757991063 2705144511111422636986595)
        ·
          refine ⟨4057716766667133955479893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2705144511111422636986595 4057716766667133955479893)
          ·
            refine ⟨11887842089845119010195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4057716766667133955479893 11887842089845119010195)
            ·
              rfl

theorem cell21_1406453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 10].length) (baseStart_1406453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1406453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1406453 prefixEnd_1406453 := by exact prefixLift 1406453
  have htrace : WordTrace (prefixWord ++ tailWord_1406453) baseStart_1406453 baseEnd_1406453 := by
    simpa [prefixWord, tailWord_1406453, baseEnd_1406453] using wordTrace_append hprefix tailTrace_1406453
  have hstable : (prefixWord ++ tailWord_1406453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406453).length < 2 ^ (prefixWord ++ tailWord_1406453).sum := by decide
  have hdescent : baseEnd_1406453 < baseStart_1406453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406515 : List Nat := [1, 1, 1, 2, 4, 5, 1, 2, 4]
def baseStart_1406515 : Nat := 118140960795 + 1406515 * 2 ^ 59
def prefixEnd_1406515 : Nat := 4983230072969 + 3 ^ 40 * 1406515 * 2
def baseEnd_1406515 : Nat := 320985885670519883241805

theorem tailTrace_1406515 : CollatzResearch.WordTrace tailWord_1406515 prefixEnd_1406515 320985885670519883241805 := by
  unfold tailWord_1406515
  simp only [CollatzResearch.WordTrace]
  refine ⟨51299816499443843482724999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34199877666295895655149999 51299816499443843482724999)
  ·
    refine ⟨76949724749165765224087499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51299816499443843482724999 76949724749165765224087499)
    ·
      refine ⟨115424587123748647836131249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76949724749165765224087499 115424587123748647836131249)
      ·
        refine ⟨86568440342811485877098437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115424587123748647836131249 86568440342811485877098437)
        ·
          refine ⟨16231582564277153601955957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86568440342811485877098437 16231582564277153601955957)
          ·
            refine ⟨1521710865400983150183371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16231582564277153601955957 1521710865400983150183371)
            ·
              refine ⟨2282566298101474725275057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1521710865400983150183371 2282566298101474725275057)
              ·
                refine ⟨1711924723576106043956293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2282566298101474725275057 1711924723576106043956293)
                ·
                  refine ⟨320985885670519883241805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1711924723576106043956293 320985885670519883241805)
                  ·
                    rfl

theorem cell21_1406515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 4].length) (baseStart_1406515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1406515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1406515 prefixEnd_1406515 := by exact prefixLift 1406515
  have htrace : WordTrace (prefixWord ++ tailWord_1406515) baseStart_1406515 baseEnd_1406515 := by
    simpa [prefixWord, tailWord_1406515, baseEnd_1406515] using wordTrace_append hprefix tailTrace_1406515
  have hstable : (prefixWord ++ tailWord_1406515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406515).length < 2 ^ (prefixWord ++ tailWord_1406515).sum := by decide
  have hdescent : baseEnd_1406515 < baseStart_1406515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406546 : List Nat := [3, 2, 2, 1, 2, 4, 2, 5]
def baseStart_1406546 : Nat := 118140960795 + 1406546 * 2 ^ 59
def prefixEnd_1406546 : Nat := 4983230072969 + 3 ^ 40 * 1406546 * 2
def baseEnd_1406546 : Nat := 106997653430956906075025

theorem tailTrace_1406546 : CollatzResearch.WordTrace tailWord_1406546 prefixEnd_1406546 106997653430956906075025 := by
  unfold tailWord_1406546
  simp only [CollatzResearch.WordTrace]
  refine ⟨12825236790582883944275873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34200631441554357184735661 12825236790582883944275873)
  ·
    refine ⟨9618927592937162958206905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12825236790582883944275873 9618927592937162958206905)
    ·
      refine ⟨7214195694702872218655179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9618927592937162958206905 7214195694702872218655179)
      ·
        refine ⟨10821293542054308327982769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7214195694702872218655179 10821293542054308327982769)
        ·
          refine ⟨8115970156540731245987077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10821293542054308327982769 8115970156540731245987077)
          ·
            refine ⟨1521744404351387108622577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8115970156540731245987077 1521744404351387108622577)
            ·
              refine ⟨1141308303263540331466933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1521744404351387108622577 1141308303263540331466933)
              ·
                refine ⟨106997653430956906075025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1141308303263540331466933 106997653430956906075025)
                ·
                  rfl

theorem cell21_1406546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 5].length) (baseStart_1406546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1406546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1406546 prefixEnd_1406546 := by exact prefixLift 1406546
  have htrace : WordTrace (prefixWord ++ tailWord_1406546) baseStart_1406546 baseEnd_1406546 := by
    simpa [prefixWord, tailWord_1406546, baseEnd_1406546] using wordTrace_append hprefix tailTrace_1406546
  have hstable : (prefixWord ++ tailWord_1406546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406546).length < 2 ^ (prefixWord ++ tailWord_1406546).sum := by decide
  have hdescent : baseEnd_1406546 < baseStart_1406546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406650 : List Nat := [3, 1, 1, 1, 2, 4, 2, 3, 4]
def baseStart_1406650 : Nat := 118140960795 + 1406650 * 2 ^ 59
def prefixEnd_1406650 : Nat := 4983230072969 + 3 ^ 40 * 1406650 * 2
def baseEnd_1406650 : Nat := 321016694509789648491529

theorem tailTrace_1406650 : CollatzResearch.WordTrace tailWord_1406650 prefixEnd_1406650 321016694509789648491529 := by
  unfold tailWord_1406650
  simp only [CollatzResearch.WordTrace]
  refine ⟨12826185088488690384722351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34203160235969841025926269 12826185088488690384722351)
  ·
    refine ⟨19239277632733035577083527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12826185088488690384722351 19239277632733035577083527)
    ·
      refine ⟨28858916449099553365625291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19239277632733035577083527 28858916449099553365625291)
      ·
        refine ⟨43288374673649330048437937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28858916449099553365625291 43288374673649330048437937)
        ·
          refine ⟨32466281005236997536328453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43288374673649330048437937 32466281005236997536328453)
          ·
            refine ⟨6087427688481937038061585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32466281005236997536328453 6087427688481937038061585)
            ·
              refine ⟨4565570766361452778546189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6087427688481937038061585 4565570766361452778546189)
              ·
                refine ⟨1712089037385544791954821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4565570766361452778546189 1712089037385544791954821)
                ·
                  refine ⟨321016694509789648491529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1712089037385544791954821 321016694509789648491529)
                  ·
                    rfl

theorem cell21_1406650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_1406650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1406650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1406650 prefixEnd_1406650 := by exact prefixLift 1406650
  have htrace : WordTrace (prefixWord ++ tailWord_1406650) baseStart_1406650 baseEnd_1406650 := by
    simpa [prefixWord, tailWord_1406650, baseEnd_1406650] using wordTrace_append hprefix tailTrace_1406650
  have hstable : (prefixWord ++ tailWord_1406650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406650).length < 2 ^ (prefixWord ++ tailWord_1406650).sum := by decide
  have hdescent : baseEnd_1406650 < baseStart_1406650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406760 : List Nat := [2, 1, 5, 1, 1, 4, 2, 1, 4]
def baseStart_1406760 : Nat := 118140960795 + 1406760 * 2 ^ 59
def prefixEnd_1406760 : Nat := 4983230072969 + 3 ^ 40 * 1406760 * 2
def baseEnd_1406760 : Nat := 321041798008453901657971

theorem tailTrace_1406760 : CollatzResearch.WordTrace tailWord_1406760 prefixEnd_1406760 321041798008453901657971 := by
  unfold tailWord_1406760
  simp only [CollatzResearch.WordTrace]
  refine ⟨25654376191778125162696867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34205834922370833550262489 25654376191778125162696867)
  ·
    refine ⟨38481564287667187744045301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25654376191778125162696867 38481564287667187744045301)
    ·
      refine ⟨3607646651968798851004247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38481564287667187744045301 3607646651968798851004247)
      ·
        refine ⟨5411469977953198276506371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3607646651968798851004247 5411469977953198276506371)
        ·
          refine ⟨8117204966929797414759557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5411469977953198276506371 8117204966929797414759557)
          ·
            refine ⟨1521975931299337015267417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8117204966929797414759557 1521975931299337015267417)
            ·
              refine ⟨1141481948474502761450563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1521975931299337015267417 1141481948474502761450563)
              ·
                refine ⟨1712222922711754142175845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1141481948474502761450563 1712222922711754142175845)
                ·
                  refine ⟨321041798008453901657971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1712222922711754142175845 321041798008453901657971)
                  ·
                    rfl

theorem cell21_1406760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 4].length) (baseStart_1406760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1406760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1406760 prefixEnd_1406760 := by exact prefixLift 1406760
  have htrace : WordTrace (prefixWord ++ tailWord_1406760) baseStart_1406760 baseEnd_1406760 := by
    simpa [prefixWord, tailWord_1406760, baseEnd_1406760] using wordTrace_append hprefix tailTrace_1406760
  have hstable : (prefixWord ++ tailWord_1406760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406760).length < 2 ^ (prefixWord ++ tailWord_1406760).sum := by decide
  have hdescent : baseEnd_1406760 < baseStart_1406760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406802 : List Nat := [3, 2, 2, 1, 1, 3, 1, 4, 4]
def baseStart_1406802 : Nat := 118140960795 + 1406802 * 2 ^ 59
def prefixEnd_1406802 : Nat := 4983230072969 + 3 ^ 40 * 1406802 * 2
def baseEnd_1406802 : Nat := 321051382980671161957885

theorem tailTrace_1406802 : CollatzResearch.WordTrace tailWord_1406802 prefixEnd_1406802 321051382980671161957885 := by
  unfold tailWord_1406802
  simp only [CollatzResearch.WordTrace]
  refine ⟨12827571062351022874605665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34206856166269394332281773 12827571062351022874605665)
  ·
    refine ⟨9620678296763267155954249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12827571062351022874605665 9620678296763267155954249)
    ·
      refine ⟨7215508722572450366965687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9620678296763267155954249 7215508722572450366965687)
      ·
        refine ⟨10823263083858675550448531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7215508722572450366965687 10823263083858675550448531)
        ·
          refine ⟨16234894625788013325672797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10823263083858675550448531 16234894625788013325672797)
          ·
            refine ⟨6088085484670504997127299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16234894625788013325672797 6088085484670504997127299)
            ·
              refine ⟨9132128227005757495690949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6088085484670504997127299 9132128227005757495690949)
              ·
                refine ⟨1712274042563579530442053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9132128227005757495690949 1712274042563579530442053)
                ·
                  refine ⟨321051382980671161957885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1712274042563579530442053 321051382980671161957885)
                  ·
                    rfl

theorem cell21_1406802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_1406802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1406802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1406802 prefixEnd_1406802 := by exact prefixLift 1406802
  have htrace : WordTrace (prefixWord ++ tailWord_1406802) baseStart_1406802 baseEnd_1406802 := by
    simpa [prefixWord, tailWord_1406802, baseEnd_1406802] using wordTrace_append hprefix tailTrace_1406802
  have hstable : (prefixWord ++ tailWord_1406802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406802).length < 2 ^ (prefixWord ++ tailWord_1406802).sum := by decide
  have hdescent : baseEnd_1406802 < baseStart_1406802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406805 : List Nat := [1, 3, 2, 2, 2, 2, 4, 2, 3]
def baseStart_1406805 : Nat := 118140960795 + 1406805 * 2 ^ 59
def prefixEnd_1406805 : Nat := 4983230072969 + 3 ^ 40 * 1406805 * 2
def baseEnd_1406805 : Nat := 321052067621543823407879

theorem tailTrace_1406805 : CollatzResearch.WordTrace tailWord_1406805 prefixEnd_1406805 321052067621543823407879 := by
  unfold tailWord_1406805
  simp only [CollatzResearch.WordTrace]
  refine ⟨51310393668393223010781869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34206929112262148673854579 51310393668393223010781869)
  ·
    refine ⟨19241397625647458629043201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51310393668393223010781869 19241397625647458629043201)
    ·
      refine ⟨14431048219235593971782401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19241397625647458629043201 14431048219235593971782401)
      ·
        refine ⟨10823286164426695478836801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14431048219235593971782401 10823286164426695478836801)
        ·
          refine ⟨8117464623320021609127601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10823286164426695478836801 8117464623320021609127601)
          ·
            refine ⟨6088098467490016206845701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8117464623320021609127601 6088098467490016206845701)
            ·
              refine ⟨1141518462654378038783569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6088098467490016206845701 1141518462654378038783569)
              ·
                refine ⟨856138846990783529087677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1141518462654378038783569 856138846990783529087677)
                ·
                  refine ⟨321052067621543823407879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 856138846990783529087677 321052067621543823407879)
                  ·
                    rfl

theorem cell21_1406805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2, 3].length) (baseStart_1406805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1406805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1406805 prefixEnd_1406805 := by exact prefixLift 1406805
  have htrace : WordTrace (prefixWord ++ tailWord_1406805) baseStart_1406805 baseEnd_1406805 := by
    simpa [prefixWord, tailWord_1406805, baseEnd_1406805] using wordTrace_append hprefix tailTrace_1406805
  have hstable : (prefixWord ++ tailWord_1406805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406805).length < 2 ^ (prefixWord ++ tailWord_1406805).sum := by decide
  have hdescent : baseEnd_1406805 < baseStart_1406805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406816 : List Nat := [2, 1, 1, 3, 3, 2, 3, 6]
def baseStart_1406816 : Nat := 118140960795 + 1406816 * 2 ^ 59
def prefixEnd_1406816 : Nat := 4983230072969 + 3 ^ 40 * 1406816 * 2
def baseEnd_1406816 : Nat := 107018192657136749574841

theorem tailTrace_1406816 : CollatzResearch.WordTrace tailWord_1406816 prefixEnd_1406816 107018192657136749574841 := by
  unfold tailWord_1406816
  simp only [CollatzResearch.WordTrace]
  refine ⟨25655397435676685944716151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34207196580902247926288201 25655397435676685944716151)
  ·
    refine ⟨38483096153515028917074227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25655397435676685944716151 38483096153515028917074227)
    ·
      refine ⟨57724644230272543375611341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38483096153515028917074227 57724644230272543375611341)
      ·
        refine ⟨21646741586352203765854253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57724644230272543375611341 21646741586352203765854253)
        ·
          refine ⟨8117528094882076412195345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21646741586352203765854253 8117528094882076412195345)
          ·
            refine ⟨6088146071161557309146509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8117528094882076412195345 6088146071161557309146509)
            ·
              refine ⟨2283054776685583990929941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6088146071161557309146509 2283054776685583990929941)
              ·
                refine ⟨107018192657136749574841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2283054776685583990929941 107018192657136749574841)
                ·
                  rfl

theorem cell21_1406816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 6].length) (baseStart_1406816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1406816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1406816 prefixEnd_1406816 := by exact prefixLift 1406816
  have htrace : WordTrace (prefixWord ++ tailWord_1406816) baseStart_1406816 baseEnd_1406816 := by
    simpa [prefixWord, tailWord_1406816, baseEnd_1406816] using wordTrace_append hprefix tailTrace_1406816
  have hstable : (prefixWord ++ tailWord_1406816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406816).length < 2 ^ (prefixWord ++ tailWord_1406816).sum := by decide
  have hdescent : baseEnd_1406816 < baseStart_1406816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406870 : List Nat := [5, 3, 1, 1, 2, 1, 3, 1, 4]
def baseStart_1406870 : Nat := 118140960795 + 1406870 * 2 ^ 59
def prefixEnd_1406870 : Nat := 4983230072969 + 3 ^ 40 * 1406870 * 2
def baseEnd_1406870 : Nat := 321066901507118154824413

theorem tailTrace_1406870 : CollatzResearch.WordTrace tailWord_1406870 prefixEnd_1406870 321066901507118154824413 := by
  unfold tailWord_1406870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3207047775822358694493629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34208509608771826074598709 3207047775822358694493629)
  ·
    refine ⟨1202642915933384510435111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3207047775822358694493629 1202642915933384510435111)
    ·
      refine ⟨1803964373900076765652667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1202642915933384510435111 1803964373900076765652667)
      ·
        refine ⟨2705946560850115148479001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1803964373900076765652667 2705946560850115148479001)
        ·
          refine ⟨2029459920637586361359251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2705946560850115148479001 2029459920637586361359251)
          ·
            refine ⟨3044189880956379542038877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2029459920637586361359251 3044189880956379542038877)
            ·
              refine ⟨1141571205358642328264579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3044189880956379542038877 1141571205358642328264579)
              ·
                refine ⟨1712356808037963492396869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1141571205358642328264579 1712356808037963492396869)
                ·
                  refine ⟨321066901507118154824413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1712356808037963492396869 321066901507118154824413)
                  ·
                    rfl

theorem cell21_1406870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_1406870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1406870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1406870 prefixEnd_1406870 := by exact prefixLift 1406870
  have htrace : WordTrace (prefixWord ++ tailWord_1406870) baseStart_1406870 baseEnd_1406870 := by
    simpa [prefixWord, tailWord_1406870, baseEnd_1406870] using wordTrace_append hprefix tailTrace_1406870
  have hstable : (prefixWord ++ tailWord_1406870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406870).length < 2 ^ (prefixWord ++ tailWord_1406870).sum := by decide
  have hdescent : baseEnd_1406870 < baseStart_1406870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406974 : List Nat := [4, 2, 2, 2, 1, 1, 4, 2, 3]
def baseStart_1406974 : Nat := 118140960795 + 1406974 * 2 ^ 59
def prefixEnd_1406974 : Nat := 4983230072969 + 3 ^ 40 * 1406974 * 2
def baseEnd_1406974 : Nat := 321090635724037085090867

theorem tailTrace_1406974 : CollatzResearch.WordTrace tailWord_1406974 prefixEnd_1406974 321090635724037085090867 := by
  unfold tailWord_1406974
  simp only [CollatzResearch.WordTrace]
  refine ⟨6414569700597620609210497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34211038403187309915789317 6414569700597620609210497)
  ·
    refine ⟨4810927275448215456907873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6414569700597620609210497 4810927275448215456907873)
    ·
      refine ⟨3608195456586161592680905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4810927275448215456907873 3608195456586161592680905)
      ·
        refine ⟨2706146592439621194510679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3608195456586161592680905 2706146592439621194510679)
        ·
          refine ⟨4059219888659431791766019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2706146592439621194510679 4059219888659431791766019)
          ·
            refine ⟨6088829832989147687649029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4059219888659431791766019 6088829832989147687649029)
            ·
              refine ⟨1141655593685465191434193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6088829832989147687649029 1141655593685465191434193)
              ·
                refine ⟨856241695264098893575645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1141655593685465191434193 856241695264098893575645)
                ·
                  refine ⟨321090635724037085090867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 856241695264098893575645 321090635724037085090867)
                  ·
                    rfl

theorem cell21_1406974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_1406974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1406974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1406974 prefixEnd_1406974 := by exact prefixLift 1406974
  have htrace : WordTrace (prefixWord ++ tailWord_1406974) baseStart_1406974 baseEnd_1406974 := by
    simpa [prefixWord, tailWord_1406974, baseEnd_1406974] using wordTrace_append hprefix tailTrace_1406974
  have hstable : (prefixWord ++ tailWord_1406974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406974).length < 2 ^ (prefixWord ++ tailWord_1406974).sum := by decide
  have hdescent : baseEnd_1406974 < baseStart_1406974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407030 : List Nat := [5, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_1407030 : Nat := 118140960795 + 1407030 * 2 ^ 59
def prefixEnd_1407030 : Nat := 4983230072969 + 3 ^ 40 * 1407030 * 2
def baseEnd_1407030 : Nat := 321103415686993432157419

theorem tailTrace_1407030 : CollatzResearch.WordTrace tailWord_1407030 prefixEnd_1407030 321103415686993432157419 := by
  unfold tailWord_1407030
  simp only [CollatzResearch.WordTrace]
  refine ⟨3207412505786130402357659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34212400061718724291815029 3207412505786130402357659)
  ·
    refine ⟨4811118758679195603536489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3207412505786130402357659 4811118758679195603536489)
    ·
      refine ⟨3608339069009396702652367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4811118758679195603536489 3608339069009396702652367)
      ·
        refine ⟨5412508603514095053978551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3608339069009396702652367 5412508603514095053978551)
        ·
          refine ⟨8118762905271142580967827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5412508603514095053978551 8118762905271142580967827)
          ·
            refine ⟨12178144357906713871451741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8118762905271142580967827 12178144357906713871451741)
            ·
              refine ⟨4566804134215017701794403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12178144357906713871451741 4566804134215017701794403)
              ·
                refine ⟨6850206201322526552691605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4566804134215017701794403 6850206201322526552691605)
                ·
                  refine ⟨321103415686993432157419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6850206201322526552691605 321103415686993432157419)
                  ·
                    rfl

theorem cell21_1407030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_1407030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1407030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1407030 prefixEnd_1407030 := by exact prefixLift 1407030
  have htrace : WordTrace (prefixWord ++ tailWord_1407030) baseStart_1407030 baseEnd_1407030 := by
    simpa [prefixWord, tailWord_1407030, baseEnd_1407030] using wordTrace_append hprefix tailTrace_1407030
  have hstable : (prefixWord ++ tailWord_1407030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407030).length < 2 ^ (prefixWord ++ tailWord_1407030).sum := by decide
  have hdescent : baseEnd_1407030 < baseStart_1407030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407061 : List Nat := [1, 3, 2, 2, 1, 5, 2, 5]
def baseStart_1407061 : Nat := 118140960795 + 1407061 * 2 ^ 59
def prefixEnd_1407061 : Nat := 4983230072969 + 3 ^ 40 * 1407061 * 2
def baseEnd_1407061 : Nat := 107036830103114755713563

theorem tailTrace_1407061 : CollatzResearch.WordTrace tailWord_1407061 prefixEnd_1407061 107036830103114755713563 := by
  unfold tailWord_1407061
  simp only [CollatzResearch.WordTrace]
  refine ⟨51319730755465778732101037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34213153836977185821400691 51319730755465778732101037)
  ·
    refine ⟨19244899033299667024537889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51319730755465778732101037 19244899033299667024537889)
    ·
      refine ⟨14433674274974750268403417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19244899033299667024537889 14433674274974750268403417)
      ·
        refine ⟨10825255706231062701302563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14433674274974750268403417 10825255706231062701302563)
        ·
          refine ⟨16237883559346594051953845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10825255706231062701302563 16237883559346594051953845)
          ·
            refine ⟨1522301583688743192370673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16237883559346594051953845 1522301583688743192370673)
            ·
              refine ⟨1141726187766557394278005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1522301583688743192370673 1141726187766557394278005)
              ·
                refine ⟨107036830103114755713563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1141726187766557394278005 107036830103114755713563)
                ·
                  rfl

theorem cell21_1407061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 5].length) (baseStart_1407061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1407061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1407061 prefixEnd_1407061 := by exact prefixLift 1407061
  have htrace : WordTrace (prefixWord ++ tailWord_1407061) baseStart_1407061 baseEnd_1407061 := by
    simpa [prefixWord, tailWord_1407061, baseEnd_1407061] using wordTrace_append hprefix tailTrace_1407061
  have hstable : (prefixWord ++ tailWord_1407061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407061).length < 2 ^ (prefixWord ++ tailWord_1407061).sum := by decide
  have hdescent : baseEnd_1407061 < baseStart_1407061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407089 : List Nat := [1, 2, 2, 2, 1, 1, 4, 4, 4]
def baseStart_1407089 : Nat := 118140960795 + 1407089 * 2 ^ 59
def prefixEnd_1407089 : Nat := 4983230072969 + 3 ^ 40 * 1407089 * 2
def baseEnd_1407089 : Nat := 321116880290822440673965

theorem tailTrace_1407089 : CollatzResearch.WordTrace tailWord_1407089 prefixEnd_1407089 321116880290822440673965 := by
  unfold tailWord_1407089
  simp only [CollatzResearch.WordTrace]
  refine ⟨51320751999364339514120321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34213834666242893009413547 51320751999364339514120321)
  ·
    refine ⟨38490563999523254635590241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51320751999364339514120321 38490563999523254635590241)
    ·
      refine ⟨28867922999642440976692681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38490563999523254635590241 28867922999642440976692681)
      ·
        refine ⟨21650942249731830732519511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28867922999642440976692681 21650942249731830732519511)
        ·
          refine ⟨32476413374597746098779267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21650942249731830732519511 32476413374597746098779267)
          ·
            refine ⟨48714620061896619148168901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32476413374597746098779267 48714620061896619148168901)
            ·
              refine ⟨9133991261605616090281669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48714620061896619148168901 9133991261605616090281669)
              ·
                refine ⟨1712623361551053016927813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9133991261605616090281669 1712623361551053016927813)
                ·
                  refine ⟨321116880290822440673965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1712623361551053016927813 321116880290822440673965)
                  ·
                    rfl

theorem cell21_1407089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 4].length) (baseStart_1407089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1407089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1407089 prefixEnd_1407089 := by exact prefixLift 1407089
  have htrace : WordTrace (prefixWord ++ tailWord_1407089) baseStart_1407089 baseEnd_1407089 := by
    simpa [prefixWord, tailWord_1407089, baseEnd_1407089] using wordTrace_append hprefix tailTrace_1407089
  have hstable : (prefixWord ++ tailWord_1407089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407089).length < 2 ^ (prefixWord ++ tailWord_1407089).sum := by decide
  have hdescent : baseEnd_1407089 < baseStart_1407089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407143 : List Nat := [1, 1, 6, 2, 3, 1, 2, 2, 3]
def baseStart_1407143 : Nat := 118140960795 + 1407143 * 2 ^ 59
def prefixEnd_1407143 : Nat := 4983230072969 + 3 ^ 40 * 1407143 * 2
def baseEnd_1407143 : Nat := 321129203826530346773855

theorem tailTrace_1407143 : CollatzResearch.WordTrace tailWord_1407143 prefixEnd_1407143 321129203826530346773855 := by
  unfold tailWord_1407143
  simp only [CollatzResearch.WordTrace]
  refine ⟨51322721541168706736586083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34215147694112471157724055 51322721541168706736586083)
  ·
    refine ⟨76984082311753060104879125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51322721541168706736586083 76984082311753060104879125)
    ·
      refine ⟨3608628858363424692416209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 76984082311753060104879125 3608628858363424692416209)
      ·
        refine ⟨2706471643772568519312157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3608628858363424692416209 2706471643772568519312157)
        ·
          refine ⟨1014926866414713194742059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2706471643772568519312157 1014926866414713194742059)
          ·
            refine ⟨1522390299622069792113089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1014926866414713194742059 1522390299622069792113089)
            ·
              refine ⟨1141792724716552344084817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1522390299622069792113089 1141792724716552344084817)
              ·
                refine ⟨856344543537414258063613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1141792724716552344084817 856344543537414258063613)
                ·
                  refine ⟨321129203826530346773855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 856344543537414258063613 321129203826530346773855)
                  ·
                    rfl

theorem cell21_1407143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2, 3].length) (baseStart_1407143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1407143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1407143 prefixEnd_1407143 := by exact prefixLift 1407143
  have htrace : WordTrace (prefixWord ++ tailWord_1407143) baseStart_1407143 baseEnd_1407143 := by
    simpa [prefixWord, tailWord_1407143, baseEnd_1407143] using wordTrace_append hprefix tailTrace_1407143
  have hstable : (prefixWord ++ tailWord_1407143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407143).length < 2 ^ (prefixWord ++ tailWord_1407143).sum := by decide
  have hdescent : baseEnd_1407143 < baseStart_1407143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407148 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 10]
def baseStart_1407148 : Nat := 118140960795 + 1407148 * 2 ^ 59
def prefixEnd_1407148 : Nat := 4983230072969 + 3 ^ 40 * 1407148 * 2
def baseEnd_1407148 : Nat := 321130344894651449190511

theorem tailTrace_1407148 : CollatzResearch.WordTrace tailWord_1407148 prefixEnd_1407148 321130344894651449190511 := by
  unfold tailWord_1407148
  simp only [CollatzResearch.WordTrace]
  refine ⟨25661451953075296295259049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34215269270767061727012065 25661451953075296295259049)
  ·
    refine ⟨19246088964806472221444287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25661451953075296295259049 19246088964806472221444287)
    ·
      refine ⟨28869133447209708332166431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19246088964806472221444287 28869133447209708332166431)
      ·
        refine ⟨43303700170814562498249647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28869133447209708332166431 43303700170814562498249647)
        ·
          refine ⟨64955550256221843747374471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43303700170814562498249647 64955550256221843747374471)
          ·
            refine ⟨97433325384332765621061707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64955550256221843747374471 97433325384332765621061707)
            ·
              refine ⟨146149988076499148431592561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97433325384332765621061707 146149988076499148431592561)
              ·
                refine ⟨109612491057374361323694421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146149988076499148431592561 109612491057374361323694421)
                ·
                  refine ⟨321130344894651449190511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 109612491057374361323694421 321130344894651449190511)
                  ·
                    rfl

theorem cell21_1407148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_1407148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1407148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1407148 prefixEnd_1407148 := by exact prefixLift 1407148
  have htrace : WordTrace (prefixWord ++ tailWord_1407148) baseStart_1407148 baseEnd_1407148 := by
    simpa [prefixWord, tailWord_1407148, baseEnd_1407148] using wordTrace_append hprefix tailTrace_1407148
  have hstable : (prefixWord ++ tailWord_1407148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407148).length < 2 ^ (prefixWord ++ tailWord_1407148).sum := by decide
  have hdescent : baseEnd_1407148 < baseStart_1407148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407202 : List Nat := [3, 3, 4, 1, 1, 1, 2, 1, 5]
def baseStart_1407202 : Nat := 118140960795 + 1407202 * 2 ^ 59
def prefixEnd_1407202 : Nat := 4983230072969 + 3 ^ 40 * 1407202 * 2
def baseEnd_1407202 : Nat := 321142668430359355290401

theorem tailTrace_1407202 : CollatzResearch.WordTrace tailWord_1407202 prefixEnd_1407202 321142668430359355290401 := by
  unfold tailWord_1407202
  simp only [CollatzResearch.WordTrace]
  refine ⟨12831218361988739953245965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34216582298636639875322573 12831218361988739953245965)
  ·
    refine ⟨4811706885745777482467237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12831218361988739953245965 4811706885745777482467237)
    ·
      refine ⟨902195041077333277962607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4811706885745777482467237 902195041077333277962607)
      ·
        refine ⟨1353292561615999916943911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 902195041077333277962607 1353292561615999916943911)
        ·
          refine ⟨2029938842423999875415867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1353292561615999916943911 2029938842423999875415867)
          ·
            refine ⟨3044908263635999813123801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2029938842423999875415867 3044908263635999813123801)
            ·
              refine ⟨2283681197726999859842851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3044908263635999813123801 2283681197726999859842851)
              ·
                refine ⟨3425521796590499789764277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2283681197726999859842851 3425521796590499789764277)
                ·
                  refine ⟨321142668430359355290401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3425521796590499789764277 321142668430359355290401)
                  ·
                    rfl

theorem cell21_1407202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_1407202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1407202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1407202 prefixEnd_1407202 := by exact prefixLift 1407202
  have htrace : WordTrace (prefixWord ++ tailWord_1407202) baseStart_1407202 baseEnd_1407202 := by
    simpa [prefixWord, tailWord_1407202, baseEnd_1407202] using wordTrace_append hprefix tailTrace_1407202
  have hstable : (prefixWord ++ tailWord_1407202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407202).length < 2 ^ (prefixWord ++ tailWord_1407202).sum := by decide
  have hdescent : baseEnd_1407202 < baseStart_1407202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407255 : List Nat := [1, 1, 3, 4, 1, 2, 9]
def baseStart_1407255 : Nat := 118140960795 + 1407255 * 2 ^ 59
def prefixEnd_1407255 : Nat := 4983230072969 + 3 ^ 40 * 1407255 * 2
def baseEnd_1407255 : Nat := 35683862639160337878551

theorem tailTrace_1407255 : CollatzResearch.WordTrace tailWord_1407255 prefixEnd_1407255 35683862639160337878551 := by
  unfold tailWord_1407255
  simp only [CollatzResearch.WordTrace]
  refine ⟨51326806516762949864663219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34217871011175299909775479 51326806516762949864663219)
  ·
    refine ⟨76990209775144424796994829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51326806516762949864663219 76990209775144424796994829)
    ·
      refine ⟨28871328665679159298873061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76990209775144424796994829 28871328665679159298873061)
      ·
        refine ⟨5413374124814842368538699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28871328665679159298873061 5413374124814842368538699)
        ·
          refine ⟨8120061187222263552808049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5413374124814842368538699 8120061187222263552808049)
          ·
            refine ⟨6090045890416697664606037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8120061187222263552808049 6090045890416697664606037)
            ·
              refine ⟨35683862639160337878551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6090045890416697664606037 35683862639160337878551)
              ·
                rfl

theorem cell21_1407255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 9].length) (baseStart_1407255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1407255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1407255 prefixEnd_1407255 := by exact prefixLift 1407255
  have htrace : WordTrace (prefixWord ++ tailWord_1407255) baseStart_1407255 baseEnd_1407255 := by
    simpa [prefixWord, tailWord_1407255, baseEnd_1407255] using wordTrace_append hprefix tailTrace_1407255
  have hstable : (prefixWord ++ tailWord_1407255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407255).length < 2 ^ (prefixWord ++ tailWord_1407255).sum := by decide
  have hdescent : baseEnd_1407255 < baseStart_1407255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407261 : List Nat := [1, 4, 2, 3, 3, 1, 1, 1, 5]
def baseStart_1407261 : Nat := 118140960795 + 1407261 * 2 ^ 59
def prefixEnd_1407261 : Nat := 4983230072969 + 3 ^ 40 * 1407261 * 2
def baseEnd_1407261 : Nat := 321156133034188363806947

theorem tailTrace_1407261 : CollatzResearch.WordTrace tailWord_1407261 prefixEnd_1407261 321156133034188363806947 := by
  unfold tailWord_1407261
  simp only [CollatzResearch.WordTrace]
  refine ⟨51327025354741212889381637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34218016903160808592921091 51327025354741212889381637)
  ·
    refine ⟨9623817254013977416759057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51327025354741212889381637 9623817254013977416759057)
    ·
      refine ⟨7217862940510483062569293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9623817254013977416759057 7217862940510483062569293)
      ·
        refine ⟨2706698602691431148463485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7217862940510483062569293 2706698602691431148463485)
        ·
          refine ⟨1015011976009286680673807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2706698602691431148463485 1015011976009286680673807)
          ·
            refine ⟨1522517964013930021010711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1015011976009286680673807 1522517964013930021010711)
            ·
              refine ⟨2283776946020895031516067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1522517964013930021010711 2283776946020895031516067)
              ·
                refine ⟨3425665419031342547274101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2283776946020895031516067 3425665419031342547274101)
                ·
                  refine ⟨321156133034188363806947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3425665419031342547274101 321156133034188363806947)
                  ·
                    rfl

theorem cell21_1407261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_1407261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1407261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1407261 prefixEnd_1407261 := by exact prefixLift 1407261
  have htrace : WordTrace (prefixWord ++ tailWord_1407261) baseStart_1407261 baseEnd_1407261 := by
    simpa [prefixWord, tailWord_1407261, baseEnd_1407261] using wordTrace_append hprefix tailTrace_1407261
  have hstable : (prefixWord ++ tailWord_1407261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407261).length < 2 ^ (prefixWord ++ tailWord_1407261).sum := by decide
  have hdescent : baseEnd_1407261 < baseStart_1407261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407303 : List Nat := [1, 1, 4, 1, 2, 2, 2, 5, 3]
def baseStart_1407303 : Nat := 118140960795 + 1407303 * 2 ^ 59
def prefixEnd_1407303 : Nat := 4983230072969 + 3 ^ 40 * 1407303 * 2
def baseEnd_1407303 : Nat := 321165718006405624106861

theorem tailTrace_1407303 : CollatzResearch.WordTrace tailWord_1407303 prefixEnd_1407303 321165718006405624106861 := by
  unfold tailWord_1407303
  simp only [CollatzResearch.WordTrace]
  refine ⟨51328557220589054062410563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34219038147059369374940375 51328557220589054062410563)
  ·
    refine ⟨76992835830883581093615845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51328557220589054062410563 76992835830883581093615845)
    ·
      refine ⟨14436156718290671455052971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76992835830883581093615845 14436156718290671455052971)
      ·
        refine ⟨21654235077436007182579457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14436156718290671455052971 21654235077436007182579457)
        ·
          refine ⟨16240676308077005386934593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21654235077436007182579457 16240676308077005386934593)
          ·
            refine ⟨12180507231057754040200945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16240676308077005386934593 12180507231057754040200945)
            ·
              refine ⟨9135380423293315530150709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12180507231057754040200945 9135380423293315530150709)
              ·
                refine ⟨856441914683748330951629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9135380423293315530150709 856441914683748330951629)
                ·
                  refine ⟨321165718006405624106861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 856441914683748330951629 321165718006405624106861)
                  ·
                    rfl

theorem cell21_1407303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5, 3].length) (baseStart_1407303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1407303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1407303 prefixEnd_1407303 := by exact prefixLift 1407303
  have htrace : WordTrace (prefixWord ++ tailWord_1407303) baseStart_1407303 baseEnd_1407303 := by
    simpa [prefixWord, tailWord_1407303, baseEnd_1407303] using wordTrace_append hprefix tailTrace_1407303
  have hstable : (prefixWord ++ tailWord_1407303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407303).length < 2 ^ (prefixWord ++ tailWord_1407303).sum := by decide
  have hdescent : baseEnd_1407303 < baseStart_1407303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407413 : List Nat := [1, 3, 3, 2, 3, 2, 1, 3, 3]
def baseStart_1407413 : Nat := 118140960795 + 1407413 * 2 ^ 59
def prefixEnd_1407413 : Nat := 4983230072969 + 3 ^ 40 * 1407413 * 2
def baseEnd_1407413 : Nat := 321190821505069877273303

theorem tailTrace_1407413 : CollatzResearch.WordTrace tailWord_1407413 prefixEnd_1407413 321190821505069877273303 := by
  unfold tailWord_1407413
  simp only [CollatzResearch.WordTrace]
  refine ⟨51332569250190542848914893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34221712833460361899276595 51332569250190542848914893)
  ·
    refine ⟨19249713468821453568343085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51332569250190542848914893 19249713468821453568343085)
    ·
      refine ⟨7218642550808045088128657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19249713468821453568343085 7218642550808045088128657)
      ·
        refine ⟨5413981913106033816096493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7218642550808045088128657 5413981913106033816096493)
        ·
          refine ⟨2030243217414762681036185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5413981913106033816096493 2030243217414762681036185)
          ·
            refine ⟨1522682413061072010777139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2030243217414762681036185 1522682413061072010777139)
            ·
              refine ⟨2284023619591608016165709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1522682413061072010777139 2284023619591608016165709)
              ·
                refine ⟨856508857346853006062141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2284023619591608016165709 856508857346853006062141)
                ·
                  refine ⟨321190821505069877273303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 856508857346853006062141 321190821505069877273303)
                  ·
                    rfl

theorem cell21_1407413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3, 3].length) (baseStart_1407413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1407413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1407413 prefixEnd_1407413 := by exact prefixLift 1407413
  have htrace : WordTrace (prefixWord ++ tailWord_1407413) baseStart_1407413 baseEnd_1407413 := by
    simpa [prefixWord, tailWord_1407413, baseEnd_1407413] using wordTrace_append hprefix tailTrace_1407413
  have hstable : (prefixWord ++ tailWord_1407413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407413).length < 2 ^ (prefixWord ++ tailWord_1407413).sum := by decide
  have hdescent : baseEnd_1407413 < baseStart_1407413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407489 : List Nat := [1, 2, 4, 1, 3, 3, 2, 2, 3]
def baseStart_1407489 : Nat := 118140960795 + 1407489 * 2 ^ 59
def prefixEnd_1407489 : Nat := 4983230072969 + 3 ^ 40 * 1407489 * 2
def baseEnd_1407489 : Nat := 321208165740510634006481

theorem tailTrace_1407489 : CollatzResearch.WordTrace tailWord_1407489 prefixEnd_1407489 321208165740510634006481 := by
  unfold tailWord_1407489
  simp only [CollatzResearch.WordTrace]
  refine ⟨51335341197915207828681521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34223560798610138552454347 51335341197915207828681521)
  ·
    refine ⟨38501505898436405871511141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51335341197915207828681521 38501505898436405871511141)
    ·
      refine ⟨7219032355956826100908339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38501505898436405871511141 7219032355956826100908339)
      ·
        refine ⟨10828548533935239151362509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7219032355956826100908339 10828548533935239151362509)
        ·
          refine ⟨4060705700225714681760941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10828548533935239151362509 4060705700225714681760941)
          ·
            refine ⟨1522764637584643005660353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4060705700225714681760941 1522764637584643005660353)
            ·
              refine ⟨1142073478188482254245265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1522764637584643005660353 1142073478188482254245265)
              ·
                refine ⟨856555108641361690683949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1142073478188482254245265 856555108641361690683949)
                ·
                  refine ⟨321208165740510634006481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 856555108641361690683949 321208165740510634006481)
                  ·
                    rfl

theorem cell21_1407489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2, 3].length) (baseStart_1407489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1407489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1407489 prefixEnd_1407489 := by exact prefixLift 1407489
  have htrace : WordTrace (prefixWord ++ tailWord_1407489) baseStart_1407489 baseEnd_1407489 := by
    simpa [prefixWord, tailWord_1407489, baseEnd_1407489] using wordTrace_append hprefix tailTrace_1407489
  have hstable : (prefixWord ++ tailWord_1407489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407489).length < 2 ^ (prefixWord ++ tailWord_1407489).sum := by decide
  have hdescent : baseEnd_1407489 < baseStart_1407489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407500 : List Nat := [2, 2, 1, 2, 4, 3, 1, 6]
def baseStart_1407500 : Nat := 118140960795 + 1407500 * 2 ^ 59
def prefixEnd_1407500 : Nat := 4983230072969 + 3 ^ 40 * 1407500 * 2
def baseEnd_1407500 : Nat := 107070225363459019774375

theorem tailTrace_1407500 : CollatzResearch.WordTrace tailWord_1407500 prefixEnd_1407500 107070225363459019774375 := by
  unfold tailWord_1407500
  simp only [CollatzResearch.WordTrace]
  refine ⟨25667871200437678353665977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34223828267250237804887969 25667871200437678353665977)
  ·
    refine ⟨19250903400328258765249483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25667871200437678353665977 19250903400328258765249483)
    ·
      refine ⟨28876355100492388147874225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19250903400328258765249483 28876355100492388147874225)
      ·
        refine ⟨21657266325369291110905669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28876355100492388147874225 21657266325369291110905669)
        ·
          refine ⟨4060737436006742083294813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21657266325369291110905669 4060737436006742083294813)
          ·
            refine ⟨1522776538502528281235555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4060737436006742083294813 1522776538502528281235555)
            ·
              refine ⟨2284164807753792421853333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1522776538502528281235555 2284164807753792421853333)
              ·
                refine ⟨107070225363459019774375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2284164807753792421853333 107070225363459019774375)
                ·
                  rfl

theorem cell21_1407500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 6].length) (baseStart_1407500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1407500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1407500 prefixEnd_1407500 := by exact prefixLift 1407500
  have htrace : WordTrace (prefixWord ++ tailWord_1407500) baseStart_1407500 baseEnd_1407500 := by
    simpa [prefixWord, tailWord_1407500, baseEnd_1407500] using wordTrace_append hprefix tailTrace_1407500
  have hstable : (prefixWord ++ tailWord_1407500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407500).length < 2 ^ (prefixWord ++ tailWord_1407500).sum := by decide
  have hdescent : baseEnd_1407500 < baseStart_1407500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407562 : List Nat := [3, 1, 2, 1, 1, 5, 3, 1, 4]
def baseStart_1407562 : Nat := 118140960795 + 1407562 * 2 ^ 59
def prefixEnd_1407562 : Nat := 4983230072969 + 3 ^ 40 * 1407562 * 2
def baseEnd_1407562 : Nat := 321224825335078729289665

theorem tailTrace_1407562 : CollatzResearch.WordTrace tailWord_1407562 prefixEnd_1407562 321224825335078729289665 := by
  unfold tailWord_1407562
  simp only [CollatzResearch.WordTrace]
  refine ⟨12834500931662685324022235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34225335817767160864059293 12834500931662685324022235)
  ·
    refine ⟨19251751397494027986033353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12834500931662685324022235 19251751397494027986033353)
    ·
      refine ⟨14438813548120520989525015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19251751397494027986033353 14438813548120520989525015)
      ·
        refine ⟨21658220322180781484287523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14438813548120520989525015 21658220322180781484287523)
        ·
          refine ⟨32487330483271172226431285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21658220322180781484287523 32487330483271172226431285)
          ·
            refine ⟨3045687232806672396227933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32487330483271172226431285 3045687232806672396227933)
            ·
              refine ⟨1142132712302502148585475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3045687232806672396227933 1142132712302502148585475)
              ·
                refine ⟨1713199068453753222878213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1142132712302502148585475 1713199068453753222878213)
                ·
                  refine ⟨321224825335078729289665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1713199068453753222878213 321224825335078729289665)
                  ·
                    rfl

theorem cell21_1407562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_1407562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1407562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1407562 prefixEnd_1407562 := by exact prefixLift 1407562
  have htrace : WordTrace (prefixWord ++ tailWord_1407562) baseStart_1407562 baseEnd_1407562 := by
    simpa [prefixWord, tailWord_1407562, baseEnd_1407562] using wordTrace_append hprefix tailTrace_1407562
  have hstable : (prefixWord ++ tailWord_1407562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407562).length < 2 ^ (prefixWord ++ tailWord_1407562).sum := by decide
  have hdescent : baseEnd_1407562 < baseStart_1407562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407621 : List Nat := [1, 3, 1, 1, 4, 3, 1, 3, 4]
def baseStart_1407621 : Nat := 118140960795 + 1407621 * 2 ^ 59
def prefixEnd_1407621 : Nat := 4983230072969 + 3 ^ 40 * 1407621 * 2
def baseEnd_1407621 : Nat := 321238289938907737806211

theorem tailTrace_1407621 : CollatzResearch.WordTrace tailWord_1407621 prefixEnd_1407621 321238289938907737806211 := by
  unfold tailWord_1407621
  simp only [CollatzResearch.WordTrace]
  refine ⟨51340155633436994372486717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34226770422291329581657811 51340155633436994372486717)
  ·
    refine ⟨19252558362538872889682519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51340155633436994372486717 19252558362538872889682519)
    ·
      refine ⟨28878837543808309334523779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19252558362538872889682519 28878837543808309334523779)
      ·
        refine ⟨43318256315712464001785669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28878837543808309334523779 43318256315712464001785669)
        ·
          refine ⟨8122173059196087000334813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43318256315712464001785669 8122173059196087000334813)
          ·
            refine ⟨3045814897198532625125555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8122173059196087000334813 3045814897198532625125555)
            ·
              refine ⟨4568722345797798937688333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3045814897198532625125555 4568722345797798937688333)
              ·
                refine ⟨1713270879674174601633125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4568722345797798937688333 1713270879674174601633125)
                ·
                  refine ⟨321238289938907737806211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1713270879674174601633125 321238289938907737806211)
                  ·
                    rfl

theorem cell21_1407621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_1407621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1407621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1407621 prefixEnd_1407621 := by exact prefixLift 1407621
  have htrace : WordTrace (prefixWord ++ tailWord_1407621) baseStart_1407621 baseEnd_1407621 := by
    simpa [prefixWord, tailWord_1407621, baseEnd_1407621] using wordTrace_append hprefix tailTrace_1407621
  have hstable : (prefixWord ++ tailWord_1407621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407621).length < 2 ^ (prefixWord ++ tailWord_1407621).sum := by decide
  have hdescent : baseEnd_1407621 < baseStart_1407621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407655 : List Nat := [1, 1, 6, 3, 1, 1, 2, 2, 4]
def baseStart_1407655 : Nat := 118140960795 + 1407655 * 2 ^ 59
def prefixEnd_1407655 : Nat := 4983230072969 + 3 ^ 40 * 1407655 * 2
def baseEnd_1407655 : Nat := 321246049202131234239475

theorem tailTrace_1407655 : CollatzResearch.WordTrace tailWord_1407655 prefixEnd_1407655 321246049202131234239475 := by
  unfold tailWord_1407655
  simp only [CollatzResearch.WordTrace]
  refine ⟨51341395715313818179224419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34227597143542545452816279 51341395715313818179224419)
  ·
    refine ⟨77012093572970727268836629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51341395715313818179224419 77012093572970727268836629)
    ·
      refine ⟨3609941886233002840726717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 77012093572970727268836629 3609941886233002840726717)
      ·
        refine ⟨1353728207337376065272519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3609941886233002840726717 1353728207337376065272519)
        ·
          refine ⟨2030592311006064097908779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1353728207337376065272519 2030592311006064097908779)
          ·
            refine ⟨3045888466509096146863169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2030592311006064097908779 3045888466509096146863169)
            ·
              refine ⟨2284416349881822110147377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3045888466509096146863169 2284416349881822110147377)
              ·
                refine ⟨1713312262411366582610533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2284416349881822110147377 1713312262411366582610533)
                ·
                  refine ⟨321246049202131234239475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1713312262411366582610533 321246049202131234239475)
                  ·
                    rfl

theorem cell21_1407655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 4].length) (baseStart_1407655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1407655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1407655 prefixEnd_1407655 := by exact prefixLift 1407655
  have htrace : WordTrace (prefixWord ++ tailWord_1407655) baseStart_1407655 baseEnd_1407655 := by
    simpa [prefixWord, tailWord_1407655, baseEnd_1407655] using wordTrace_append hprefix tailTrace_1407655
  have hstable : (prefixWord ++ tailWord_1407655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407655).length < 2 ^ (prefixWord ++ tailWord_1407655).sum := by decide
  have hdescent : baseEnd_1407655 < baseStart_1407655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407776 : List Nat := [2, 1, 1, 5, 1, 3, 3, 2, 3]
def baseStart_1407776 : Nat := 118140960795 + 1407776 * 2 ^ 59
def prefixEnd_1407776 : Nat := 4983230072969 + 3 ^ 40 * 1407776 * 2
def baseEnd_1407776 : Nat := 321273663050661912722561

theorem tailTrace_1407776 : CollatzResearch.WordTrace tailWord_1407776 prefixEnd_1407776 321273663050661912722561 := by
  unfold tailWord_1407776
  simp only [CollatzResearch.WordTrace]
  refine ⟨25672904473937727922189591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34230539298583637229586121 25672904473937727922189591)
  ·
    refine ⟨38509356710906591883284387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25672904473937727922189591 38509356710906591883284387)
    ·
      refine ⟨57764035066359887824926581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38509356710906591883284387 57764035066359887824926581)
      ·
        refine ⟨5415378287471239483586867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57764035066359887824926581 5415378287471239483586867)
        ·
          refine ⟨8123067431206859225380301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5415378287471239483586867 8123067431206859225380301)
          ·
            refine ⟨3046150286702572209517613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8123067431206859225380301 3046150286702572209517613)
            ·
              refine ⟨1142306357513464578569105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3046150286702572209517613 1142306357513464578569105)
              ·
                refine ⟨856729768135098433926829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1142306357513464578569105 856729768135098433926829)
                ·
                  refine ⟨321273663050661912722561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 856729768135098433926829 321273663050661912722561)
                  ·
                    rfl

theorem cell21_1407776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2, 3].length) (baseStart_1407776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1407776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1407776 prefixEnd_1407776 := by exact prefixLift 1407776
  have htrace : WordTrace (prefixWord ++ tailWord_1407776) baseStart_1407776 baseEnd_1407776 := by
    simpa [prefixWord, tailWord_1407776, baseEnd_1407776] using wordTrace_append hprefix tailTrace_1407776
  have hstable : (prefixWord ++ tailWord_1407776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407776).length < 2 ^ (prefixWord ++ tailWord_1407776).sum := by decide
  have hdescent : baseEnd_1407776 < baseStart_1407776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407790 : List Nat := [4, 1, 3, 2, 1, 2, 1, 3, 4]
def baseStart_1407790 : Nat := 118140960795 + 1407790 * 2 ^ 59
def prefixEnd_1407790 : Nat := 4983230072969 + 3 ^ 40 * 1407790 * 2
def baseEnd_1407790 : Nat := 321276858041400999489199

theorem tailTrace_1407790 : CollatzResearch.WordTrace tailWord_1407790 prefixEnd_1407790 321276858041400999489199 := by
  unfold tailWord_1407790
  simp only [CollatzResearch.WordTrace]
  refine ⟨6418289946228092029423603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34230879713216490823592549 6418289946228092029423603)
  ·
    refine ⟨9627434919342138044135405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6418289946228092029423603 9627434919342138044135405)
    ·
      refine ⟨3610288094753301766550777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9627434919342138044135405 3610288094753301766550777)
      ·
        refine ⟨2707716071064976324913083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3610288094753301766550777 2707716071064976324913083)
        ·
          refine ⟨4061574106597464487369625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2707716071064976324913083 4061574106597464487369625)
          ·
            refine ⟨3046180579948098365527219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4061574106597464487369625 3046180579948098365527219)
            ·
              refine ⟨4569270869922147548290829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3046180579948098365527219 4569270869922147548290829)
              ·
                refine ⟨1713476576220805330609061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4569270869922147548290829 1713476576220805330609061)
                ·
                  refine ⟨321276858041400999489199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1713476576220805330609061 321276858041400999489199)
                  ·
                    rfl

theorem cell21_1407790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_1407790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1407790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1407790 prefixEnd_1407790 := by exact prefixLift 1407790
  have htrace : WordTrace (prefixWord ++ tailWord_1407790) baseStart_1407790 baseEnd_1407790 := by
    simpa [prefixWord, tailWord_1407790, baseEnd_1407790] using wordTrace_append hprefix tailTrace_1407790
  have hstable : (prefixWord ++ tailWord_1407790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407790).length < 2 ^ (prefixWord ++ tailWord_1407790).sum := by decide
  have hdescent : baseEnd_1407790 < baseStart_1407790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408001 : List Nat := [1, 2, 4, 1, 2, 3, 2, 2, 4]
def baseStart_1408001 : Nat := 118140960795 + 1408001 * 2 ^ 59
def prefixEnd_1408001 : Nat := 4983230072969 + 3 ^ 40 * 1408001 * 2
def baseEnd_1408001 : Nat := 321325011116111521472101

theorem tailTrace_1408001 : CollatzResearch.WordTrace tailWord_1408001 prefixEnd_1408001 321325011116111521472101 := by
  unfold tailWord_1408001
  simp only [CollatzResearch.WordTrace]
  refine ⟨51354015372060319271319857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34236010248040212847546571 51354015372060319271319857)
  ·
    refine ⟨38515511529045239453489893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51354015372060319271319857 38515511529045239453489893)
    ·
      refine ⟨7221658411695982397529355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38515511529045239453489893 7221658411695982397529355)
      ·
        refine ⟨10832487617543973596294033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7221658411695982397529355 10832487617543973596294033)
        ·
          refine ⟨8124365713157980197220525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10832487617543973596294033 8124365713157980197220525)
          ·
            refine ⟨3046637142434242573957697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8124365713157980197220525 3046637142434242573957697)
            ·
              refine ⟨2284977856825681930468273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3046637142434242573957697 2284977856825681930468273)
              ·
                refine ⟨1713733392619261447851205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2284977856825681930468273 1713733392619261447851205)
                ·
                  refine ⟨321325011116111521472101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1713733392619261447851205 321325011116111521472101)
                  ·
                    rfl

theorem cell21_1408001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 4].length) (baseStart_1408001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408001 prefixEnd_1408001 := by exact prefixLift 1408001
  have htrace : WordTrace (prefixWord ++ tailWord_1408001) baseStart_1408001 baseEnd_1408001 := by
    simpa [prefixWord, tailWord_1408001, baseEnd_1408001] using wordTrace_append hprefix tailTrace_1408001
  have hstable : (prefixWord ++ tailWord_1408001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408001).length < 2 ^ (prefixWord ++ tailWord_1408001).sum := by decide
  have hdescent : baseEnd_1408001 < baseStart_1408001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408043 : List Nat := [1, 1, 1, 1, 2, 1, 6, 2, 6]
def baseStart_1408043 : Nat := 118140960795 + 1408043 * 2 ^ 59
def prefixEnd_1408043 : Nat := 4983230072969 + 3 ^ 40 * 1408043 * 2
def baseEnd_1408043 : Nat := 321334596088328781772015

theorem tailTrace_1408043 : CollatzResearch.WordTrace tailWord_1408043 prefixEnd_1408043 321334596088328781772015 := by
  unfold tailWord_1408043
  simp only [CollatzResearch.WordTrace]
  refine ⟨51355547237908160444348783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34237031491938773629565855 51355547237908160444348783)
  ·
    refine ⟨77033320856862240666523175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51355547237908160444348783 77033320856862240666523175)
    ·
      refine ⟨115549981285293360999784763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77033320856862240666523175 115549981285293360999784763)
      ·
        refine ⟨173324971927940041499677145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115549981285293360999784763 173324971927940041499677145)
        ·
          refine ⟨129993728945955031124757859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173324971927940041499677145 129993728945955031124757859)
          ·
            refine ⟨194990593418932546687136789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129993728945955031124757859 194990593418932546687136789)
            ·
              refine ⟨9140184066512463125959537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 194990593418932546687136789 9140184066512463125959537)
              ·
                refine ⟨6855138049884347344469653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9140184066512463125959537 6855138049884347344469653)
                ·
                  refine ⟨321334596088328781772015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6855138049884347344469653 321334596088328781772015)
                  ·
                    rfl

theorem cell21_1408043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 6].length) (baseStart_1408043 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408043 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408043 prefixEnd_1408043 := by exact prefixLift 1408043
  have htrace : WordTrace (prefixWord ++ tailWord_1408043) baseStart_1408043 baseEnd_1408043 := by
    simpa [prefixWord, tailWord_1408043, baseEnd_1408043] using wordTrace_append hprefix tailTrace_1408043
  have hstable : (prefixWord ++ tailWord_1408043).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408043).length < 2 ^ (prefixWord ++ tailWord_1408043).sum := by decide
  have hdescent : baseEnd_1408043 < baseStart_1408043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408060 : List Nat := [2, 2, 2, 2, 2, 3, 1, 1, 6]
def baseStart_1408060 : Nat := 118140960795 + 1408060 * 2 ^ 59
def prefixEnd_1408060 : Nat := 4983230072969 + 3 ^ 40 * 1408060 * 2
def baseEnd_1408060 : Nat := 321338475719940529988647

theorem tailTrace_1408060 : CollatzResearch.WordTrace tailWord_1408060 prefixEnd_1408060 321338475719940529988647 := by
  unfold tailWord_1408060
  simp only [CollatzResearch.WordTrace]
  refine ⟨25678083639423286173858817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34237444852564381565145089 25678083639423286173858817)
  ·
    refine ⟨19258562729567464630394113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25678083639423286173858817 19258562729567464630394113)
    ·
      refine ⟨14443922047175598472795585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19258562729567464630394113 14443922047175598472795585)
      ·
        refine ⟨10832941535381698854596689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14443922047175598472795585 10832941535381698854596689)
        ·
          refine ⟨8124706151536274140947517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10832941535381698854596689 8124706151536274140947517)
          ·
            refine ⟨3046764806826102802855319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8124706151536274140947517 3046764806826102802855319)
            ·
              refine ⟨4570147210239154204282979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3046764806826102802855319 4570147210239154204282979)
              ·
                refine ⟨6855220815358731306424469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4570147210239154204282979 6855220815358731306424469)
                ·
                  refine ⟨321338475719940529988647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6855220815358731306424469 321338475719940529988647)
                  ·
                    rfl

theorem cell21_1408060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_1408060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408060 prefixEnd_1408060 := by exact prefixLift 1408060
  have htrace : WordTrace (prefixWord ++ tailWord_1408060) baseStart_1408060 baseEnd_1408060 := by
    simpa [prefixWord, tailWord_1408060, baseEnd_1408060] using wordTrace_append hprefix tailTrace_1408060
  have hstable : (prefixWord ++ tailWord_1408060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408060).length < 2 ^ (prefixWord ++ tailWord_1408060).sum := by decide
  have hdescent : baseEnd_1408060 < baseStart_1408060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408094 : List Nat := [4, 4, 1, 1, 1, 1, 1, 2, 6]
def baseStart_1408094 : Nat := 118140960795 + 1408094 * 2 ^ 59
def prefixEnd_1408094 : Nat := 4983230072969 + 3 ^ 40 * 1408094 * 2
def baseEnd_1408094 : Nat := 321346234983164026421911

theorem tailTrace_1408094 : CollatzResearch.WordTrace tailWord_1408094 prefixEnd_1408094 321346234983164026421911 := by
  unfold tailWord_1408094
  simp only [CollatzResearch.WordTrace]
  refine ⟨6419675920090424519306917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34238271573815597436303557 6419675920090424519306917)
  ·
    refine ⟨1203689235016954597370047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6419675920090424519306917 1203689235016954597370047)
    ·
      refine ⟨1805533852525431896055071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1203689235016954597370047 1805533852525431896055071)
      ·
        refine ⟨2708300778788147844082607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1805533852525431896055071 2708300778788147844082607)
        ·
          refine ⟨4062451168182221766123911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2708300778788147844082607 4062451168182221766123911)
          ·
            refine ⟨6093676752273332649185867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4062451168182221766123911 6093676752273332649185867)
            ·
              refine ⟨9140515128409998973778801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6093676752273332649185867 9140515128409998973778801)
              ·
                refine ⟨6855386346307499230334101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9140515128409998973778801 6855386346307499230334101)
                ·
                  refine ⟨321346234983164026421911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6855386346307499230334101 321346234983164026421911)
                  ·
                    rfl

theorem cell21_1408094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_1408094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408094 prefixEnd_1408094 := by exact prefixLift 1408094
  have htrace : WordTrace (prefixWord ++ tailWord_1408094) baseStart_1408094 baseEnd_1408094 := by
    simpa [prefixWord, tailWord_1408094, baseEnd_1408094] using wordTrace_append hprefix tailTrace_1408094
  have hstable : (prefixWord ++ tailWord_1408094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408094).length < 2 ^ (prefixWord ++ tailWord_1408094).sum := by decide
  have hdescent : baseEnd_1408094 < baseStart_1408094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408119 : List Nat := [1, 1, 3, 1, 1, 4, 1, 3, 6]
def baseStart_1408119 : Nat := 118140960795 + 1408119 * 2 ^ 59
def prefixEnd_1408119 : Nat := 4983230072969 + 3 ^ 40 * 1408119 * 2
def baseEnd_1408119 : Nat := 321351940323769538505193

theorem tailTrace_1408119 : CollatzResearch.WordTrace tailWord_1408119 prefixEnd_1408119 321351940323769538505193 := by
  unfold tailWord_1408119
  simp only [CollatzResearch.WordTrace]
  refine ⟨51358319185632825424115411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34238879457088550282743607 51358319185632825424115411)
  ·
    refine ⟨77037478778449238136173117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51358319185632825424115411 77037478778449238136173117)
    ·
      refine ⟨28889054541918464301064919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77037478778449238136173117 28889054541918464301064919)
      ·
        refine ⟨43333581812877696451597379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28889054541918464301064919 43333581812877696451597379)
        ·
          refine ⟨65000372719316544677396069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43333581812877696451597379 65000372719316544677396069)
          ·
            refine ⟨12187569884871852127011763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65000372719316544677396069 12187569884871852127011763)
            ·
              refine ⟨18281354827307778190517645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12187569884871852127011763 18281354827307778190517645)
              ·
                refine ⟨6855508060240416821444117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18281354827307778190517645 6855508060240416821444117)
                ·
                  refine ⟨321351940323769538505193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6855508060240416821444117 321351940323769538505193)
                  ·
                    rfl

theorem cell21_1408119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 6].length) (baseStart_1408119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408119 prefixEnd_1408119 := by exact prefixLift 1408119
  have htrace : WordTrace (prefixWord ++ tailWord_1408119) baseStart_1408119 baseEnd_1408119 := by
    simpa [prefixWord, tailWord_1408119, baseEnd_1408119] using wordTrace_append hprefix tailTrace_1408119
  have hstable : (prefixWord ++ tailWord_1408119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408119).length < 2 ^ (prefixWord ++ tailWord_1408119).sum := by decide
  have hdescent : baseEnd_1408119 < baseStart_1408119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408170 : List Nat := [3, 1, 5, 1, 1, 2, 2, 2, 4]
def baseStart_1408170 : Nat := 118140960795 + 1408170 * 2 ^ 59
def prefixEnd_1408170 : Nat := 4983230072969 + 3 ^ 40 * 1408170 * 2
def baseEnd_1408170 : Nat := 321363579218604783155089

theorem tailTrace_1408170 : CollatzResearch.WordTrace tailWord_1408170 prefixEnd_1408170 321363579218604783155089 := by
  unfold tailWord_1408170
  simp only [CollatzResearch.WordTrace]
  refine ⟨12840044827112015283555491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34240119538965374089481309 12840044827112015283555491)
  ·
    refine ⟨19260067240668022925333237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12840044827112015283555491 19260067240668022925333237)
    ·
      refine ⟨1805631303812627149249991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19260067240668022925333237 1805631303812627149249991)
      ·
        refine ⟨2708446955718940723874987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1805631303812627149249991 2708446955718940723874987)
        ·
          refine ⟨4062670433578411085812481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2708446955718940723874987 4062670433578411085812481)
          ·
            refine ⟨3047002825183808314359361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4062670433578411085812481 3047002825183808314359361)
            ·
              refine ⟨2285252118887856235769521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3047002825183808314359361 2285252118887856235769521)
              ·
                refine ⟨1713939089165892176827141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2285252118887856235769521 1713939089165892176827141)
                ·
                  refine ⟨321363579218604783155089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1713939089165892176827141 321363579218604783155089)
                  ·
                    rfl

theorem cell21_1408170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_1408170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408170 prefixEnd_1408170 := by exact prefixLift 1408170
  have htrace : WordTrace (prefixWord ++ tailWord_1408170) baseStart_1408170 baseEnd_1408170 := by
    simpa [prefixWord, tailWord_1408170, baseEnd_1408170] using wordTrace_append hprefix tailTrace_1408170
  have hstable : (prefixWord ++ tailWord_1408170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408170).length < 2 ^ (prefixWord ++ tailWord_1408170).sum := by decide
  have hdescent : baseEnd_1408170 < baseStart_1408170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408173 : List Nat := [1, 5, 2, 1, 3, 2, 2, 2, 3]
def baseStart_1408173 : Nat := 118140960795 + 1408173 * 2 ^ 59
def prefixEnd_1408173 : Nat := 4983230072969 + 3 ^ 40 * 1408173 * 2
def baseEnd_1408173 : Nat := 321364263859477444605083

theorem tailTrace_1408173 : CollatzResearch.WordTrace tailWord_1408173 prefixEnd_1408173 321364263859477444605083 := by
  unfold tailWord_1408173
  simp only [CollatzResearch.WordTrace]
  refine ⟨51360288727437192646581173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34240192484958128431054115 51360288727437192646581173)
  ·
    refine ⟨4815027068197236810616985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51360288727437192646581173 4815027068197236810616985)
    ·
      refine ⟨3611270301147927607962739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4815027068197236810616985 3611270301147927607962739)
      ·
        refine ⟨5416905451721891411944109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3611270301147927607962739 5416905451721891411944109)
        ·
          refine ⟨2031339544395709279479041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5416905451721891411944109 2031339544395709279479041)
          ·
            refine ⟨1523504658296781959609281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2031339544395709279479041 1523504658296781959609281)
            ·
              refine ⟨1142628493722586469706961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1523504658296781959609281 1142628493722586469706961)
              ·
                refine ⟨856971370291939852280221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1142628493722586469706961 856971370291939852280221)
                ·
                  refine ⟨321364263859477444605083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 856971370291939852280221 321364263859477444605083)
                  ·
                    rfl

theorem cell21_1408173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_1408173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408173 prefixEnd_1408173 := by exact prefixLift 1408173
  have htrace : WordTrace (prefixWord ++ tailWord_1408173) baseStart_1408173 baseEnd_1408173 := by
    simpa [prefixWord, tailWord_1408173, baseEnd_1408173] using wordTrace_append hprefix tailTrace_1408173
  have hstable : (prefixWord ++ tailWord_1408173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408173).length < 2 ^ (prefixWord ++ tailWord_1408173).sum := by decide
  have hdescent : baseEnd_1408173 < baseStart_1408173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408257 : List Nat := [1, 2, 4, 1, 1, 3, 2, 2, 5]
def baseStart_1408257 : Nat := 118140960795 + 1408257 * 2 ^ 59
def prefixEnd_1408257 : Nat := 4983230072969 + 3 ^ 40 * 1408257 * 2
def baseEnd_1408257 : Nat := 321383433803911965204911

theorem tailTrace_1408257 : CollatzResearch.WordTrace tailWord_1408257 prefixEnd_1408257 321383433803911965204911 := by
  unfold tailWord_1408257
  simp only [CollatzResearch.WordTrace]
  refine ⟨51363352459132874992639025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34242234972755249995092683 51363352459132874992639025)
  ·
    refine ⟨38522514344349656244479269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51363352459132874992639025 38522514344349656244479269)
    ·
      refine ⟨7222971439565560545839863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38522514344349656244479269 7222971439565560545839863)
      ·
        refine ⟨10834457159348340818759795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7222971439565560545839863 10834457159348340818759795)
        ·
          refine ⟨16251685739022511228139693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10834457159348340818759795 16251685739022511228139693)
          ·
            refine ⟨6094382152133441710552385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16251685739022511228139693 6094382152133441710552385)
            ·
              refine ⟨4570786614100081282914289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6094382152133441710552385 4570786614100081282914289)
              ·
                refine ⟨3428089960575060962185717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4570786614100081282914289 3428089960575060962185717)
                ·
                  refine ⟨321383433803911965204911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3428089960575060962185717 321383433803911965204911)
                  ·
                    rfl

theorem cell21_1408257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 5].length) (baseStart_1408257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408257 prefixEnd_1408257 := by exact prefixLift 1408257
  have htrace : WordTrace (prefixWord ++ tailWord_1408257) baseStart_1408257 baseEnd_1408257 := by
    simpa [prefixWord, tailWord_1408257, baseEnd_1408257] using wordTrace_append hprefix tailTrace_1408257
  have hstable : (prefixWord ++ tailWord_1408257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408257).length < 2 ^ (prefixWord ++ tailWord_1408257).sum := by decide
  have hdescent : baseEnd_1408257 < baseStart_1408257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408260 : List Nat := [2, 3, 2, 2, 2, 3, 2, 5]
def baseStart_1408260 : Nat := 118140960795 + 1408260 * 2 ^ 59
def prefixEnd_1408260 : Nat := 4983230072969 + 3 ^ 40 * 1408260 * 2
def baseEnd_1408260 : Nat := 107128039481594875551635

theorem tailTrace_1408260 : CollatzResearch.WordTrace tailWord_1408260 prefixEnd_1408260 107128039481594875551635 := by
  unfold tailWord_1408260
  simp only [CollatzResearch.WordTrace]
  refine ⟨25681730939061003252499117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34242307918748004336665489 25681730939061003252499117)
  ·
    refine ⟨9630649102147876219687169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25681730939061003252499117 9630649102147876219687169)
    ·
      refine ⟨7222986826610907164765377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9630649102147876219687169 7222986826610907164765377)
      ·
        refine ⟨5417240119958180373574033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7222986826610907164765377 5417240119958180373574033)
        ·
          refine ⟨4062930089968635280180525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5417240119958180373574033 4062930089968635280180525)
          ·
            refine ⟨1523598783738238230067697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4062930089968635280180525 1523598783738238230067697)
            ·
              refine ⟨1142699087803678672550773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1523598783738238230067697 1142699087803678672550773)
              ·
                refine ⟨107128039481594875551635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1142699087803678672550773 107128039481594875551635)
                ·
                  rfl

theorem cell21_1408260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 5].length) (baseStart_1408260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408260 prefixEnd_1408260 := by exact prefixLift 1408260
  have htrace : WordTrace (prefixWord ++ tailWord_1408260) baseStart_1408260 baseEnd_1408260 := by
    simpa [prefixWord, tailWord_1408260, baseEnd_1408260] using wordTrace_append hprefix tailTrace_1408260
  have hstable : (prefixWord ++ tailWord_1408260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408260).length < 2 ^ (prefixWord ++ tailWord_1408260).sum := by decide
  have hdescent : baseEnd_1408260 < baseStart_1408260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408291 : List Nat := [1, 1, 1, 4, 2, 4, 3, 2, 3]
def baseStart_1408291 : Nat := 118140960795 + 1408291 * 2 ^ 59
def prefixEnd_1408291 : Nat := 4983230072969 + 3 ^ 40 * 1408291 * 2
def baseEnd_1408291 : Nat := 321391193067135461638175

theorem tailTrace_1408291 : CollatzResearch.WordTrace tailWord_1408291 prefixEnd_1408291 321391193067135461638175 := by
  unfold tailWord_1408291
  simp only [CollatzResearch.WordTrace]
  refine ⟨51364592541009698799376727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34243061694006465866251151 51364592541009698799376727)
  ·
    refine ⟨77046888811514548199065091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51364592541009698799376727 77046888811514548199065091)
    ·
      refine ⟨115570333217271822298597637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77046888811514548199065091 115570333217271822298597637)
      ·
        refine ⟨21669437478238466680987057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115570333217271822298597637 21669437478238466680987057)
        ·
          refine ⟨16252078108678850010740293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21669437478238466680987057 16252078108678850010740293)
          ·
            refine ⟨3047264645377284377013805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16252078108678850010740293 3047264645377284377013805)
            ·
              refine ⟨1142724242016481641380177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3047264645377284377013805 1142724242016481641380177)
              ·
                refine ⟨857043181512361231035133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1142724242016481641380177 857043181512361231035133)
                ·
                  refine ⟨321391193067135461638175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 857043181512361231035133 321391193067135461638175)
                  ·
                    rfl

theorem cell21_1408291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2, 3].length) (baseStart_1408291 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408291 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408291 prefixEnd_1408291 := by exact prefixLift 1408291
  have htrace : WordTrace (prefixWord ++ tailWord_1408291) baseStart_1408291 baseEnd_1408291 := by
    simpa [prefixWord, tailWord_1408291, baseEnd_1408291] using wordTrace_append hprefix tailTrace_1408291
  have hstable : (prefixWord ++ tailWord_1408291).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408291).length < 2 ^ (prefixWord ++ tailWord_1408291).sum := by decide
  have hdescent : baseEnd_1408291 < baseStart_1408291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408305 : List Nat := [1, 2, 2, 3, 3, 1, 4, 1, 4]
def baseStart_1408305 : Nat := 118140960795 + 1408305 * 2 ^ 59
def prefixEnd_1408305 : Nat := 4983230072969 + 3 ^ 40 * 1408305 * 2
def baseEnd_1408305 : Nat := 321394388057874548404813

theorem tailTrace_1408305 : CollatzResearch.WordTrace tailWord_1408305 prefixEnd_1408305 321394388057874548404813 := by
  unfold tailWord_1408305
  simp only [CollatzResearch.WordTrace]
  refine ⟨51365103162958979190386369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34243402108639319460257579 51365103162958979190386369)
  ·
    refine ⟨38523827372219234392789777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51365103162958979190386369 38523827372219234392789777)
    ·
      refine ⟨28892870529164425794592333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38523827372219234392789777 28892870529164425794592333)
      ·
        refine ⟨10834826448436659672972125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28892870529164425794592333 10834826448436659672972125)
        ·
          refine ⟨4063059918163747377364547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10834826448436659672972125 4063059918163747377364547)
          ·
            refine ⟨6094589877245621066046821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4063059918163747377364547 6094589877245621066046821)
            ·
              refine ⟨1142735601983553949883779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6094589877245621066046821 1142735601983553949883779)
              ·
                refine ⟨1714103402975330924825669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1142735601983553949883779 1714103402975330924825669)
                ·
                  refine ⟨321394388057874548404813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1714103402975330924825669 321394388057874548404813)
                  ·
                    rfl

theorem cell21_1408305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 4].length) (baseStart_1408305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408305 prefixEnd_1408305 := by exact prefixLift 1408305
  have htrace : WordTrace (prefixWord ++ tailWord_1408305) baseStart_1408305 baseEnd_1408305 := by
    simpa [prefixWord, tailWord_1408305, baseEnd_1408305] using wordTrace_append hprefix tailTrace_1408305
  have hstable : (prefixWord ++ tailWord_1408305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408305).length < 2 ^ (prefixWord ++ tailWord_1408305).sum := by decide
  have hdescent : baseEnd_1408305 < baseStart_1408305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408342 : List Nat := [5, 2, 3, 1, 1, 1, 1, 4, 3]
def baseStart_1408342 : Nat := 118140960795 + 1408342 * 2 ^ 59
def prefixEnd_1408342 : Nat := 4983230072969 + 3 ^ 40 * 1408342 * 2
def baseEnd_1408342 : Nat := 321402831961970706288071

theorem tailTrace_1408342 : CollatzResearch.WordTrace tailWord_1408342 prefixEnd_1408342 321402831961970706288071 := by
  unfold tailWord_1408342
  simp only [CollatzResearch.WordTrace]
  refine ⟨3210403291489058406842705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34244301775883289672988853 3210403291489058406842705)
  ·
    refine ⟨2407802468616793805132029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3210403291489058406842705 2407802468616793805132029)
    ·
      refine ⟨902925925731297676924511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2407802468616793805132029 902925925731297676924511)
      ·
        refine ⟨1354388888596946515386767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 902925925731297676924511 1354388888596946515386767)
        ·
          refine ⟨2031583332895419773080151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1354388888596946515386767 2031583332895419773080151)
          ·
            refine ⟨3047374999343129659620227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2031583332895419773080151 3047374999343129659620227)
            ·
              refine ⟨4571062499014694489430341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3047374999343129659620227 4571062499014694489430341)
              ·
                refine ⟨857074218565255216768189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4571062499014694489430341 857074218565255216768189)
                ·
                  refine ⟨321402831961970706288071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 857074218565255216768189 321402831961970706288071)
                  ·
                    rfl

theorem cell21_1408342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_1408342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408342 prefixEnd_1408342 := by exact prefixLift 1408342
  have htrace : WordTrace (prefixWord ++ tailWord_1408342) baseStart_1408342 baseEnd_1408342 := by
    simpa [prefixWord, tailWord_1408342, baseEnd_1408342] using wordTrace_append hprefix tailTrace_1408342
  have hstable : (prefixWord ++ tailWord_1408342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408342).length < 2 ^ (prefixWord ++ tailWord_1408342).sum := by decide
  have hdescent : baseEnd_1408342 < baseStart_1408342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408361 : List Nat := [1, 2, 1, 1, 1, 3, 2, 10]
def baseStart_1408361 : Nat := 118140960795 + 1408361 * 2 ^ 59
def prefixEnd_1408361 : Nat := 4983230072969 + 3 ^ 40 * 1408361 * 2
def baseEnd_1408361 : Nat := 107135722673610298490455

theorem tailTrace_1408361 : CollatzResearch.WordTrace tailWord_1408361 prefixEnd_1408361 107135722673610298490455 := by
  unfold tailWord_1408361
  simp only [CollatzResearch.WordTrace]
  refine ⟨51367145650756100754424937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34244763767170733836283291 51367145650756100754424937)
  ·
    refine ⟨38525359238067075565818703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51367145650756100754424937 38525359238067075565818703)
    ·
      refine ⟨57788038857100613348728055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38525359238067075565818703 57788038857100613348728055)
      ·
        refine ⟨86682058285650920023092083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57788038857100613348728055 86682058285650920023092083)
        ·
          refine ⟨130023087428476380034638125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86682058285650920023092083 130023087428476380034638125)
          ·
            refine ⟨48758657785678642512989297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130023087428476380034638125 48758657785678642512989297)
            ·
              refine ⟨36568993339258981884741973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48758657785678642512989297 36568993339258981884741973)
              ·
                refine ⟨107135722673610298490455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36568993339258981884741973 107135722673610298490455)
                ·
                  rfl

theorem cell21_1408361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 10].length) (baseStart_1408361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408361 prefixEnd_1408361 := by exact prefixLift 1408361
  have htrace : WordTrace (prefixWord ++ tailWord_1408361) baseStart_1408361 baseEnd_1408361 := by
    simpa [prefixWord, tailWord_1408361, baseEnd_1408361] using wordTrace_append hprefix tailTrace_1408361
  have hstable : (prefixWord ++ tailWord_1408361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408361).length < 2 ^ (prefixWord ++ tailWord_1408361).sum := by decide
  have hdescent : baseEnd_1408361 < baseStart_1408361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408364 : List Nat := [2, 2, 1, 1, 5, 1, 2, 3, 4]
def baseStart_1408364 : Nat := 118140960795 + 1408364 * 2 ^ 59
def prefixEnd_1408364 : Nat := 4983230072969 + 3 ^ 40 * 1408364 * 2
def baseEnd_1408364 : Nat := 321407852661703556921359

theorem tailTrace_1408364 : CollatzResearch.WordTrace tailWord_1408364 prefixEnd_1408364 321407852661703556921359 := by
  unfold tailWord_1408364
  simp only [CollatzResearch.WordTrace]
  refine ⟨25683627534872616133392073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34244836713163488177856097 25683627534872616133392073)
  ·
    refine ⟨19262720651154462100044055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25683627534872616133392073 19262720651154462100044055)
    ·
      refine ⟨28894080976731693150066083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19262720651154462100044055 28894080976731693150066083)
      ·
        refine ⟨43341121465097539725099125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28894080976731693150066083 43341121465097539725099125)
        ·
          refine ⟨4063230137352894349228043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43341121465097539725099125 4063230137352894349228043)
          ·
            refine ⟨6094845206029341523842065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4063230137352894349228043 6094845206029341523842065)
            ·
              refine ⟨4571133904522006142881549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6094845206029341523842065 4571133904522006142881549)
              ·
                refine ⟨1714175214195752303580581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4571133904522006142881549 1714175214195752303580581)
                ·
                  refine ⟨321407852661703556921359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1714175214195752303580581 321407852661703556921359)
                  ·
                    rfl

theorem cell21_1408364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_1408364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408364 prefixEnd_1408364 := by exact prefixLift 1408364
  have htrace : WordTrace (prefixWord ++ tailWord_1408364) baseStart_1408364 baseEnd_1408364 := by
    simpa [prefixWord, tailWord_1408364, baseEnd_1408364] using wordTrace_append hprefix tailTrace_1408364
  have hstable : (prefixWord ++ tailWord_1408364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408364).length < 2 ^ (prefixWord ++ tailWord_1408364).sum := by decide
  have hdescent : baseEnd_1408364 < baseStart_1408364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408398 : List Nat := [4, 1, 1, 4, 2, 2, 1, 2, 4]
def baseStart_1408398 : Nat := 118140960795 + 1408398 * 2 ^ 59
def prefixEnd_1408398 : Nat := 4983230072969 + 3 ^ 40 * 1408398 * 2
def baseEnd_1408398 : Nat := 321415611924927053354623

theorem tailTrace_1408398 : CollatzResearch.WordTrace tailWord_1408398 prefixEnd_1408398 321415611924927053354623 := by
  unfold tailWord_1408398
  simp only [CollatzResearch.WordTrace]
  refine ⟨6421061893952757009190231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34245663434414704049014565 6421061893952757009190231)
  ·
    refine ⟨9631592840929135513785347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6421061893952757009190231 9631592840929135513785347)
    ·
      refine ⟨14447389261393703270678021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9631592840929135513785347 14447389261393703270678021)
      ·
        refine ⟨2708885486511319363252129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14447389261393703270678021 2708885486511319363252129)
        ·
          refine ⟨2031664114883489522439097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2708885486511319363252129 2031664114883489522439097)
          ·
            refine ⟨1523748086162617141829323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2031664114883489522439097 1523748086162617141829323)
            ·
              refine ⟨2285622129243925712743985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1523748086162617141829323 2285622129243925712743985)
              ·
                refine ⟨1714216596932944284557989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2285622129243925712743985 1714216596932944284557989)
                ·
                  refine ⟨321415611924927053354623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1714216596932944284557989 321415611924927053354623)
                  ·
                    rfl

theorem cell21_1408398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_1408398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408398 prefixEnd_1408398 := by exact prefixLift 1408398
  have htrace : WordTrace (prefixWord ++ tailWord_1408398) baseStart_1408398 baseEnd_1408398 := by
    simpa [prefixWord, tailWord_1408398, baseEnd_1408398] using wordTrace_append hprefix tailTrace_1408398
  have hstable : (prefixWord ++ tailWord_1408398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408398).length < 2 ^ (prefixWord ++ tailWord_1408398).sum := by decide
  have hdescent : baseEnd_1408398 < baseStart_1408398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408409 : List Nat := [1, 2, 1, 2, 1, 6, 2, 1, 5]
def baseStart_1408409 : Nat := 118140960795 + 1408409 * 2 ^ 59
def prefixEnd_1408409 : Nat := 4983230072969 + 3 ^ 40 * 1408409 * 2
def baseEnd_1408409 : Nat := 321418122274793478671267

theorem tailTrace_1408409 : CollatzResearch.WordTrace tailWord_1408409 prefixEnd_1408409 321418122274793478671267 := by
  unfold tailWord_1408409
  simp only [CollatzResearch.WordTrace]
  refine ⟨51368896354582204952172281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34245930903054803301448187 51368896354582204952172281)
  ·
    refine ⟨38526672265936653714129211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51368896354582204952172281 38526672265936653714129211)
    ·
      refine ⟨57790008398904980571193817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38526672265936653714129211 57790008398904980571193817)
      ·
        refine ⟨43342506299178735428395363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57790008398904980571193817 43342506299178735428395363)
        ·
          refine ⟨65013759448768103142593045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43342506299178735428395363 65013759448768103142593045)
          ·
            refine ⟨3047519974161004834809049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65013759448768103142593045 3047519974161004834809049)
            ·
              refine ⟨2285639980620753626106787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3047519974161004834809049 2285639980620753626106787)
              ·
                refine ⟨3428459970931130439160181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2285639980620753626106787 3428459970931130439160181)
                ·
                  refine ⟨321418122274793478671267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3428459970931130439160181 321418122274793478671267)
                  ·
                    rfl

theorem cell21_1408409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 5].length) (baseStart_1408409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408409 prefixEnd_1408409 := by exact prefixLift 1408409
  have htrace : WordTrace (prefixWord ++ tailWord_1408409) baseStart_1408409 baseEnd_1408409 := by
    simpa [prefixWord, tailWord_1408409, baseEnd_1408409] using wordTrace_append hprefix tailTrace_1408409
  have hstable : (prefixWord ++ tailWord_1408409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408409).length < 2 ^ (prefixWord ++ tailWord_1408409).sum := by decide
  have hdescent : baseEnd_1408409 < baseStart_1408409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408513 : List Nat := [1, 2, 4, 1, 13]
def baseStart_1408513 : Nat := 118140960795 + 1408513 * 2 ^ 59
def prefixEnd_1408513 : Nat := 4983230072969 + 3 ^ 40 * 1408513 * 2
def baseEnd_1408513 : Nat := 3968417981379165542441

theorem tailTrace_1408513 : CollatzResearch.WordTrace tailWord_1408513 prefixEnd_1408513 3968417981379165542441 := by
  unfold tailWord_1408513
  simp only [CollatzResearch.WordTrace]
  refine ⟨51372689546205430713958193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34248459697470287142638795 51372689546205430713958193)
  ·
    refine ⟨38529517159654073035468645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51372689546205430713958193 38529517159654073035468645)
    ·
      refine ⟨7224284467435138694150371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38529517159654073035468645 7224284467435138694150371)
      ·
        refine ⟨10836426701152708041225557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7224284467435138694150371 10836426701152708041225557)
        ·
          refine ⟨3968417981379165542441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 10836426701152708041225557 3968417981379165542441)
          ·
            rfl

theorem cell21_1408513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 13].length) (baseStart_1408513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408513 prefixEnd_1408513 := by exact prefixLift 1408513
  have htrace : WordTrace (prefixWord ++ tailWord_1408513) baseStart_1408513 baseEnd_1408513 := by
    simpa [prefixWord, tailWord_1408513, baseEnd_1408513] using wordTrace_append hprefix tailTrace_1408513
  have hstable : (prefixWord ++ tailWord_1408513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408513).length < 2 ^ (prefixWord ++ tailWord_1408513).sum := by decide
  have hdescent : baseEnd_1408513 < baseStart_1408513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408519 : List Nat := [1, 1, 4, 3, 2, 1, 4, 2, 3]
def baseStart_1408519 : Nat := 118140960795 + 1408519 * 2 ^ 59
def prefixEnd_1408519 : Nat := 4983230072969 + 3 ^ 40 * 1408519 * 2
def baseEnd_1408519 : Nat := 321443225773457731837709

theorem tailTrace_1408519 : CollatzResearch.WordTrace tailWord_1408519 prefixEnd_1408519 321443225773457731837709 := by
  unfold tailWord_1408519
  simp only [CollatzResearch.WordTrace]
  refine ⟨51372908384183693738676611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34248605589455795825784407 51372908384183693738676611)
  ·
    refine ⟨77059362576275540608014917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51372908384183693738676611 77059362576275540608014917)
    ·
      refine ⟨14448630483051663864002797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77059362576275540608014917 14448630483051663864002797)
      ·
        refine ⟨5418236431144373949001049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14448630483051663864002797 5418236431144373949001049)
        ·
          refine ⟨4063677323358280461750787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5418236431144373949001049 4063677323358280461750787)
          ·
            refine ⟨6095515985037420692626181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4063677323358280461750787 6095515985037420692626181)
            ·
              refine ⟨1142909247194516379867409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6095515985037420692626181 1142909247194516379867409)
              ·
                refine ⟨857181935395887284900557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1142909247194516379867409 857181935395887284900557)
                ·
                  refine ⟨321443225773457731837709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 857181935395887284900557 321443225773457731837709)
                  ·
                    rfl

theorem cell21_1408519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2, 3].length) (baseStart_1408519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408519 prefixEnd_1408519 := by exact prefixLift 1408519
  have htrace : WordTrace (prefixWord ++ tailWord_1408519) baseStart_1408519 baseEnd_1408519 := by
    simpa [prefixWord, tailWord_1408519, baseEnd_1408519] using wordTrace_append hprefix tailTrace_1408519
  have hstable : (prefixWord ++ tailWord_1408519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408519).length < 2 ^ (prefixWord ++ tailWord_1408519).sum := by decide
  have hdescent : baseEnd_1408519 < baseStart_1408519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408547 : List Nat := [1, 1, 1, 4, 5, 1, 3, 5]
def baseStart_1408547 : Nat := 118140960795 + 1408547 * 2 ^ 59
def prefixEnd_1408547 : Nat := 4983230072969 + 3 ^ 40 * 1408547 * 2
def baseEnd_1408547 : Nat := 107149871918311968456995

theorem tailTrace_1408547 : CollatzResearch.WordTrace tailWord_1408547 prefixEnd_1408547 107149871918311968456995 := by
  unfold tailWord_1408547
  simp only [CollatzResearch.WordTrace]
  refine ⟨51373929628082254520695895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34249286418721503013797263 51373929628082254520695895)
  ·
    refine ⟨77060894442123381781043843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51373929628082254520695895 77060894442123381781043843)
    ·
      refine ⟨115591341663185072671565765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77060894442123381781043843 115591341663185072671565765)
      ·
        refine ⟨21673376561847201125918581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115591341663185072671565765 21673376561847201125918581)
        ·
          refine ⟨2031879052673175105554867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21673376561847201125918581 2031879052673175105554867)
          ·
            refine ⟨3047818579009762658332301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2031879052673175105554867 3047818579009762658332301)
            ·
              refine ⟨1142931967128660996874613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3047818579009762658332301 1142931967128660996874613)
              ·
                refine ⟨107149871918311968456995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1142931967128660996874613 107149871918311968456995)
                ·
                  rfl

theorem cell21_1408547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 5].length) (baseStart_1408547 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408547 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408547 prefixEnd_1408547 := by exact prefixLift 1408547
  have htrace : WordTrace (prefixWord ++ tailWord_1408547) baseStart_1408547 baseEnd_1408547 := by
    simpa [prefixWord, tailWord_1408547, baseEnd_1408547] using wordTrace_append hprefix tailTrace_1408547
  have hstable : (prefixWord ++ tailWord_1408547).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408547).length < 2 ^ (prefixWord ++ tailWord_1408547).sum := by decide
  have hdescent : baseEnd_1408547 < baseStart_1408547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408575 : List Nat := [1, 1, 2, 2, 3, 4, 1, 1, 6]
def baseStart_1408575 : Nat := 118140960795 + 1408575 * 2 ^ 59
def prefixEnd_1408575 : Nat := 4983230072969 + 3 ^ 40 * 1408575 * 2
def baseEnd_1408575 : Nat := 321456005736414078904261

theorem tailTrace_1408575 : CollatzResearch.WordTrace tailWord_1408575 prefixEnd_1408575 321456005736414078904261 := by
  unfold tailWord_1408575
  simp only [CollatzResearch.WordTrace]
  refine ⟨51374950871980815302715179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34249967247987210201810119 51374950871980815302715179)
  ·
    refine ⟨77062426307971222954072769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51374950871980815302715179 77062426307971222954072769)
    ·
      refine ⟨57796819730978417215554577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77062426307971222954072769 57796819730978417215554577)
      ·
        refine ⟨43347614798233812911665933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57796819730978417215554577 43347614798233812911665933)
        ·
          refine ⟨16255355549337679841874725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43347614798233812911665933 16255355549337679841874725)
          ·
            refine ⟨3047879165500814970351511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16255355549337679841874725 3047879165500814970351511)
            ·
              refine ⟨4571818748251222455527267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3047879165500814970351511 4571818748251222455527267)
              ·
                refine ⟨6857728122376833683290901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4571818748251222455527267 6857728122376833683290901)
                ·
                  refine ⟨321456005736414078904261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6857728122376833683290901 321456005736414078904261)
                  ·
                    rfl

theorem cell21_1408575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 6].length) (baseStart_1408575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408575 prefixEnd_1408575 := by exact prefixLift 1408575
  have htrace : WordTrace (prefixWord ++ tailWord_1408575) baseStart_1408575 baseEnd_1408575 := by
    simpa [prefixWord, tailWord_1408575, baseEnd_1408575] using wordTrace_append hprefix tailTrace_1408575
  have hstable : (prefixWord ++ tailWord_1408575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408575).length < 2 ^ (prefixWord ++ tailWord_1408575).sum := by decide
  have hdescent : baseEnd_1408575 < baseStart_1408575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408592 : List Nat := [2, 1, 1, 1, 1, 3, 7, 1, 4]
def baseStart_1408592 : Nat := 118140960795 + 1408592 * 2 ^ 59
def prefixEnd_1408592 : Nat := 4983230072969 + 3 ^ 40 * 1408592 * 2
def baseEnd_1408592 : Nat := 321459885368025827120893

theorem tailTrace_1408592 : CollatzResearch.WordTrace tailWord_1408592 prefixEnd_1408592 321459885368025827120893 := by
  unfold tailWord_1408592
  simp only [CollatzResearch.WordTrace]
  refine ⟨25687785456459613603042015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34250380608612818137389353 25687785456459613603042015)
  ·
    refine ⟨38531678184689420404563023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25687785456459613603042015 38531678184689420404563023)
    ·
      refine ⟨57797517277034130606844535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38531678184689420404563023 57797517277034130606844535)
      ·
        refine ⟨86696275915551195910266803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57797517277034130606844535 86696275915551195910266803)
        ·
          refine ⟨130044413873326793865400205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86696275915551195910266803 130044413873326793865400205)
          ·
            refine ⟨48766655202497547699525077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130044413873326793865400205 48766655202497547699525077)
            ·
              refine ⟨1142968481308536274207619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 48766655202497547699525077 1142968481308536274207619)
              ·
                refine ⟨1714452721962804411311429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1142968481308536274207619 1714452721962804411311429)
                ·
                  refine ⟨321459885368025827120893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1714452721962804411311429 321459885368025827120893)
                  ·
                    rfl

theorem cell21_1408592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 4].length) (baseStart_1408592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408592 prefixEnd_1408592 := by exact prefixLift 1408592
  have htrace : WordTrace (prefixWord ++ tailWord_1408592) baseStart_1408592 baseEnd_1408592 := by
    simpa [prefixWord, tailWord_1408592, baseEnd_1408592] using wordTrace_append hprefix tailTrace_1408592
  have hstable : (prefixWord ++ tailWord_1408592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408592).length < 2 ^ (prefixWord ++ tailWord_1408592).sum := by decide
  have hdescent : baseEnd_1408592 < baseStart_1408592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408598 : List Nat := [5, 2, 2, 2, 1, 2, 2, 5]
def baseStart_1408598 : Nat := 118140960795 + 1408598 * 2 ^ 59
def prefixEnd_1408598 : Nat := 4983230072969 + 3 ^ 40 * 1408598 * 2
def baseEnd_1408598 : Nat := 107153751549923716673627

theorem tailTrace_1408598 : CollatzResearch.WordTrace tailWord_1408598 prefixEnd_1408598 107153751549923716673627 := by
  unfold tailWord_1408598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3210986859431093139425153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34250526500598326820534965 3210986859431093139425153)
  ·
    refine ⟨2408240144573319854568865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3210986859431093139425153 2408240144573319854568865)
    ·
      refine ⟨1806180108429989890926649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2408240144573319854568865 1806180108429989890926649)
      ·
        refine ⟨1354635081322492418194987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1806180108429989890926649 1354635081322492418194987)
        ·
          refine ⟨2031952621983738627292481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1354635081322492418194987 2031952621983738627292481)
          ·
            refine ⟨1523964466487803970469361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2031952621983738627292481 1523964466487803970469361)
            ·
              refine ⟨1142973349865852977852021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1523964466487803970469361 1142973349865852977852021)
              ·
                refine ⟨107153751549923716673627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1142973349865852977852021 107153751549923716673627)
                ·
                  rfl

theorem cell21_1408598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_1408598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408598 prefixEnd_1408598 := by exact prefixLift 1408598
  have htrace : WordTrace (prefixWord ++ tailWord_1408598) baseStart_1408598 baseEnd_1408598 := by
    simpa [prefixWord, tailWord_1408598, baseEnd_1408598] using wordTrace_append hprefix tailTrace_1408598
  have hstable : (prefixWord ++ tailWord_1408598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408598).length < 2 ^ (prefixWord ++ tailWord_1408598).sum := by decide
  have hdescent : baseEnd_1408598 < baseStart_1408598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408637 : List Nat := [1, 4, 1, 1, 4, 1, 3, 1, 5]
def baseStart_1408637 : Nat := 118140960795 + 1408637 * 2 ^ 59
def prefixEnd_1408637 : Nat := 4983230072969 + 3 ^ 40 * 1408637 * 2
def baseEnd_1408637 : Nat := 321470154981115748870801

theorem tailTrace_1408637 : CollatzResearch.WordTrace tailWord_1408637 prefixEnd_1408637 321470154981115748870801 := by
  unfold tailWord_1408637
  simp only [CollatzResearch.WordTrace]
  refine ⟨51377212197756199891472165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34251474798504133260981443 51377212197756199891472165)
  ·
    refine ⟨9633227287079287479651031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51377212197756199891472165 9633227287079287479651031)
    ·
      refine ⟨14449840930618931219476547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9633227287079287479651031 14449840930618931219476547)
      ·
        refine ⟨21674761395928396829214821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14449840930618931219476547 21674761395928396829214821)
        ·
          refine ⟨4064017761736574405477779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21674761395928396829214821 4064017761736574405477779)
          ·
            refine ⟨6096026642604861608216669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4064017761736574405477779 6096026642604861608216669)
            ·
              refine ⟨2286009990976823103081251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6096026642604861608216669 2286009990976823103081251)
              ·
                refine ⟨3429014986465234654621877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2286009990976823103081251 3429014986465234654621877)
                ·
                  refine ⟨321470154981115748870801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3429014986465234654621877 321470154981115748870801)
                  ·
                    rfl

theorem cell21_1408637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_1408637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408637 prefixEnd_1408637 := by exact prefixLift 1408637
  have htrace : WordTrace (prefixWord ++ tailWord_1408637) baseStart_1408637 baseEnd_1408637 := by
    simpa [prefixWord, tailWord_1408637, baseEnd_1408637] using wordTrace_append hprefix tailTrace_1408637
  have hstable : (prefixWord ++ tailWord_1408637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408637).length < 2 ^ (prefixWord ++ tailWord_1408637).sum := by decide
  have hdescent : baseEnd_1408637 < baseStart_1408637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408651 : List Nat := [1, 1, 1, 1, 4, 1, 5, 3, 4]
def baseStart_1408651 : Nat := 118140960795 + 1408651 * 2 ^ 59
def prefixEnd_1408651 : Nat := 4983230072969 + 3 ^ 40 * 1408651 * 2
def baseEnd_1408651 : Nat := 321473349971854835637439

theorem tailTrace_1408651 : CollatzResearch.WordTrace tailWord_1408651 prefixEnd_1408651 321473349971854835637439 := by
  unfold tailWord_1408651
  simp only [CollatzResearch.WordTrace]
  refine ⟨51377722819705480282481807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34251815213136986854987871 51377722819705480282481807)
  ·
    refine ⟨77066584229558220423722711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51377722819705480282481807 77066584229558220423722711)
    ·
      refine ⟨115599876344337330635584067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77066584229558220423722711 115599876344337330635584067)
      ·
        refine ⟨173399814516505995953376101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115599876344337330635584067 173399814516505995953376101)
        ·
          refine ⟨32512465221844874241258019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173399814516505995953376101 32512465221844874241258019)
          ·
            refine ⟨48768697832767311361887029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32512465221844874241258019 48768697832767311361887029)
            ·
              refine ⟨4572065421821935440176909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48768697832767311361887029 4572065421821935440176909)
              ·
                refine ⟨1714524533183225790066341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4572065421821935440176909 1714524533183225790066341)
                ·
                  refine ⟨321473349971854835637439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1714524533183225790066341 321473349971854835637439)
                  ·
                    rfl

theorem cell21_1408651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 4].length) (baseStart_1408651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408651 prefixEnd_1408651 := by exact prefixLift 1408651
  have htrace : WordTrace (prefixWord ++ tailWord_1408651) baseStart_1408651 baseEnd_1408651 := by
    simpa [prefixWord, tailWord_1408651, baseEnd_1408651] using wordTrace_append hprefix tailTrace_1408651
  have hstable : (prefixWord ++ tailWord_1408651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408651).length < 2 ^ (prefixWord ++ tailWord_1408651).sum := by decide
  have hdescent : baseEnd_1408651 < baseStart_1408651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408730 : List Nat := [3, 1, 1, 2, 2, 4, 2, 3, 3]
def baseStart_1408730 : Nat := 118140960795 + 1408730 * 2 ^ 59
def prefixEnd_1408730 : Nat := 4983230072969 + 3 ^ 40 * 1408730 * 2
def baseEnd_1408730 : Nat := 321491378848168253820611

theorem tailTrace_1408730 : CollatzResearch.WordTrace tailWord_1408730 prefixEnd_1408730 321491378848168253820611 := by
  unfold tailWord_1408730
  simp only [CollatzResearch.WordTrace]
  refine ⟨12845151046604819193651911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34253736124279517849738429 12845151046604819193651911)
  ·
    refine ⟨19267726569907228790477867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12845151046604819193651911 19267726569907228790477867)
    ·
      refine ⟨28901589854860843185716801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19267726569907228790477867 28901589854860843185716801)
      ·
        refine ⟨21676192391145632389287601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28901589854860843185716801 21676192391145632389287601)
        ·
          refine ⟨16257144293359224291965701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21676192391145632389287601 16257144293359224291965701)
          ·
            refine ⟨3048214555004854554743569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16257144293359224291965701 3048214555004854554743569)
            ·
              refine ⟨2286160916253640916057677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3048214555004854554743569 2286160916253640916057677)
              ·
                refine ⟨857310343595115343521629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2286160916253640916057677 857310343595115343521629)
                ·
                  refine ⟨321491378848168253820611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 857310343595115343521629 321491378848168253820611)
                  ·
                    rfl

theorem cell21_1408730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3, 3].length) (baseStart_1408730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408730 prefixEnd_1408730 := by exact prefixLift 1408730
  have htrace : WordTrace (prefixWord ++ tailWord_1408730) baseStart_1408730 baseEnd_1408730 := by
    simpa [prefixWord, tailWord_1408730, baseEnd_1408730] using wordTrace_append hprefix tailTrace_1408730
  have hstable : (prefixWord ++ tailWord_1408730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408730).length < 2 ^ (prefixWord ++ tailWord_1408730).sum := by decide
  have hdescent : baseEnd_1408730 < baseStart_1408730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408741 : List Nat := [1, 3, 1, 4, 1, 1, 10]
def baseStart_1408741 : Nat := 118140960795 + 1408741 * 2 ^ 59
def prefixEnd_1408741 : Nat := 4983230072969 + 3 ^ 40 * 1408741 * 2
def baseEnd_1408741 : Nat := 35721543244226075459695

theorem tailTrace_1408741 : CollatzResearch.WordTrace tailWord_1408741 prefixEnd_1408741 35721543244226075459695 := by
  unfold tailWord_1408741
  simp only [CollatzResearch.WordTrace]
  refine ⟨51381005389379425653258077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34254003592919617102172051 51381005389379425653258077)
  ·
    refine ⟨19267877021017284619971779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51381005389379425653258077 19267877021017284619971779)
    ·
      refine ⟨28901815531525926929957669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19267877021017284619971779 28901815531525926929957669)
      ·
        refine ⟨5419090412161111299367063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28901815531525926929957669 5419090412161111299367063)
        ·
          refine ⟨8128635618241666949050595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5419090412161111299367063 8128635618241666949050595)
          ·
            refine ⟨12192953427362500423575893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8128635618241666949050595 12192953427362500423575893)
            ·
              refine ⟨35721543244226075459695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12192953427362500423575893 35721543244226075459695)
              ·
                rfl

theorem cell21_1408741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 10].length) (baseStart_1408741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408741 prefixEnd_1408741 := by exact prefixLift 1408741
  have htrace : WordTrace (prefixWord ++ tailWord_1408741) baseStart_1408741 baseEnd_1408741 := by
    simpa [prefixWord, tailWord_1408741, baseEnd_1408741] using wordTrace_append hprefix tailTrace_1408741
  have hstable : (prefixWord ++ tailWord_1408741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408741).length < 2 ^ (prefixWord ++ tailWord_1408741).sum := by decide
  have hdescent : baseEnd_1408741 < baseStart_1408741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408744 : List Nat := [2, 1, 4, 1, 3, 1, 3, 2, 4]
def baseStart_1408744 : Nat := 118140960795 + 1408744 * 2 ^ 59
def prefixEnd_1408744 : Nat := 4983230072969 + 3 ^ 40 * 1408744 * 2
def baseEnd_1408744 : Nat := 321494573838907340587249

theorem tailTrace_1408744 : CollatzResearch.WordTrace tailWord_1408744 prefixEnd_1408744 321494573838907340587249 := by
  unfold tailWord_1408744
  simp only [CollatzResearch.WordTrace]
  refine ⟨25690557404184278582808643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34254076538912371443744857 25690557404184278582808643)
  ·
    refine ⟨38535836106276417874212965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25690557404184278582808643 38535836106276417874212965)
    ·
      refine ⟨7225469269926828351414931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38535836106276417874212965 7225469269926828351414931)
      ·
        refine ⟨10838203904890242527122397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7225469269926828351414931 10838203904890242527122397)
        ·
          refine ⟨4064326464333840947670899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10838203904890242527122397 4064326464333840947670899)
          ·
            refine ⟨6096489696500761421506349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4064326464333840947670899 6096489696500761421506349)
            ·
              refine ⟨2286183636187785533064881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6096489696500761421506349 2286183636187785533064881)
              ·
                refine ⟨1714637727140839149798661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2286183636187785533064881 1714637727140839149798661)
                ·
                  refine ⟨321494573838907340587249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1714637727140839149798661 321494573838907340587249)
                  ·
                    rfl

theorem cell21_1408744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 4].length) (baseStart_1408744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408744 prefixEnd_1408744 := by exact prefixLift 1408744
  have htrace : WordTrace (prefixWord ++ tailWord_1408744) baseStart_1408744 baseEnd_1408744 := by
    simpa [prefixWord, tailWord_1408744, baseEnd_1408744] using wordTrace_append hprefix tailTrace_1408744
  have hstable : (prefixWord ++ tailWord_1408744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408744).length < 2 ^ (prefixWord ++ tailWord_1408744).sum := by decide
  have hdescent : baseEnd_1408744 < baseStart_1408744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408817 : List Nat := [1, 2, 2, 3, 2, 2, 1, 8]
def baseStart_1408817 : Nat := 118140960795 + 1408817 * 2 ^ 59
def prefixEnd_1408817 : Nat := 4983230072969 + 3 ^ 40 * 1408817 * 2
def baseEnd_1408817 : Nat := 107170411144491811956811

theorem tailTrace_1408817 : CollatzResearch.WordTrace tailWord_1408817 prefixEnd_1408817 107170411144491811956811 := by
  unfold tailWord_1408817
  simp only [CollatzResearch.WordTrace]
  refine ⟨51383777337104090633024705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34255851558069393755349803 51383777337104090633024705)
  ·
    refine ⟨38537833002828067974768529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51383777337104090633024705 38537833002828067974768529)
    ·
      refine ⟨28903374752121050981076397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38537833002828067974768529 28903374752121050981076397)
      ·
        refine ⟨10838765532045394117903649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28903374752121050981076397 10838765532045394117903649)
        ·
          refine ⟨8129074149034045588427737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10838765532045394117903649 8129074149034045588427737)
          ·
            refine ⟨6096805611775534191320803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8129074149034045588427737 6096805611775534191320803)
            ·
              refine ⟨9145208417663301286981205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6096805611775534191320803 9145208417663301286981205)
              ·
                refine ⟨107170411144491811956811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9145208417663301286981205 107170411144491811956811)
                ·
                  rfl

theorem cell21_1408817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 8].length) (baseStart_1408817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408817 prefixEnd_1408817 := by exact prefixLift 1408817
  have htrace : WordTrace (prefixWord ++ tailWord_1408817) baseStart_1408817 baseEnd_1408817 := by
    simpa [prefixWord, tailWord_1408817, baseEnd_1408817] using wordTrace_append hprefix tailTrace_1408817
  have hstable : (prefixWord ++ tailWord_1408817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408817).length < 2 ^ (prefixWord ++ tailWord_1408817).sum := by decide
  have hdescent : baseEnd_1408817 < baseStart_1408817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408865 : List Nat := [1, 2, 3, 1, 1, 1, 5, 4, 3]
def baseStart_1408865 : Nat := 118140960795 + 1408865 * 2 ^ 59
def prefixEnd_1408865 : Nat := 4983230072969 + 3 ^ 40 * 1408865 * 2
def baseEnd_1408865 : Nat := 321522187687438019070335

theorem tailTrace_1408865 : CollatzResearch.WordTrace tailWord_1408865 prefixEnd_1408865 321522187687438019070335 := by
  unfold tailWord_1408865
  simp only [CollatzResearch.WordTrace]
  refine ⟨51385528040930194830772049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34257018693953463220514699 51385528040930194830772049)
  ·
    refine ⟨38539146030697646123079037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51385528040930194830772049 38539146030697646123079037)
    ·
      refine ⟨14452179761511617296154639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38539146030697646123079037 14452179761511617296154639)
      ·
        refine ⟨21678269642267425944231959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14452179761511617296154639 21678269642267425944231959)
        ·
          refine ⟨32517404463401138916347939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21678269642267425944231959 32517404463401138916347939)
          ·
            refine ⟨48776106695101708374521909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32517404463401138916347939 48776106695101708374521909)
            ·
              refine ⟨4572760002665785160111429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48776106695101708374521909 4572760002665785160111429)
              ·
                refine ⟨857392500499834717520893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4572760002665785160111429 857392500499834717520893)
                ·
                  refine ⟨321522187687438019070335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 857392500499834717520893 321522187687438019070335)
                  ·
                    rfl

theorem cell21_1408865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4, 3].length) (baseStart_1408865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408865 prefixEnd_1408865 := by exact prefixLift 1408865
  have htrace : WordTrace (prefixWord ++ tailWord_1408865) baseStart_1408865 baseEnd_1408865 := by
    simpa [prefixWord, tailWord_1408865, baseEnd_1408865] using wordTrace_append hprefix tailTrace_1408865
  have hstable : (prefixWord ++ tailWord_1408865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408865).length < 2 ^ (prefixWord ++ tailWord_1408865).sum := by decide
  have hdescent : baseEnd_1408865 < baseStart_1408865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408907 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 9]
def baseStart_1408907 : Nat := 118140960795 + 1408907 * 2 ^ 59
def prefixEnd_1408907 : Nat := 4983230072969 + 3 ^ 40 * 1408907 * 2
def baseEnd_1408907 : Nat := 321531772659655279370249

theorem tailTrace_1408907 : CollatzResearch.WordTrace tailWord_1408907 prefixEnd_1408907 321531772659655279370249 := by
  unfold tailWord_1408907
  simp only [CollatzResearch.WordTrace]
  refine ⟨51387059906778036003800975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34258039937852024002533983 51387059906778036003800975)
  ·
    refine ⟨77080589860167054005701463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51387059906778036003800975 77080589860167054005701463)
    ·
      refine ⟨115620884790250581008552195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77080589860167054005701463 115620884790250581008552195)
      ·
        refine ⟨173431327185375871512828293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115620884790250581008552195 173431327185375871512828293)
        ·
          refine ⟨32518373847257975908655305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173431327185375871512828293 32518373847257975908655305)
          ·
            refine ⟨24388780385443481931491479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32518373847257975908655305 24388780385443481931491479)
            ·
              refine ⟨36583170578165222897237219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24388780385443481931491479 36583170578165222897237219)
              ·
                refine ⟨54874755867247834345855829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36583170578165222897237219 54874755867247834345855829)
                ·
                  refine ⟨321531772659655279370249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54874755867247834345855829 321531772659655279370249)
                  ·
                    rfl

theorem cell21_1408907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 9].length) (baseStart_1408907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408907 prefixEnd_1408907 := by exact prefixLift 1408907
  have htrace : WordTrace (prefixWord ++ tailWord_1408907) baseStart_1408907 baseEnd_1408907 := by
    simpa [prefixWord, tailWord_1408907, baseEnd_1408907] using wordTrace_append hprefix tailTrace_1408907
  have hstable : (prefixWord ++ tailWord_1408907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408907).length < 2 ^ (prefixWord ++ tailWord_1408907).sum := by decide
  have hdescent : baseEnd_1408907 < baseStart_1408907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408958 : List Nat := [4, 2, 1, 1, 1, 3, 3, 3, 3]
def baseStart_1408958 : Nat := 118140960795 + 1408958 * 2 ^ 59
def prefixEnd_1408958 : Nat := 4983230072969 + 3 ^ 40 * 1408958 * 2
def baseEnd_1408958 : Nat := 321543411554490524020145

theorem tailTrace_1408958 : CollatzResearch.WordTrace tailWord_1408958 prefixEnd_1408958 321543411554490524020145 := by
  unfold tailWord_1408958
  simp only [CollatzResearch.WordTrace]
  refine ⟨6423615003699158964238441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34259280019728847809271685 6423615003699158964238441)
  ·
    refine ⟨4817711252774369223178831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6423615003699158964238441 4817711252774369223178831)
    ·
      refine ⟨7226566879161553834768247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4817711252774369223178831 7226566879161553834768247)
      ·
        refine ⟨10839850318742330752152371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7226566879161553834768247 10839850318742330752152371)
        ·
          refine ⟨16259775478113496128228557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10839850318742330752152371 16259775478113496128228557)
          ·
            refine ⟨6097415804292561048085709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16259775478113496128228557 6097415804292561048085709)
            ·
              refine ⟨2286530926609710393032141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6097415804292561048085709 2286530926609710393032141)
              ·
                refine ⟨857449097478641397387053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2286530926609710393032141 857449097478641397387053)
                ·
                  refine ⟨321543411554490524020145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 857449097478641397387053 321543411554490524020145)
                  ·
                    rfl

theorem cell21_1408958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_1408958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408958 prefixEnd_1408958 := by exact prefixLift 1408958
  have htrace : WordTrace (prefixWord ++ tailWord_1408958) baseStart_1408958 baseEnd_1408958 := by
    simpa [prefixWord, tailWord_1408958, baseEnd_1408958] using wordTrace_append hprefix tailTrace_1408958
  have hstable : (prefixWord ++ tailWord_1408958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408958).length < 2 ^ (prefixWord ++ tailWord_1408958).sum := by decide
  have hdescent : baseEnd_1408958 < baseStart_1408958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408986 : List Nat := [3, 1, 1, 2, 5, 1, 2, 6]
def baseStart_1408986 : Nat := 118140960795 + 1408986 * 2 ^ 59
def prefixEnd_1408986 : Nat := 4983230072969 + 3 ^ 40 * 1408986 * 2
def baseEnd_1408986 : Nat := 107183267178656232517807

theorem tailTrace_1408986 : CollatzResearch.WordTrace tailWord_1408986 prefixEnd_1408986 107183267178656232517807 := by
  unfold tailWord_1408986
  simp only [CollatzResearch.WordTrace]
  refine ⟨12847485318372958123981703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34259960848994554997284541 12847485318372958123981703)
  ·
    refine ⟨19271227977559437185972555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12847485318372958123981703 19271227977559437185972555)
    ·
      refine ⟨28906841966339155778958833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19271227977559437185972555 28906841966339155778958833)
      ·
        refine ⟨21680131474754366834219125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28906841966339155778958833 21680131474754366834219125)
        ·
          refine ⟨2032512325758221890708043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21680131474754366834219125 2032512325758221890708043)
          ·
            refine ⟨3048768488637332836062065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2032512325758221890708043 3048768488637332836062065)
            ·
              refine ⟨2286576366477999627046549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3048768488637332836062065 2286576366477999627046549)
              ·
                refine ⟨107183267178656232517807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2286576366477999627046549 107183267178656232517807)
                ·
                  rfl

theorem cell21_1408986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 6].length) (baseStart_1408986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1408986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1408986 prefixEnd_1408986 := by exact prefixLift 1408986
  have htrace : WordTrace (prefixWord ++ tailWord_1408986) baseStart_1408986 baseEnd_1408986 := by
    simpa [prefixWord, tailWord_1408986, baseEnd_1408986] using wordTrace_append hprefix tailTrace_1408986
  have hstable : (prefixWord ++ tailWord_1408986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408986).length < 2 ^ (prefixWord ++ tailWord_1408986).sum := by decide
  have hdescent : baseEnd_1408986 < baseStart_1408986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409031 : List Nat := [1, 1, 4, 3, 1, 2, 1, 4, 4]
def baseStart_1409031 : Nat := 118140960795 + 1409031 * 2 ^ 59
def prefixEnd_1409031 : Nat := 4983230072969 + 3 ^ 40 * 1409031 * 2
def baseEnd_1409031 : Nat := 321560071149058619303329

theorem tailTrace_1409031 : CollatzResearch.WordTrace tailWord_1409031 prefixEnd_1409031 321560071149058619303329 := by
  unfold tailWord_1409031
  simp only [CollatzResearch.WordTrace]
  refine ⟨51391582558328805181314947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34261055038885870120876631 51391582558328805181314947)
  ·
    refine ⟨77087373837493207771972421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51391582558328805181314947 77087373837493207771972421)
    ·
      refine ⟨14453882594529976457244829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77087373837493207771972421 14453882594529976457244829)
      ·
        refine ⟨5420205972948741171466811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14453882594529976457244829 5420205972948741171466811)
        ·
          refine ⟨8130308959423111757200217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5420205972948741171466811 8130308959423111757200217)
          ·
            refine ⟨6097731719567333817900163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8130308959423111757200217 6097731719567333817900163)
            ·
              refine ⟨9146597579351000726850245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6097731719567333817900163 9146597579351000726850245)
              ·
                refine ⟨1714987046128312636284421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9146597579351000726850245 1714987046128312636284421)
                ·
                  refine ⟨321560071149058619303329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1714987046128312636284421 321560071149058619303329)
                  ·
                    rfl

theorem cell21_1409031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 4].length) (baseStart_1409031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1409031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1409031 prefixEnd_1409031 := by exact prefixLift 1409031
  have htrace : WordTrace (prefixWord ++ tailWord_1409031) baseStart_1409031 baseEnd_1409031 := by
    simpa [prefixWord, tailWord_1409031, baseEnd_1409031] using wordTrace_append hprefix tailTrace_1409031
  have hstable : (prefixWord ++ tailWord_1409031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409031).length < 2 ^ (prefixWord ++ tailWord_1409031).sum := by decide
  have hdescent : baseEnd_1409031 < baseStart_1409031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409034 : List Nat := [3, 1, 2, 2, 4, 1, 1, 4, 3]
def baseStart_1409034 : Nat := 118140960795 + 1409034 * 2 ^ 59
def prefixEnd_1409034 : Nat := 4983230072969 + 3 ^ 40 * 1409034 * 2
def baseEnd_1409034 : Nat := 321560755789931280753323

theorem tailTrace_1409034 : CollatzResearch.WordTrace tailWord_1409034 prefixEnd_1409034 321560755789931280753323 := by
  unfold tailWord_1409034
  simp only [CollatzResearch.WordTrace]
  refine ⟨12847922994329484173418539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34261127984878624462449437 12847922994329484173418539)
  ·
    refine ⟨19271884491494226260127809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12847922994329484173418539 19271884491494226260127809)
    ·
      refine ⟨14453913368620669695095857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19271884491494226260127809 14453913368620669695095857)
      ·
        refine ⟨10840435026465502271321893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14453913368620669695095857 10840435026465502271321893)
        ·
          refine ⟨2032581567462281675872855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10840435026465502271321893 2032581567462281675872855)
          ·
            refine ⟨3048872351193422513809283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2032581567462281675872855 3048872351193422513809283)
            ·
              refine ⟨4573308526790133770713925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3048872351193422513809283 4573308526790133770713925)
              ·
                refine ⟨857495348773150082008861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4573308526790133770713925 857495348773150082008861)
                ·
                  refine ⟨321560755789931280753323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 857495348773150082008861 321560755789931280753323)
                  ·
                    rfl

theorem cell21_1409034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4, 3].length) (baseStart_1409034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1409034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1409034 prefixEnd_1409034 := by exact prefixLift 1409034
  have htrace : WordTrace (prefixWord ++ tailWord_1409034) baseStart_1409034 baseEnd_1409034 := by
    simpa [prefixWord, tailWord_1409034, baseEnd_1409034] using wordTrace_append hprefix tailTrace_1409034
  have hstable : (prefixWord ++ tailWord_1409034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409034).length < 2 ^ (prefixWord ++ tailWord_1409034).sum := by decide
  have hdescent : baseEnd_1409034 < baseStart_1409034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409037 : List Nat := [1, 7, 1, 2, 1, 2, 1, 6]
def baseStart_1409037 : Nat := 118140960795 + 1409037 * 2 ^ 59
def prefixEnd_1409037 : Nat := 4983230072969 + 3 ^ 40 * 1409037 * 2
def baseEnd_1409037 : Nat := 107187146810267980734439

theorem tailTrace_1409037 : CollatzResearch.WordTrace tailWord_1409037 prefixEnd_1409037 107187146810267980734439 := by
  unfold tailWord_1409037
  simp only [CollatzResearch.WordTrace]
  refine ⟨51391801396307068206033365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34261200930871378804022243 51391801396307068206033365)
  ·
    refine ⟨1204495345225946911078907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 51391801396307068206033365 1204495345225946911078907)
    ·
      refine ⟨1806743017838920366618361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1204495345225946911078907 1806743017838920366618361)
      ·
        refine ⟨1355057263379190274963771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1806743017838920366618361 1355057263379190274963771)
        ·
          refine ⟨2032585895068785412445657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1355057263379190274963771 2032585895068785412445657)
          ·
            refine ⟨1524439421301589059334243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2032585895068785412445657 1524439421301589059334243)
            ·
              refine ⟨2286659131952383589001365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1524439421301589059334243 2286659131952383589001365)
              ·
                refine ⟨107187146810267980734439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2286659131952383589001365 107187146810267980734439)
                ·
                  rfl

theorem cell21_1409037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 6].length) (baseStart_1409037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1409037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1409037 prefixEnd_1409037 := by exact prefixLift 1409037
  have htrace : WordTrace (prefixWord ++ tailWord_1409037) baseStart_1409037 baseEnd_1409037 := by
    simpa [prefixWord, tailWord_1409037, baseEnd_1409037] using wordTrace_append hprefix tailTrace_1409037
  have hstable : (prefixWord ++ tailWord_1409037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409037).length < 2 ^ (prefixWord ++ tailWord_1409037).sum := by decide
  have hdescent : baseEnd_1409037 < baseStart_1409037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409110 : List Nat := [5, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_1409110 : Nat := 118140960795 + 1409110 * 2 ^ 59
def prefixEnd_1409110 : Nat := 4983230072969 + 3 ^ 40 * 1409110 * 2
def baseEnd_1409110 : Nat := 321578100025372037486501

theorem tailTrace_1409110 : CollatzResearch.WordTrace tailWord_1409110 prefixEnd_1409110 321578100025372037486501 := by
  unfold tailWord_1409110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3212153995315162604590049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34262975950028401115627189 3212153995315162604590049)
  ·
    refine ⟨2409115496486371953442537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3212153995315162604590049 2409115496486371953442537)
    ·
      refine ⟨1806836622364778965081903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2409115496486371953442537 1806836622364778965081903)
      ·
        refine ⟨2710254933547168447622855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1806836622364778965081903 2710254933547168447622855)
        ·
          refine ⟨4065382400320752671434283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2710254933547168447622855 4065382400320752671434283)
          ·
            refine ⟨6098073600481129007151425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4065382400320752671434283 6098073600481129007151425)
            ·
              refine ⟨4573555200360846755363569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6098073600481129007151425 4573555200360846755363569)
              ·
                refine ⟨3430166400270635066522677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4573555200360846755363569 3430166400270635066522677)
                ·
                  refine ⟨321578100025372037486501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3430166400270635066522677 321578100025372037486501)
                  ·
                    rfl

theorem cell21_1409110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_1409110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1409110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1409110 prefixEnd_1409110 := by exact prefixLift 1409110
  have htrace : WordTrace (prefixWord ++ tailWord_1409110) baseStart_1409110 baseEnd_1409110 := by
    simpa [prefixWord, tailWord_1409110, baseEnd_1409110] using wordTrace_append hprefix tailTrace_1409110
  have hstable : (prefixWord ++ tailWord_1409110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409110).length < 2 ^ (prefixWord ++ tailWord_1409110).sum := by decide
  have hdescent : baseEnd_1409110 < baseStart_1409110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409197 : List Nat := [1, 5, 2, 1, 2, 10]
def baseStart_1409197 : Nat := 118140960795 + 1409197 * 2 ^ 59
def prefixEnd_1409197 : Nat := 4983230072969 + 3 ^ 40 * 1409197 * 2
def baseEnd_1409197 : Nat := 11911035355951082205049

theorem tailTrace_1409197 : CollatzResearch.WordTrace tailWord_1409197 prefixEnd_1409197 11911035355951082205049 := by
  unfold tailWord_1409197
  simp only [CollatzResearch.WordTrace]
  refine ⟨51397637075727415531857845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34265091383818277021238563 51397637075727415531857845)
  ·
    refine ⟨4818528475849445206111673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51397637075727415531857845 4818528475849445206111673)
    ·
      refine ⟨3613896356887083904583755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4818528475849445206111673 3613896356887083904583755)
      ·
        refine ⟨5420844535330625856875633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3613896356887083904583755 5420844535330625856875633)
        ·
          refine ⟨4065633401497969392656725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5420844535330625856875633 4065633401497969392656725)
          ·
            refine ⟨11911035355951082205049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4065633401497969392656725 11911035355951082205049)
            ·
              rfl

theorem cell21_1409197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 10].length) (baseStart_1409197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1409197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1409197 prefixEnd_1409197 := by exact prefixLift 1409197
  have htrace : WordTrace (prefixWord ++ tailWord_1409197) baseStart_1409197 baseEnd_1409197 := by
    simpa [prefixWord, tailWord_1409197, baseEnd_1409197] using wordTrace_append hprefix tailTrace_1409197
  have hstable : (prefixWord ++ tailWord_1409197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409197).length < 2 ^ (prefixWord ++ tailWord_1409197).sum := by decide
  have hdescent : baseEnd_1409197 < baseStart_1409197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409211 : List Nat := [1, 1, 1, 1, 1, 2, 6, 3, 5]
def baseStart_1409211 : Nat := 118140960795 + 1409211 * 2 ^ 59
def prefixEnd_1409211 : Nat := 4983230072969 + 3 ^ 40 * 1409211 * 2
def baseEnd_1409211 : Nat := 321601149601418306302961

theorem tailTrace_1409211 : CollatzResearch.WordTrace tailWord_1409211 prefixEnd_1409211 321601149601418306302961 := by
  unfold tailWord_1409211
  simp only [CollatzResearch.WordTrace]
  refine ⟨51398147697676695922867487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34265431798451130615244991 51398147697676695922867487)
  ·
    refine ⟨77097221546515043884301231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51398147697676695922867487 77097221546515043884301231)
    ·
      refine ⟨115645832319772565826451847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77097221546515043884301231 115645832319772565826451847)
      ·
        refine ⟨173468748479658848739677771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115645832319772565826451847 173468748479658848739677771)
        ·
          refine ⟨260203122719488273109516657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173468748479658848739677771 260203122719488273109516657)
          ·
            refine ⟨195152342039616204832137493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260203122719488273109516657 195152342039616204832137493)
            ·
              refine ⟨9147766033107009601506445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 195152342039616204832137493 9147766033107009601506445)
              ·
                refine ⟨3430412262415128600564917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9147766033107009601506445 3430412262415128600564917)
                ·
                  refine ⟨321601149601418306302961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3430412262415128600564917 321601149601418306302961)
                  ·
                    rfl

theorem cell21_1409211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 5].length) (baseStart_1409211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1409211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1409211 prefixEnd_1409211 := by exact prefixLift 1409211
  have htrace : WordTrace (prefixWord ++ tailWord_1409211) baseStart_1409211 baseEnd_1409211 := by
    simpa [prefixWord, tailWord_1409211, baseEnd_1409211] using wordTrace_append hprefix tailTrace_1409211
  have hstable : (prefixWord ++ tailWord_1409211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409211).length < 2 ^ (prefixWord ++ tailWord_1409211).sum := by decide
  have hdescent : baseEnd_1409211 < baseStart_1409211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409276 : List Nat := [2, 2, 2, 1, 4, 2, 3, 1, 4]
def baseStart_1409276 : Nat := 118140960795 + 1409276 * 2 ^ 59
def prefixEnd_1409276 : Nat := 4983230072969 + 3 ^ 40 * 1409276 * 2
def baseEnd_1409276 : Nat := 321615983486992637719495

theorem tailTrace_1409276 : CollatzResearch.WordTrace tailWord_1409276 prefixEnd_1409276 321615983486992637719495 := by
  unfold tailWord_1409276
  simp only [CollatzResearch.WordTrace]
  refine ⟨25700259221220606011991841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34267012294960808015989121 25700259221220606011991841)
  ·
    refine ⟨19275194415915454508993881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25700259221220606011991841 19275194415915454508993881)
    ·
      refine ⟨14456395811936590881745411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19275194415915454508993881 14456395811936590881745411)
      ·
        refine ⟨21684593717904886322618117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14456395811936590881745411 21684593717904886322618117)
        ·
          refine ⟨4065861322107166185490897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21684593717904886322618117 4065861322107166185490897)
          ·
            refine ⟨3049395991580374639118173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4065861322107166185490897 3049395991580374639118173)
            ·
              refine ⟨1143523496842640489669315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3049395991580374639118173 1143523496842640489669315)
              ·
                refine ⟨1715285245263960734503973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1143523496842640489669315 1715285245263960734503973)
                ·
                  refine ⟨321615983486992637719495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1715285245263960734503973 321615983486992637719495)
                  ·
                    rfl

theorem cell21_1409276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_1409276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1409276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1409276 prefixEnd_1409276 := by exact prefixLift 1409276
  have htrace : WordTrace (prefixWord ++ tailWord_1409276) baseStart_1409276 baseEnd_1409276 := by
    simpa [prefixWord, tailWord_1409276, baseEnd_1409276] using wordTrace_append hprefix tailTrace_1409276
  have hstable : (prefixWord ++ tailWord_1409276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409276).length < 2 ^ (prefixWord ++ tailWord_1409276).sum := by decide
  have hdescent : baseEnd_1409276 < baseStart_1409276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409366 : List Nat := [5, 2, 3, 11]
def baseStart_1409366 : Nat := 118140960795 + 1409366 * 2 ^ 59
def prefixEnd_1409366 : Nat := 4983230072969 + 3 ^ 40 * 1409366 * 2
def baseEnd_1409366 : Nat := 1323607089354619264277

theorem tailTrace_1409366 : CollatzResearch.WordTrace tailWord_1409366 prefixEnd_1409366 1323607089354619264277 := by
  unfold tailWord_1409366
  simp only [CollatzResearch.WordTrace]
  refine ⟨3212737563257197337172497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34269200674743438263173301 3212737563257197337172497)
  ·
    refine ⟨2409553172442898002879373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3212737563257197337172497 2409553172442898002879373)
    ·
      refine ⟨903582439666086751079765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2409553172442898002879373 903582439666086751079765)
      ·
        refine ⟨1323607089354619264277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 903582439666086751079765 1323607089354619264277)
        ·
          rfl

theorem cell21_1409366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 11].length) (baseStart_1409366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1409366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1409366 prefixEnd_1409366 := by exact prefixLift 1409366
  have htrace : WordTrace (prefixWord ++ tailWord_1409366) baseStart_1409366 baseEnd_1409366 := by
    simpa [prefixWord, tailWord_1409366, baseEnd_1409366] using wordTrace_append hprefix tailTrace_1409366
  have hstable : (prefixWord ++ tailWord_1409366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409366).length < 2 ^ (prefixWord ++ tailWord_1409366).sum := by decide
  have hdescent : baseEnd_1409366 < baseStart_1409366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409372 : List Nat := [2, 2, 4, 3, 1, 2, 2, 2, 3]
def baseStart_1409372 : Nat := 118140960795 + 1409372 * 2 ^ 59
def prefixEnd_1409372 : Nat := 4983230072969 + 3 ^ 40 * 1409372 * 2
def baseEnd_1409372 : Nat := 321637891994917804119299

theorem tailTrace_1409372 : CollatzResearch.WordTrace tailWord_1409372 prefixEnd_1409372 321637891994917804119299 := by
  unfold tailWord_1409372
  simp only [CollatzResearch.WordTrace]
  refine ⟨25702009925046710209739185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34269346566728946946318913 25702009925046710209739185)
  ·
    refine ⟨19276507443785032657304389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25702009925046710209739185 19276507443785032657304389)
    ·
      refine ⟨3614345145709693623244573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19276507443785032657304389 3614345145709693623244573)
      ·
        refine ⟨1355379429641135108716715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3614345145709693623244573 1355379429641135108716715)
        ·
          refine ⟨2033069144461702663075073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1355379429641135108716715 2033069144461702663075073)
          ·
            refine ⟨1524801858346276997306305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2033069144461702663075073 1524801858346276997306305)
            ·
              refine ⟨1143601393759707747979729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1524801858346276997306305 1143601393759707747979729)
              ·
                refine ⟨857701045319780810984797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1143601393759707747979729 857701045319780810984797)
                ·
                  refine ⟨321637891994917804119299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 857701045319780810984797 321637891994917804119299)
                  ·
                    rfl

theorem cell21_1409372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2, 3].length) (baseStart_1409372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1409372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1409372 prefixEnd_1409372 := by exact prefixLift 1409372
  have htrace : WordTrace (prefixWord ++ tailWord_1409372) baseStart_1409372 baseEnd_1409372 := by
    simpa [prefixWord, tailWord_1409372, baseEnd_1409372] using wordTrace_append hprefix tailTrace_1409372
  have hstable : (prefixWord ++ tailWord_1409372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409372).length < 2 ^ (prefixWord ++ tailWord_1409372).sum := by decide
  have hdescent : baseEnd_1409372 < baseStart_1409372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409470 : List Nat := [4, 2, 1, 1, 1, 1, 3, 2, 6]
def baseStart_1409470 : Nat := 118140960795 + 1409470 * 2 ^ 59
def prefixEnd_1409470 : Nat := 4983230072969 + 3 ^ 40 * 1409470 * 2
def baseEnd_1409470 : Nat := 321660256930091411485765

theorem tailTrace_1409470 : CollatzResearch.WordTrace tailWord_1409470 prefixEnd_1409470 321660256930091411485765 := by
  unfold tailWord_1409470
  simp only [CollatzResearch.WordTrace]
  refine ⟨6425949275467297894568233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34271729469158922104363909 6425949275467297894568233)
  ·
    refine ⟨4819461956600473420926175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6425949275467297894568233 4819461956600473420926175)
    ·
      refine ⟨7229192934900710131389263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4819461956600473420926175 7229192934900710131389263)
      ·
        refine ⟨10843789402351065197083895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7229192934900710131389263 10843789402351065197083895)
        ·
          refine ⟨16265684103526597795625843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10843789402351065197083895 16265684103526597795625843)
          ·
            refine ⟨24398526155289896693438765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16265684103526597795625843 24398526155289896693438765)
            ·
              refine ⟨9149447308233711260039537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24398526155289896693438765 9149447308233711260039537)
              ·
                refine ⟨6862085481175283445029653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9149447308233711260039537 6862085481175283445029653)
                ·
                  refine ⟨321660256930091411485765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6862085481175283445029653 321660256930091411485765)
                  ·
                    rfl

theorem cell21_1409470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_1409470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1409470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1409470 prefixEnd_1409470 := by exact prefixLift 1409470
  have htrace : WordTrace (prefixWord ++ tailWord_1409470) baseStart_1409470 baseEnd_1409470 := by
    simpa [prefixWord, tailWord_1409470, baseEnd_1409470] using wordTrace_append hprefix tailTrace_1409470
  have hstable : (prefixWord ++ tailWord_1409470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409470).length < 2 ^ (prefixWord ++ tailWord_1409470).sum := by decide
  have hdescent : baseEnd_1409470 < baseStart_1409470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409490 : List Nat := [3, 2, 2, 4, 1, 2, 1, 1, 5]
def baseStart_1409490 : Nat := 118140960795 + 1409490 * 2 ^ 59
def prefixEnd_1409490 : Nat := 4983230072969 + 3 ^ 40 * 1409490 * 2
def baseEnd_1409490 : Nat := 321664821202575821152391

theorem tailTrace_1409490 : CollatzResearch.WordTrace tailWord_1409490 prefixEnd_1409490 321664821202575821152391 := by
  unfold tailWord_1409490
  simp only [CollatzResearch.WordTrace]
  refine ⟨12852080915916481643068481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34272215775777284381515949 12852080915916481643068481)
  ·
    refine ⟨9639060686937361232301361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12852080915916481643068481 9639060686937361232301361)
    ·
      refine ⟨7229295515203020924226021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9639060686937361232301361 7229295515203020924226021)
      ·
        refine ⟨1355492909100566423292379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7229295515203020924226021 1355492909100566423292379)
        ·
          refine ⟨2033239363650849634938569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1355492909100566423292379 2033239363650849634938569)
          ·
            refine ⟨1524929522738137226203927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2033239363650849634938569 1524929522738137226203927)
            ·
              refine ⟨2287394284107205839305891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1524929522738137226203927 2287394284107205839305891)
              ·
                refine ⟨3431091426160808758958837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2287394284107205839305891 3431091426160808758958837)
                ·
                  refine ⟨321664821202575821152391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3431091426160808758958837 321664821202575821152391)
                  ·
                    rfl

theorem cell21_1409490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_1409490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1409490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1409490 prefixEnd_1409490 := by exact prefixLift 1409490
  have htrace : WordTrace (prefixWord ++ tailWord_1409490) baseStart_1409490 baseEnd_1409490 := by
    simpa [prefixWord, tailWord_1409490, baseEnd_1409490] using wordTrace_append hprefix tailTrace_1409490
  have hstable : (prefixWord ++ tailWord_1409490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409490).length < 2 ^ (prefixWord ++ tailWord_1409490).sum := by decide
  have hdescent : baseEnd_1409490 < baseStart_1409490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409501 : List Nat := [1, 4, 3, 1, 1, 1, 4, 6]
def baseStart_1409501 : Nat := 118140960795 + 1409501 * 2 ^ 59
def prefixEnd_1409501 : Nat := 4983230072969 + 3 ^ 40 * 1409501 * 2
def baseEnd_1409501 : Nat := 107222443850814082156345

theorem tailTrace_1409501 : CollatzResearch.WordTrace tailWord_1409501 prefixEnd_1409501 107222443850814082156345 := by
  unfold tailWord_1409501
  simp only [CollatzResearch.WordTrace]
  refine ⟨51408724866626075450924357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34272483244417383633949571 51408724866626075450924357)
  ·
    refine ⟨9639135912492389147048317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51408724866626075450924357 9639135912492389147048317)
    ·
      refine ⟨3614675967184645930143119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9639135912492389147048317 3614675967184645930143119)
      ·
        refine ⟨5422013950776968895214679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3614675967184645930143119 5422013950776968895214679)
        ·
          refine ⟨8133020926165453342822019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5422013950776968895214679 8133020926165453342822019)
          ·
            refine ⟨12199531389248180014233029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8133020926165453342822019 12199531389248180014233029)
            ·
              refine ⟨2287412135484033752668693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12199531389248180014233029 2287412135484033752668693)
              ·
                refine ⟨107222443850814082156345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2287412135484033752668693 107222443850814082156345)
                ·
                  rfl

theorem cell21_1409501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 6].length) (baseStart_1409501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1409501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1409501 prefixEnd_1409501 := by exact prefixLift 1409501
  have htrace : WordTrace (prefixWord ++ tailWord_1409501) baseStart_1409501 baseEnd_1409501 := by
    simpa [prefixWord, tailWord_1409501, baseEnd_1409501] using wordTrace_append hprefix tailTrace_1409501
  have hstable : (prefixWord ++ tailWord_1409501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409501).length < 2 ^ (prefixWord ++ tailWord_1409501).sum := by decide
  have hdescent : baseEnd_1409501 < baseStart_1409501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409529 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 8]
def baseStart_1409529 : Nat := 118140960795 + 1409529 * 2 ^ 59
def prefixEnd_1409529 : Nat := 4983230072969 + 3 ^ 40 * 1409529 * 2
def baseEnd_1409529 : Nat := 321673721533920420002311

theorem tailTrace_1409529 : CollatzResearch.WordTrace tailWord_1409529 prefixEnd_1409529 321673721533920420002311 := by
  unfold tailWord_1409529
  simp only [CollatzResearch.WordTrace]
  refine ⟨51409746110524636232943641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34273164073683090821962427 51409746110524636232943641)
  ·
    refine ⟨38557309582893477174707731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51409746110524636232943641 38557309582893477174707731)
    ·
      refine ⟨57835964374340215762061597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38557309582893477174707731 57835964374340215762061597)
      ·
        refine ⟨21688486640377580910773099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57835964374340215762061597 21688486640377580910773099)
        ·
          refine ⟨32532729960566371366159649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21688486640377580910773099 32532729960566371366159649)
          ·
            refine ⟨24399547470424778524619737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32532729960566371366159649 24399547470424778524619737)
            ·
              refine ⟨18299660602818583893464803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24399547470424778524619737 18299660602818583893464803)
              ·
                refine ⟨27449490904227875840197205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18299660602818583893464803 27449490904227875840197205)
                ·
                  refine ⟨321673721533920420002311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27449490904227875840197205 321673721533920420002311)
                  ·
                    rfl

theorem cell21_1409529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 8].length) (baseStart_1409529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1409529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1409529 prefixEnd_1409529 := by exact prefixLift 1409529
  have htrace : WordTrace (prefixWord ++ tailWord_1409529) baseStart_1409529 baseEnd_1409529 := by
    simpa [prefixWord, tailWord_1409529, baseEnd_1409529] using wordTrace_append hprefix tailTrace_1409529
  have hstable : (prefixWord ++ tailWord_1409529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409529).length < 2 ^ (prefixWord ++ tailWord_1409529).sum := by decide
  have hdescent : baseEnd_1409529 < baseStart_1409529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409532 : List Nat := [2, 2, 2, 1, 2, 1, 1, 7, 3]
def baseStart_1409532 : Nat := 118140960795 + 1409532 * 2 ^ 59
def prefixEnd_1409532 : Nat := 4983230072969 + 3 ^ 40 * 1409532 * 2
def baseEnd_1409532 : Nat := 321674406174793081452305

theorem tailTrace_1409532 : CollatzResearch.WordTrace tailWord_1409532 prefixEnd_1409532 321674406174793081452305 := by
  unfold tailWord_1409532
  simp only [CollatzResearch.WordTrace]
  refine ⟨25704927764756883872651425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34273237019675845163535233 25704927764756883872651425)
  ·
    refine ⟨19278695823567662904488569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25704927764756883872651425 19278695823567662904488569)
    ·
      refine ⟨14459021867675747178366427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19278695823567662904488569 14459021867675747178366427)
      ·
        refine ⟨21688532801513620767549641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14459021867675747178366427 21688532801513620767549641)
        ·
          refine ⟨16266399601135215575662231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21688532801513620767549641 16266399601135215575662231)
          ·
            refine ⟨24399599401702823363493347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16266399601135215575662231 24399599401702823363493347)
            ·
              refine ⟨36599399102554235045240021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24399599401702823363493347 36599399102554235045240021)
              ·
                refine ⟨857798416466114883872813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 36599399102554235045240021 857798416466114883872813)
                ·
                  refine ⟨321674406174793081452305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 857798416466114883872813 321674406174793081452305)
                  ·
                    rfl

theorem cell21_1409532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7, 3].length) (baseStart_1409532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1409532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1409532 prefixEnd_1409532 := by exact prefixLift 1409532
  have htrace : WordTrace (prefixWord ++ tailWord_1409532) baseStart_1409532 baseEnd_1409532 := by
    simpa [prefixWord, tailWord_1409532, baseEnd_1409532] using wordTrace_append hprefix tailTrace_1409532
  have hstable : (prefixWord ++ tailWord_1409532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409532).length < 2 ^ (prefixWord ++ tailWord_1409532).sum := by decide
  have hdescent : baseEnd_1409532 < baseStart_1409532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409636 : List Nat := [2, 3, 1, 1, 2, 2, 3, 7]
def baseStart_1409636 : Nat := 118140960795 + 1409636 * 2 ^ 59
def prefixEnd_1409636 : Nat := 4983230072969 + 3 ^ 40 * 1409636 * 2
def baseEnd_1409636 : Nat := 107232713463904003906253

theorem tailTrace_1409636 : CollatzResearch.WordTrace tailWord_1409636 prefixEnd_1409636 107232713463904003906253 := by
  unfold tailWord_1409636
  simp only [CollatzResearch.WordTrace]
  refine ⟨25706824360568496753544381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34275765814091329004725841 25706824360568496753544381)
  ·
    refine ⟨9640059135213186282579143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25706824360568496753544381 9640059135213186282579143)
    ·
      refine ⟨14460088702819779423868715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9640059135213186282579143 14460088702819779423868715)
      ·
        refine ⟨21690133054229669135803073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14460088702819779423868715 21690133054229669135803073)
        ·
          refine ⟨16267599790672251851852305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21690133054229669135803073 16267599790672251851852305)
          ·
            refine ⟨12200699843004188888889229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16267599790672251851852305 12200699843004188888889229)
            ·
              refine ⟨4575262441126570833333461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12200699843004188888889229 4575262441126570833333461)
              ·
                refine ⟨107232713463904003906253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4575262441126570833333461 107232713463904003906253)
                ·
                  rfl

theorem cell21_1409636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 7].length) (baseStart_1409636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1409636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1409636 prefixEnd_1409636 := by exact prefixLift 1409636
  have htrace : WordTrace (prefixWord ++ tailWord_1409636) baseStart_1409636 baseEnd_1409636 := by
    simpa [prefixWord, tailWord_1409636, baseEnd_1409636] using wordTrace_append hprefix tailTrace_1409636
  have hstable : (prefixWord ++ tailWord_1409636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409636).length < 2 ^ (prefixWord ++ tailWord_1409636).sum := by decide
  have hdescent : baseEnd_1409636 < baseStart_1409636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409667 : List Nat := [1, 1, 1, 3, 3, 1, 5, 1, 5]
def baseStart_1409667 : Nat := 118140960795 + 1409667 * 2 ^ 59
def prefixEnd_1409667 : Nat := 4983230072969 + 3 ^ 40 * 1409667 * 2
def baseEnd_1409667 : Nat := 321705215014062846702029

theorem tailTrace_1409667 : CollatzResearch.WordTrace tailWord_1409667 prefixEnd_1409667 321705215014062846702029 := by
  unfold tailWord_1409667
  simp only [CollatzResearch.WordTrace]
  refine ⟨51414779384024685801467255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34276519589349790534311503 51414779384024685801467255)
  ·
    refine ⟨77122169076037028702200883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51414779384024685801467255 77122169076037028702200883)
    ·
      refine ⟨115683253614055543053301325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77122169076037028702200883 115683253614055543053301325)
      ·
        refine ⟨43381220105270828644987997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115683253614055543053301325 43381220105270828644987997)
        ·
          refine ⟨16267957539476560741870499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43381220105270828644987997 16267957539476560741870499)
          ·
            refine ⟨24401936309214841112805749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16267957539476560741870499 24401936309214841112805749)
            ·
              refine ⟨2287681528988891354325539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24401936309214841112805749 2287681528988891354325539)
              ·
                refine ⟨3431522293483337031488309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2287681528988891354325539 3431522293483337031488309)
                ·
                  refine ⟨321705215014062846702029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3431522293483337031488309 321705215014062846702029)
                  ·
                    rfl

theorem cell21_1409667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 5].length) (baseStart_1409667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1409667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1409667 prefixEnd_1409667 := by exact prefixLift 1409667
  have htrace : WordTrace (prefixWord ++ tailWord_1409667) baseStart_1409667 baseEnd_1409667 := by
    simpa [prefixWord, tailWord_1409667, baseEnd_1409667] using wordTrace_append hprefix tailTrace_1409667
  have hstable : (prefixWord ++ tailWord_1409667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409667).length < 2 ^ (prefixWord ++ tailWord_1409667).sum := by decide
  have hdescent : baseEnd_1409667 < baseStart_1409667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409746 : List Nat := [3, 2, 2, 2, 3, 1, 3, 5]
def baseStart_1409746 : Nat := 118140960795 + 1409746 * 2 ^ 59
def prefixEnd_1409746 : Nat := 4983230072969 + 3 ^ 40 * 1409746 * 2
def baseEnd_1409746 : Nat := 107241081296792088295067

theorem tailTrace_1409746 : CollatzResearch.WordTrace tailWord_1409746 prefixEnd_1409746 107241081296792088295067 := by
  unfold tailWord_1409746
  simp only [CollatzResearch.WordTrace]
  refine ⟨12854415187684620573398273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34278440500492321529062061 12854415187684620573398273)
  ·
    refine ⟨9640811390763465430048705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12854415187684620573398273 9640811390763465430048705)
    ·
      refine ⟨7230608543072599072536529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9640811390763465430048705 7230608543072599072536529)
      ·
        refine ⟨5422956407304449304402397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7230608543072599072536529 5422956407304449304402397)
        ·
          refine ⟨2033608652739168489150899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5422956407304449304402397 2033608652739168489150899)
          ·
            refine ⟨3050412979108752733726349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2033608652739168489150899 3050412979108752733726349)
            ·
              refine ⟨1143904867165782275147381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3050412979108752733726349 1143904867165782275147381)
              ·
                refine ⟨107241081296792088295067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1143904867165782275147381 107241081296792088295067)
                ·
                  rfl

theorem cell21_1409746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 5].length) (baseStart_1409746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1409746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1409746 prefixEnd_1409746 := by exact prefixLift 1409746
  have htrace : WordTrace (prefixWord ++ tailWord_1409746) baseStart_1409746 baseEnd_1409746 := by
    simpa [prefixWord, tailWord_1409746, baseEnd_1409746] using wordTrace_append hprefix tailTrace_1409746
  have hstable : (prefixWord ++ tailWord_1409746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409746).length < 2 ^ (prefixWord ++ tailWord_1409746).sum := by decide
  have hdescent : baseEnd_1409746 < baseStart_1409746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409774 : List Nat := [4, 1, 2, 1, 1, 4, 1, 1, 6]
def baseStart_1409774 : Nat := 118140960795 + 1409774 * 2 ^ 59
def prefixEnd_1409774 : Nat := 4983230072969 + 3 ^ 40 * 1409774 * 2
def baseEnd_1409774 : Nat := 321729633871854438418477

theorem tailTrace_1409774 : CollatzResearch.WordTrace tailWord_1409774 prefixEnd_1409774 321729633871854438418477 := by
  unfold tailWord_1409774
  simp only [CollatzResearch.WordTrace]
  refine ⟨6427335249329630384451547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34279121329758028717074917 6427335249329630384451547)
  ·
    refine ⟨9641002873994445576677321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6427335249329630384451547 9641002873994445576677321)
    ·
      refine ⟨7230752155495834182507991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9641002873994445576677321 7230752155495834182507991)
      ·
        refine ⟨10846128233243751273761987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7230752155495834182507991 10846128233243751273761987)
        ·
          refine ⟨16269192349865626910642981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10846128233243751273761987 16269192349865626910642981)
          ·
            refine ⟨3050473565599805045745559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16269192349865626910642981 3050473565599805045745559)
            ·
              refine ⟨4575710348399707568618339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3050473565599805045745559 4575710348399707568618339)
              ·
                refine ⟨6863565522599561352927509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4575710348399707568618339 6863565522599561352927509)
                ·
                  refine ⟨321729633871854438418477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6863565522599561352927509 321729633871854438418477)
                  ·
                    rfl

theorem cell21_1409774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_1409774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1409774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1409774 prefixEnd_1409774 := by exact prefixLift 1409774
  have htrace : WordTrace (prefixWord ++ tailWord_1409774) baseStart_1409774 baseEnd_1409774 := by
    simpa [prefixWord, tailWord_1409774, baseEnd_1409774] using wordTrace_append hprefix tailTrace_1409774
  have hstable : (prefixWord ++ tailWord_1409774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409774).length < 2 ^ (prefixWord ++ tailWord_1409774).sum := by decide
  have hdescent : baseEnd_1409774 < baseStart_1409774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409940 : List Nat := [2, 4, 2, 1, 1, 1, 10]
def baseStart_1409940 : Nat := 118140960795 + 1409940 * 2 ^ 59
def prefixEnd_1409940 : Nat := 4983230072969 + 3 ^ 40 * 1409940 * 2
def baseEnd_1409940 : Nat := 35751946370386115405719

theorem tailTrace_1409940 : CollatzResearch.WordTrace tailWord_1409940 prefixEnd_1409940 35751946370386115405719 := by
  unfold tailWord_1409940
  simp only [CollatzResearch.WordTrace]
  refine ⟨25712368256017826713077637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34283157674690435617436849 25712368256017826713077637)
  ·
    refine ⟨4821069048003342508702057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25712368256017826713077637 4821069048003342508702057)
    ·
      refine ⟨3615801786002506881526543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4821069048003342508702057 3615801786002506881526543)
      ·
        refine ⟨5423702679003760322289815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3615801786002506881526543 5423702679003760322289815)
        ·
          refine ⟨8135554018505640483434723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5423702679003760322289815 8135554018505640483434723)
          ·
            refine ⟨12203331027758460725152085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8135554018505640483434723 12203331027758460725152085)
            ·
              refine ⟨35751946370386115405719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12203331027758460725152085 35751946370386115405719)
              ·
                rfl

theorem cell21_1409940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 10].length) (baseStart_1409940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1409940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1409940 prefixEnd_1409940 := by exact prefixLift 1409940
  have htrace : WordTrace (prefixWord ++ tailWord_1409940) baseStart_1409940 baseEnd_1409940 := by
    simpa [prefixWord, tailWord_1409940, baseEnd_1409940] using wordTrace_append hprefix tailTrace_1409940
  have hstable : (prefixWord ++ tailWord_1409940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409940).length < 2 ^ (prefixWord ++ tailWord_1409940).sum := by decide
  have hdescent : baseEnd_1409940 < baseStart_1409940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409999 : List Nat := [1, 1, 2, 1, 1, 6, 9]
def baseStart_1409999 : Nat := 118140960795 + 1409999 * 2 ^ 59
def prefixEnd_1409999 : Nat := 4983230072969 + 3 ^ 40 * 1409999 * 2
def baseEnd_1409999 : Nat := 35753442437478227463113

theorem tailTrace_1409999 : CollatzResearch.WordTrace tailWord_1409999 prefixEnd_1409999 35753442437478227463113 := by
  unfold tailWord_1409999
  simp only [CollatzResearch.WordTrace]
  refine ⟨51426888418821906502553051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34284592279214604335035367 51426888418821906502553051)
  ·
    refine ⟨77140332628232859753829577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51426888418821906502553051 77140332628232859753829577)
    ·
      refine ⟨57855249471174644815372183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77140332628232859753829577 57855249471174644815372183)
      ·
        refine ⟨86782874206761967223058275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57855249471174644815372183 86782874206761967223058275)
        ·
          refine ⟨130174311310142950834587413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86782874206761967223058275 130174311310142950834587413)
          ·
            refine ⟨6101920842662950820371285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 130174311310142950834587413 6101920842662950820371285)
            ·
              refine ⟨35753442437478227463113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6101920842662950820371285 35753442437478227463113)
              ·
                rfl

theorem cell21_1409999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 9].length) (baseStart_1409999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1409999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1409999 prefixEnd_1409999 := by exact prefixLift 1409999
  have htrace : WordTrace (prefixWord ++ tailWord_1409999) baseStart_1409999 baseEnd_1409999 := by
    simpa [prefixWord, tailWord_1409999, baseEnd_1409999] using wordTrace_append hprefix tailTrace_1409999
  have hstable : (prefixWord ++ tailWord_1409999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409999).length < 2 ^ (prefixWord ++ tailWord_1409999).sum := by decide
  have hdescent : baseEnd_1409999 < baseStart_1409999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410002 : List Nat := [3, 2, 2, 3, 1, 1, 2, 1, 6]
def baseStart_1410002 : Nat := 118140960795 + 1410002 * 2 ^ 59
def prefixEnd_1410002 : Nat := 4983230072969 + 3 ^ 40 * 1410002 * 2
def baseEnd_1410002 : Nat := 321781666578176708618011

theorem tailTrace_1410002 : CollatzResearch.WordTrace tailWord_1410002 prefixEnd_1410002 321781666578176708618011 := by
  unfold tailWord_1410002
  simp only [CollatzResearch.WordTrace]
  refine ⟨12856749459452759503728065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34284665225207358676608173 12856749459452759503728065)
  ·
    refine ⟨9642562094589569627796049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12856749459452759503728065 9642562094589569627796049)
    ·
      refine ⟨7231921570942177220847037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9642562094589569627796049 7231921570942177220847037)
      ·
        refine ⟨2711970589103316457817639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7231921570942177220847037 2711970589103316457817639)
        ·
          refine ⟨4067955883654974686726459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2711970589103316457817639 4067955883654974686726459)
          ·
            refine ⟨6101933825482462030089689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4067955883654974686726459 6101933825482462030089689)
            ·
              refine ⟨4576450369111846522567267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6101933825482462030089689 4576450369111846522567267)
              ·
                refine ⟨6864675553667769783850901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4576450369111846522567267 6864675553667769783850901)
                ·
                  refine ⟨321781666578176708618011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6864675553667769783850901 321781666578176708618011)
                  ·
                    rfl

theorem cell21_1410002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_1410002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1410002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1410002 prefixEnd_1410002 := by exact prefixLift 1410002
  have htrace : WordTrace (prefixWord ++ tailWord_1410002) baseStart_1410002 baseEnd_1410002 := by
    simpa [prefixWord, tailWord_1410002, baseEnd_1410002] using wordTrace_append hprefix tailTrace_1410002
  have hstable : (prefixWord ++ tailWord_1410002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410002).length < 2 ^ (prefixWord ++ tailWord_1410002).sum := by decide
  have hdescent : baseEnd_1410002 < baseStart_1410002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410005 : List Nat := [1, 3, 2, 3, 4, 1, 1, 1, 5]
def baseStart_1410005 : Nat := 118140960795 + 1410005 * 2 ^ 59
def prefixEnd_1410005 : Nat := 4983230072969 + 3 ^ 40 * 1410005 * 2
def baseEnd_1410005 : Nat := 321782351219049370068005

theorem tailTrace_1410005 : CollatzResearch.WordTrace tailWord_1410005 prefixEnd_1410005 321782351219049370068005 := by
  unfold tailWord_1410005
  simp only [CollatzResearch.WordTrace]
  refine ⟨51427107256800169527271469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34284738171200113018180979 51427107256800169527271469)
  ·
    refine ⟨19285165221300063572726801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51427107256800169527271469 19285165221300063572726801)
    ·
      refine ⟨14463873915975047679545101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19285165221300063572726801 14463873915975047679545101)
      ·
        refine ⟨5423952718490642879829413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14463873915975047679545101 5423952718490642879829413)
        ·
          refine ⟨1016991134716995539968015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5423952718490642879829413 1016991134716995539968015)
          ·
            refine ⟨1525486702075493309952023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1016991134716995539968015 1525486702075493309952023)
            ·
              refine ⟨2288230053113239964928035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1525486702075493309952023 2288230053113239964928035)
              ·
                refine ⟨3432345079669859947392053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2288230053113239964928035 3432345079669859947392053)
                ·
                  refine ⟨321782351219049370068005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3432345079669859947392053 321782351219049370068005)
                  ·
                    rfl

theorem cell21_1410005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 5].length) (baseStart_1410005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1410005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1410005 prefixEnd_1410005 := by exact prefixLift 1410005
  have htrace : WordTrace (prefixWord ++ tailWord_1410005) baseStart_1410005 baseEnd_1410005 := by
    simpa [prefixWord, tailWord_1410005, baseEnd_1410005] using wordTrace_append hprefix tailTrace_1410005
  have hstable : (prefixWord ++ tailWord_1410005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410005).length < 2 ^ (prefixWord ++ tailWord_1410005).sum := by decide
  have hdescent : baseEnd_1410005 < baseStart_1410005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410050 : List Nat := [3, 4, 1, 3, 2, 8]
def baseStart_1410050 : Nat := 118140960795 + 1410050 * 2 ^ 59
def prefixEnd_1410050 : Nat := 4983230072969 + 3 ^ 40 * 1410050 * 2
def baseEnd_1410050 : Nat := 11918245216005158956219

theorem tailTrace_1410050 : CollatzResearch.WordTrace tailWord_1410050 prefixEnd_1410050 11918245216005158956219 := by
  unfold tailWord_1410050
  simp only [CollatzResearch.WordTrace]
  refine ⟨12857187135409285553164901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34285832361091428141773069 12857187135409285553164901)
  ·
    refine ⟨2410722587889241041218419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12857187135409285553164901 2410722587889241041218419)
    ·
      refine ⟨3616083881833861561827629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2410722587889241041218419 3616083881833861561827629)
      ·
        refine ⟨1356031455687698085685361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3616083881833861561827629 1356031455687698085685361)
        ·
          refine ⟨1017023591765773564264021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1356031455687698085685361 1017023591765773564264021)
          ·
            refine ⟨11918245216005158956219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1017023591765773564264021 11918245216005158956219)
            ·
              rfl

theorem cell21_1410050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 8].length) (baseStart_1410050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1410050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1410050 prefixEnd_1410050 := by exact prefixLift 1410050
  have htrace : WordTrace (prefixWord ++ tailWord_1410050) baseStart_1410050 baseEnd_1410050 := by
    simpa [prefixWord, tailWord_1410050, baseEnd_1410050] using wordTrace_append hprefix tailTrace_1410050
  have hstable : (prefixWord ++ tailWord_1410050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410050).length < 2 ^ (prefixWord ++ tailWord_1410050).sum := by decide
  have hdescent : baseEnd_1410050 < baseStart_1410050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410092 : List Nat := [2, 2, 1, 1, 1, 2, 7, 5]
def baseStart_1410092 : Nat := 118140960795 + 1410092 * 2 ^ 59
def prefixEnd_1410092 : Nat := 4983230072969 + 3 ^ 40 * 1410092 * 2
def baseEnd_1410092 : Nat := 107267401934785517372609

theorem tailTrace_1410092 : CollatzResearch.WordTrace tailWord_1410092 prefixEnd_1410092 107267401934785517372609 := by
  unfold tailWord_1410092
  simp only [CollatzResearch.WordTrace]
  refine ⟨25715140203742491692844265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34286853604989988923792353 25715140203742491692844265)
  ·
    refine ⟨19286355152806868769633199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25715140203742491692844265 19286355152806868769633199)
    ·
      refine ⟨28929532729210303154449799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19286355152806868769633199 28929532729210303154449799)
      ·
        refine ⟨43394299093815454731674699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28929532729210303154449799 43394299093815454731674699)
        ·
          refine ⟨65091448640723182097512049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43394299093815454731674699 65091448640723182097512049)
          ·
            refine ⟨48818586480542386573134037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65091448640723182097512049 48818586480542386573134037)
            ·
              refine ⟨1144185620637712185307829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 48818586480542386573134037 1144185620637712185307829)
              ·
                refine ⟨107267401934785517372609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1144185620637712185307829 107267401934785517372609)
                ·
                  rfl

theorem cell21_1410092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 5].length) (baseStart_1410092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1410092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1410092 prefixEnd_1410092 := by exact prefixLift 1410092
  have htrace : WordTrace (prefixWord ++ tailWord_1410092) baseStart_1410092 baseEnd_1410092 := by
    simpa [prefixWord, tailWord_1410092, baseEnd_1410092] using wordTrace_append hprefix tailTrace_1410092
  have hstable : (prefixWord ++ tailWord_1410092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410092).length < 2 ^ (prefixWord ++ tailWord_1410092).sum := by decide
  have hdescent : baseEnd_1410092 < baseStart_1410092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410157 : List Nat := [1, 5, 1, 1, 2, 4, 1, 3, 3]
def baseStart_1410157 : Nat := 118140960795 + 1410157 * 2 ^ 59
def prefixEnd_1410157 : Nat := 4983230072969 + 3 ^ 40 * 1410157 * 2
def baseEnd_1410157 : Nat := 321817039689930883534361

theorem tailTrace_1410157 : CollatzResearch.WordTrace tailWord_1410157 prefixEnd_1410157 321817039689930883534361 := by
  unfold tailWord_1410157
  simp only [CollatzResearch.WordTrace]
  refine ⟨51432651152249499486804725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34288434101499666324536483 51432651152249499486804725)
  ·
    refine ⟨4821811045523390576887943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51432651152249499486804725 4821811045523390576887943)
    ·
      refine ⟨7232716568285085865331915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4821811045523390576887943 7232716568285085865331915)
      ·
        refine ⟨10849074852427628797997873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7232716568285085865331915 10849074852427628797997873)
        ·
          refine ⟨8136806139320721598498405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10849074852427628797997873 8136806139320721598498405)
          ·
            refine ⟨1525651151122635299718451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8136806139320721598498405 1525651151122635299718451)
            ·
              refine ⟨2288476726683952949577677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1525651151122635299718451 2288476726683952949577677)
              ·
                refine ⟨858178772506482356091629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2288476726683952949577677 858178772506482356091629)
                ·
                  refine ⟨321817039689930883534361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 858178772506482356091629 321817039689930883534361)
                  ·
                    rfl

theorem cell21_1410157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_1410157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1410157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1410157 prefixEnd_1410157 := by exact prefixLift 1410157
  have htrace : WordTrace (prefixWord ++ tailWord_1410157) baseStart_1410157 baseEnd_1410157 := by
    simpa [prefixWord, tailWord_1410157, baseEnd_1410157] using wordTrace_append hprefix tailTrace_1410157
  have hstable : (prefixWord ++ tailWord_1410157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410157).length < 2 ^ (prefixWord ++ tailWord_1410157).sum := by decide
  have hdescent : baseEnd_1410157 < baseStart_1410157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410233 : List Nat := [1, 2, 1, 4, 1, 5, 2, 2, 3]
def baseStart_1410233 : Nat := 118140960795 + 1410233 * 2 ^ 59
def prefixEnd_1410233 : Nat := 4983230072969 + 3 ^ 40 * 1410233 * 2
def baseEnd_1410233 : Nat := 321834383925371640267539

theorem tailTrace_1410233 : CollatzResearch.WordTrace tailWord_1410233 prefixEnd_1410233 321834383925371640267539 := by
  unfold tailWord_1410233
  simp only [CollatzResearch.WordTrace]
  refine ⟨51435423099974164466571353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34290282066649442977714235 51435423099974164466571353)
  ·
    refine ⟨38576567324980623349928515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51435423099974164466571353 38576567324980623349928515)
    ·
      refine ⟨57864850987470935024892773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38576567324980623349928515 57864850987470935024892773)
      ·
        refine ⟨10849659560150800317167395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57864850987470935024892773 10849659560150800317167395)
        ·
          refine ⟨16274489340226200475751093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10849659560150800317167395 16274489340226200475751093)
          ·
            refine ⟨1525733375646206294601665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16274489340226200475751093 1525733375646206294601665)
            ·
              refine ⟨1144300031734654720951249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1525733375646206294601665 1144300031734654720951249)
              ·
                refine ⟨858225023800991040713437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1144300031734654720951249 858225023800991040713437)
                ·
                  refine ⟨321834383925371640267539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 858225023800991040713437 321834383925371640267539)
                  ·
                    rfl

theorem cell21_1410233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2, 3].length) (baseStart_1410233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1410233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1410233 prefixEnd_1410233 := by exact prefixLift 1410233
  have htrace : WordTrace (prefixWord ++ tailWord_1410233) baseStart_1410233 baseEnd_1410233 := by
    simpa [prefixWord, tailWord_1410233, baseEnd_1410233] using wordTrace_append hprefix tailTrace_1410233
  have hstable : (prefixWord ++ tailWord_1410233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410233).length < 2 ^ (prefixWord ++ tailWord_1410233).sum := by decide
  have hdescent : baseEnd_1410233 < baseStart_1410233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410261 : List Nat := [1, 3, 2, 4, 1, 2, 3, 5]
def baseStart_1410261 : Nat := 118140960795 + 1410261 * 2 ^ 59
def prefixEnd_1410261 : Nat := 4983230072969 + 3 ^ 40 * 1410261 * 2
def baseEnd_1410261 : Nat := 107280257968949937933605

theorem tailTrace_1410261 : CollatzResearch.WordTrace tailWord_1410261 prefixEnd_1410261 107280257968949937933605 := by
  unfold tailWord_1410261
  simp only [CollatzResearch.WordTrace]
  refine ⟨51436444343872725248590637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34290962895915150165727091 51436444343872725248590637)
  ·
    refine ⟨19288666628952271968221489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51436444343872725248590637 19288666628952271968221489)
    ·
      refine ⟨14466499971714203976166117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19288666628952271968221489 14466499971714203976166117)
      ·
        refine ⟨2712468744696413245531147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14466499971714203976166117 2712468744696413245531147)
        ·
          refine ⟨4068703117044619868296721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2712468744696413245531147 4068703117044619868296721)
          ·
            refine ⟨3051527337783464901222541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4068703117044619868296721 3051527337783464901222541)
            ·
              refine ⟨1144322751668799337958453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3051527337783464901222541 1144322751668799337958453)
              ·
                refine ⟨107280257968949937933605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1144322751668799337958453 107280257968949937933605)
                ·
                  rfl

theorem cell21_1410261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 5].length) (baseStart_1410261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1410261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1410261 prefixEnd_1410261 := by exact prefixLift 1410261
  have htrace : WordTrace (prefixWord ++ tailWord_1410261) baseStart_1410261 baseEnd_1410261 := by
    simpa [prefixWord, tailWord_1410261, baseEnd_1410261] using wordTrace_append hprefix tailTrace_1410261
  have hstable : (prefixWord ++ tailWord_1410261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410261).length < 2 ^ (prefixWord ++ tailWord_1410261).sum := by decide
  have hdescent : baseEnd_1410261 < baseStart_1410261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410489 : List Nat := [1, 2, 1, 4, 4, 2, 2, 5]
def baseStart_1410489 : Nat := 118140960795 + 1410489 * 2 ^ 59
def prefixEnd_1410489 : Nat := 4983230072969 + 3 ^ 40 * 1410489 * 2
def baseEnd_1410489 : Nat := 107297602204390694666783

theorem tailTrace_1410489 : CollatzResearch.WordTrace tailWord_1410489 prefixEnd_1410489 107297602204390694666783 := by
  unfold tailWord_1410489
  simp only [CollatzResearch.WordTrace]
  refine ⟨51444760187046720187890521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34296506791364480125260347 51444760187046720187890521)
  ·
    refine ⟨38583570140285040140917891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51444760187046720187890521 38583570140285040140917891)
    ·
      refine ⟨57875355210427560211376837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38583570140285040140917891 57875355210427560211376837)
      ·
        refine ⟨10851629101955167539633157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57875355210427560211376837 10851629101955167539633157)
        ·
          refine ⟨2034680456616593913681217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10851629101955167539633157 2034680456616593913681217)
          ·
            refine ⟨1526010342462445435260913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2034680456616593913681217 1526010342462445435260913)
            ·
              refine ⟨1144507756846834076445685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1526010342462445435260913 1144507756846834076445685)
              ·
                refine ⟨107297602204390694666783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1144507756846834076445685 107297602204390694666783)
                ·
                  rfl

theorem cell21_1410489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 5].length) (baseStart_1410489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1410489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1410489 prefixEnd_1410489 := by exact prefixLift 1410489
  have htrace : WordTrace (prefixWord ++ tailWord_1410489) baseStart_1410489 baseEnd_1410489 := by
    simpa [prefixWord, tailWord_1410489, baseEnd_1410489] using wordTrace_append hprefix tailTrace_1410489
  have hstable : (prefixWord ++ tailWord_1410489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410489).length < 2 ^ (prefixWord ++ tailWord_1410489).sum := by decide
  have hdescent : baseEnd_1410489 < baseStart_1410489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410517 : List Nat := [1, 3, 2, 3, 1, 1, 2, 4, 4]
def baseStart_1410517 : Nat := 118140960795 + 1410517 * 2 ^ 59
def prefixEnd_1410517 : Nat := 4983230072969 + 3 ^ 40 * 1410517 * 2
def baseEnd_1410517 : Nat := 321899196594650257533625

theorem tailTrace_1410517 : CollatzResearch.WordTrace tailWord_1410517 prefixEnd_1410517 321899196594650257533625 := by
  unfold tailWord_1410517
  simp only [CollatzResearch.WordTrace]
  refine ⟨51445781430945280969909805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34297187620630187313273203 51445781430945280969909805)
  ·
    refine ⟨19292168036604480363716177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51445781430945280969909805 19292168036604480363716177)
    ·
      refine ⟨14469126027453360272787133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19292168036604480363716177 14469126027453360272787133)
      ·
        refine ⟨5425922260295010102295175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14469126027453360272787133 5425922260295010102295175)
        ·
          refine ⟨8138883390442515153442763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5425922260295010102295175 8138883390442515153442763)
          ·
            refine ⟨12208325085663772730164145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8138883390442515153442763 12208325085663772730164145)
            ·
              refine ⟨9156243814247829547623109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12208325085663772730164145 9156243814247829547623109)
              ·
                refine ⟨1716795715171468040179333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9156243814247829547623109 1716795715171468040179333)
                ·
                  refine ⟨321899196594650257533625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1716795715171468040179333 321899196594650257533625)
                  ·
                    rfl

theorem cell21_1410517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_1410517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1410517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1410517 prefixEnd_1410517 := by exact prefixLift 1410517
  have htrace : WordTrace (prefixWord ++ tailWord_1410517) baseStart_1410517 baseEnd_1410517 := by
    simpa [prefixWord, tailWord_1410517, baseEnd_1410517] using wordTrace_append hprefix tailTrace_1410517
  have hstable : (prefixWord ++ tailWord_1410517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410517).length < 2 ^ (prefixWord ++ tailWord_1410517).sum := by decide
  have hdescent : baseEnd_1410517 < baseStart_1410517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410531 : List Nat := [1, 1, 1, 6, 2, 1, 1, 8]
def baseStart_1410531 : Nat := 118140960795 + 1410531 * 2 ^ 59
def prefixEnd_1410531 : Nat := 4983230072969 + 3 ^ 40 * 1410531 * 2
def baseEnd_1410531 : Nat := 107300797195129781433421

theorem tailTrace_1410531 : CollatzResearch.WordTrace tailWord_1410531 prefixEnd_1410531 107300797195129781433421 := by
  unfold tailWord_1410531
  simp only [CollatzResearch.WordTrace]
  refine ⟨51446292052894561360919447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34297528035263040907279631 51446292052894561360919447)
  ·
    refine ⟨77169438079341842041379171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51446292052894561360919447 77169438079341842041379171)
    ·
      refine ⟨115754157119012763062068757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77169438079341842041379171 115754157119012763062068757)
      ·
        refine ⟨5425976114953723268534473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 115754157119012763062068757 5425976114953723268534473)
        ·
          refine ⟨4069482086215292451400855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5425976114953723268534473 4069482086215292451400855)
          ·
            refine ⟨6104223129322938677101283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4069482086215292451400855 6104223129322938677101283)
            ·
              refine ⟨9156334693984408015651925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6104223129322938677101283 9156334693984408015651925)
              ·
                refine ⟨107300797195129781433421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9156334693984408015651925 107300797195129781433421)
                ·
                  rfl

theorem cell21_1410531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 8].length) (baseStart_1410531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1410531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1410531 prefixEnd_1410531 := by exact prefixLift 1410531
  have htrace : WordTrace (prefixWord ++ tailWord_1410531) baseStart_1410531 baseEnd_1410531 := by
    simpa [prefixWord, tailWord_1410531, baseEnd_1410531] using wordTrace_append hprefix tailTrace_1410531
  have hstable : (prefixWord ++ tailWord_1410531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410531).length < 2 ^ (prefixWord ++ tailWord_1410531).sum := by decide
  have hdescent : baseEnd_1410531 < baseStart_1410531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410579 : List Nat := [1, 1, 1, 2, 1, 7, 1, 4, 3]
def baseStart_1410579 : Nat := 118140960795 + 1410579 * 2 ^ 59
def prefixEnd_1410579 : Nat := 4983230072969 + 3 ^ 40 * 1410579 * 2
def baseEnd_1410579 : Nat := 321913345839351927500165

theorem tailTrace_1410579 : CollatzResearch.WordTrace tailWord_1410579 prefixEnd_1410579 321913345839351927500165 := by
  unfold tailWord_1410579
  simp only [CollatzResearch.WordTrace]
  refine ⟨51448042756720665558666791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34298695171147110372444527 51448042756720665558666791)
  ·
    refine ⟨77172064135080998338000187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51448042756720665558666791 77172064135080998338000187)
    ·
      refine ⟨115758096202621497507000281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77172064135080998338000187 115758096202621497507000281)
      ·
        refine ⟨86818572151966123130250211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115758096202621497507000281 86818572151966123130250211)
        ·
          refine ⟨130227858227949184695375317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86818572151966123130250211 130227858227949184695375317)
          ·
            refine ⟨3052215427217559016297859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 130227858227949184695375317 3052215427217559016297859)
            ·
              refine ⟨4578323140826338524446789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3052215427217559016297859 4578323140826338524446789)
              ·
                refine ⟨858435588904938473333773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4578323140826338524446789 858435588904938473333773)
                ·
                  refine ⟨321913345839351927500165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 858435588904938473333773 321913345839351927500165)
                  ·
                    rfl

theorem cell21_1410579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4, 3].length) (baseStart_1410579 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1410579 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1410579 prefixEnd_1410579 := by exact prefixLift 1410579
  have htrace : WordTrace (prefixWord ++ tailWord_1410579) baseStart_1410579 baseEnd_1410579 := by
    simpa [prefixWord, tailWord_1410579, baseEnd_1410579] using wordTrace_append hprefix tailTrace_1410579
  have hstable : (prefixWord ++ tailWord_1410579).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410579).length < 2 ^ (prefixWord ++ tailWord_1410579).sum := by decide
  have hdescent : baseEnd_1410579 < baseStart_1410579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410593 : List Nat := [1, 2, 3, 2, 2, 2, 2, 3, 4]
def baseStart_1410593 : Nat := 118140960795 + 1410593 * 2 ^ 59
def prefixEnd_1410593 : Nat := 4983230072969 + 3 ^ 40 * 1410593 * 2
def baseEnd_1410593 : Nat := 321916540830091014266803

theorem tailTrace_1410593 : CollatzResearch.WordTrace tailWord_1410593 prefixEnd_1410593 321916540830091014266803 := by
  unfold tailWord_1410593
  simp only [CollatzResearch.WordTrace]
  refine ⟨51448553378669945949676433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34299035585779963966450955 51448553378669945949676433)
  ·
    refine ⟨38586415034002459462257325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51448553378669945949676433 38586415034002459462257325)
    ·
      refine ⟨14469905637750922298346497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38586415034002459462257325 14469905637750922298346497)
      ·
        refine ⟨10852429228313191723759873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14469905637750922298346497 10852429228313191723759873)
        ·
          refine ⟨8139321921234893792819905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10852429228313191723759873 8139321921234893792819905)
          ·
            refine ⟨6104491440926170344614929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8139321921234893792819905 6104491440926170344614929)
            ·
              refine ⟨4578368580694627758461197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6104491440926170344614929 4578368580694627758461197)
              ·
                refine ⟨1716888217760485409422949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4578368580694627758461197 1716888217760485409422949)
                ·
                  refine ⟨321916540830091014266803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1716888217760485409422949 321916540830091014266803)
                  ·
                    rfl

theorem cell21_1410593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 4].length) (baseStart_1410593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1410593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1410593 prefixEnd_1410593 := by exact prefixLift 1410593
  have htrace : WordTrace (prefixWord ++ tailWord_1410593) baseStart_1410593 baseEnd_1410593 := by
    simpa [prefixWord, tailWord_1410593, baseEnd_1410593] using wordTrace_append hprefix tailTrace_1410593
  have hstable : (prefixWord ++ tailWord_1410593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410593).length < 2 ^ (prefixWord ++ tailWord_1410593).sum := by decide
  have hdescent : baseEnd_1410593 < baseStart_1410593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410672 : List Nat := [2, 1, 1, 1, 6, 3, 1, 3, 3]
def baseStart_1410672 : Nat := 118140960795 + 1410672 * 2 ^ 59
def prefixEnd_1410672 : Nat := 4983230072969 + 3 ^ 40 * 1410672 * 2
def baseEnd_1410672 : Nat := 321934569706404432449975

theorem tailTrace_1410672 : CollatzResearch.WordTrace tailWord_1410672 prefixEnd_1410672 321934569706404432449975 := by
  unfold tailWord_1410672
  simp only [CollatzResearch.WordTrace]
  refine ⟨25725717372691871220901135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34300956496922494961201513 25725717372691871220901135)
  ·
    refine ⟨38588576059037806831351703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25725717372691871220901135 38588576059037806831351703)
    ·
      refine ⟨57882864088556710247027555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38588576059037806831351703 57882864088556710247027555)
      ·
        refine ⟨86824296132835065370541333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57882864088556710247027555 86824296132835065370541333)
        ·
          refine ⟨4069888881226643689244125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 86824296132835065370541333 4069888881226643689244125)
          ·
            refine ⟨1526208330459991383466547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4069888881226643689244125 1526208330459991383466547)
            ·
              refine ⟨2289312495689987075199821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1526208330459991383466547 2289312495689987075199821)
              ·
                refine ⟨858492185883745153199933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2289312495689987075199821 858492185883745153199933)
                ·
                  refine ⟨321934569706404432449975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 858492185883745153199933 321934569706404432449975)
                  ·
                    rfl

theorem cell21_1410672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3, 3].length) (baseStart_1410672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1410672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1410672 prefixEnd_1410672 := by exact prefixLift 1410672
  have htrace : WordTrace (prefixWord ++ tailWord_1410672) baseStart_1410672 baseEnd_1410672 := by
    simpa [prefixWord, tailWord_1410672, baseEnd_1410672] using wordTrace_append hprefix tailTrace_1410672
  have hstable : (prefixWord ++ tailWord_1410672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410672).length < 2 ^ (prefixWord ++ tailWord_1410672).sum := by decide
  have hdescent : baseEnd_1410672 < baseStart_1410672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410748 : List Nat := [2, 2, 2, 3, 1, 2, 4, 2, 3]
def baseStart_1410748 : Nat := 118140960795 + 1410748 * 2 ^ 59
def prefixEnd_1410748 : Nat := 4983230072969 + 3 ^ 40 * 1410748 * 2
def baseEnd_1410748 : Nat := 321951913941845189183153

theorem tailTrace_1410748 : CollatzResearch.WordTrace tailWord_1410748 prefixEnd_1410748 321951913941845189183153 := by
  unfold tailWord_1410748
  simp only [CollatzResearch.WordTrace]
  refine ⟨25727103346554203710784449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34302804462072271614379265 25727103346554203710784449)
  ·
    refine ⟨19295327509915652783088337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25727103346554203710784449 19295327509915652783088337)
    ·
      refine ⟨14471495632436739587316253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19295327509915652783088337 14471495632436739587316253)
      ·
        refine ⟨5426810862163777345243595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14471495632436739587316253 5426810862163777345243595)
        ·
          refine ⟨8140216293245666017865393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5426810862163777345243595 8140216293245666017865393)
          ·
            refine ⟨6105162219934249513399045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8140216293245666017865393 6105162219934249513399045)
            ·
              refine ⟨1144717916237671783762321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6105162219934249513399045 1144717916237671783762321)
              ·
                refine ⟨858538437178253837821741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1144717916237671783762321 858538437178253837821741)
                ·
                  refine ⟨321951913941845189183153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 858538437178253837821741 321951913941845189183153)
                  ·
                    rfl

theorem cell21_1410748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2, 3].length) (baseStart_1410748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1410748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1410748 prefixEnd_1410748 := by exact prefixLift 1410748
  have htrace : WordTrace (prefixWord ++ tailWord_1410748) baseStart_1410748 baseEnd_1410748 := by
    simpa [prefixWord, tailWord_1410748, baseEnd_1410748] using wordTrace_append hprefix tailTrace_1410748
  have hstable : (prefixWord ++ tailWord_1410748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410748).length < 2 ^ (prefixWord ++ tailWord_1410748).sum := by decide
  have hdescent : baseEnd_1410748 < baseStart_1410748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410866 : List Nat := [3, 2, 1, 1, 3, 2, 3, 1, 5]
def baseStart_1410866 : Nat := 118140960795 + 1410866 * 2 ^ 59
def prefixEnd_1410866 : Nat := 4983230072969 + 3 ^ 40 * 1410866 * 2
def baseEnd_1410866 : Nat := 321978843149503206216245

theorem tailTrace_1410866 : CollatzResearch.WordTrace tailWord_1410866 prefixEnd_1410866 321978843149503206216245 := by
  unfold tailWord_1410866
  simp only [CollatzResearch.WordTrace]
  refine ⟨12864627626670228393591113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34305673671120609049576301 12864627626670228393591113)
  ·
    refine ⟨9648470720002671295193335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12864627626670228393591113 9648470720002671295193335)
    ·
      refine ⟨14472706080004006942790003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9648470720002671295193335 14472706080004006942790003)
      ·
        refine ⟨21709059120006010414185005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14472706080004006942790003 21709059120006010414185005)
        ·
          refine ⟨8140897170002253905319377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21709059120006010414185005 8140897170002253905319377)
          ·
            refine ⟨6105672877501690428989533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8140897170002253905319377 6105672877501690428989533)
            ·
              refine ⟨2289627329063133910871075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6105672877501690428989533 2289627329063133910871075)
              ·
                refine ⟨3434440993594700866306613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2289627329063133910871075 3434440993594700866306613)
                ·
                  refine ⟨321978843149503206216245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3434440993594700866306613 321978843149503206216245)
                  ·
                    rfl

theorem cell21_1410866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_1410866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1410866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1410866 prefixEnd_1410866 := by exact prefixLift 1410866
  have htrace : WordTrace (prefixWord ++ tailWord_1410866) baseStart_1410866 baseEnd_1410866 := by
    simpa [prefixWord, tailWord_1410866, baseEnd_1410866] using wordTrace_append hprefix tailTrace_1410866
  have hstable : (prefixWord ++ tailWord_1410866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410866).length < 2 ^ (prefixWord ++ tailWord_1410866).sum := by decide
  have hdescent : baseEnd_1410866 < baseStart_1410866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410914 : List Nat := [3, 3, 2, 1, 2, 2, 2, 2, 4]
def baseStart_1410914 : Nat := 118140960795 + 1410914 * 2 ^ 59
def prefixEnd_1410914 : Nat := 4983230072969 + 3 ^ 40 * 1410914 * 2
def baseEnd_1410914 : Nat := 321989797403465789416147

theorem tailTrace_1410914 : CollatzResearch.WordTrace tailWord_1410914 prefixEnd_1410914 321989797403465789416147 := by
  unfold tailWord_1410914
  simp only [CollatzResearch.WordTrace]
  refine ⟨12865065302626754443027949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34306840807004678514741197 12865065302626754443027949)
  ·
    refine ⟨4824399488485032916135481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12865065302626754443027949 4824399488485032916135481)
    ·
      refine ⟨3618299616363774687101611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4824399488485032916135481 3618299616363774687101611)
      ·
        refine ⟨5427449424545662030652417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3618299616363774687101611 5427449424545662030652417)
        ·
          refine ⟨4070587068409246522989313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5427449424545662030652417 4070587068409246522989313)
          ·
            refine ⟨3052940301306934892241985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4070587068409246522989313 3052940301306934892241985)
            ·
              refine ⟨2289705225980201169181489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3052940301306934892241985 2289705225980201169181489)
              ·
                refine ⟨1717278919485150876886117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2289705225980201169181489 1717278919485150876886117)
                ·
                  refine ⟨321989797403465789416147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1717278919485150876886117 321989797403465789416147)
                  ·
                    rfl

theorem cell21_1410914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_1410914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1410914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1410914 prefixEnd_1410914 := by exact prefixLift 1410914
  have htrace : WordTrace (prefixWord ++ tailWord_1410914) baseStart_1410914 baseEnd_1410914 := by
    simpa [prefixWord, tailWord_1410914, baseEnd_1410914] using wordTrace_append hprefix tailTrace_1410914
  have hstable : (prefixWord ++ tailWord_1410914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410914).length < 2 ^ (prefixWord ++ tailWord_1410914).sum := by decide
  have hdescent : baseEnd_1410914 < baseStart_1410914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410939 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 8]
def baseStart_1410939 : Nat := 118140960795 + 1410939 * 2 ^ 59
def prefixEnd_1410939 : Nat := 4983230072969 + 3 ^ 40 * 1410939 * 2
def baseEnd_1410939 : Nat := 321995502744071301499429

theorem tailTrace_1410939 : CollatzResearch.WordTrace tailWord_1410939 prefixEnd_1410939 321995502744071301499429 := by
  unfold tailWord_1410939
  simp only [CollatzResearch.WordTrace]
  refine ⟨51461173035416447041771871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34307448690277631361181247 51461173035416447041771871)
  ·
    refine ⟨77191759553124670562657807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51461173035416447041771871 77191759553124670562657807)
    ·
      refine ⟨115787639329687005843986711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77191759553124670562657807 115787639329687005843986711)
      ·
        refine ⟨173681458994530508765980067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115787639329687005843986711 173681458994530508765980067)
        ·
          refine ⟨260522188491795763148970101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173681458994530508765980067 260522188491795763148970101)
          ·
            refine ⟨24423955171105852795215947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 260522188491795763148970101 24423955171105852795215947)
            ·
              refine ⟨36635932756658779192823921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24423955171105852795215947 36635932756658779192823921)
              ·
                refine ⟨27476949567494084394617941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36635932756658779192823921 27476949567494084394617941)
                ·
                  refine ⟨321995502744071301499429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27476949567494084394617941 321995502744071301499429)
                  ·
                    rfl

theorem cell21_1410939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 8].length) (baseStart_1410939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1410939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1410939 prefixEnd_1410939 := by exact prefixLift 1410939
  have htrace : WordTrace (prefixWord ++ tailWord_1410939) baseStart_1410939 baseEnd_1410939 := by
    simpa [prefixWord, tailWord_1410939, baseEnd_1410939] using wordTrace_append hprefix tailTrace_1410939
  have hstable : (prefixWord ++ tailWord_1410939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410939).length < 2 ^ (prefixWord ++ tailWord_1410939).sum := by decide
  have hdescent : baseEnd_1410939 < baseStart_1410939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410945 : List Nat := [1, 2, 4, 4, 1, 1, 3, 5]
def baseStart_1410945 : Nat := 118140960795 + 1410945 * 2 ^ 59
def prefixEnd_1410945 : Nat := 4983230072969 + 3 ^ 40 * 1410945 * 2
def baseEnd_1410945 : Nat := 107332290675272208133139

theorem tailTrace_1410945 : CollatzResearch.WordTrace tailWord_1410945 prefixEnd_1410945 107332290675272208133139 := by
  unfold tailWord_1410945
  simp only [CollatzResearch.WordTrace]
  refine ⟨51461391873394710066490289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34307594582263140044326859 51461391873394710066490289)
  ·
    refine ⟨38596043905046032549867717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51461391873394710066490289 38596043905046032549867717)
    ·
      refine ⟨7236758232196131103100197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38596043905046032549867717 7236758232196131103100197)
      ·
        refine ⟨1356892168536774581831287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7236758232196131103100197 1356892168536774581831287)
        ·
          refine ⟨2035338252805161872746931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1356892168536774581831287 2035338252805161872746931)
          ·
            refine ⟨3053007379207742809120397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2035338252805161872746931 3053007379207742809120397)
            ·
              refine ⟨1144877767202903553420149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3053007379207742809120397 1144877767202903553420149)
              ·
                refine ⟨107332290675272208133139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1144877767202903553420149 107332290675272208133139)
                ·
                  rfl

theorem cell21_1410945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 5].length) (baseStart_1410945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1410945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1410945 prefixEnd_1410945 := by exact prefixLift 1410945
  have htrace : WordTrace (prefixWord ++ tailWord_1410945) baseStart_1410945 baseEnd_1410945 := by
    simpa [prefixWord, tailWord_1410945, baseEnd_1410945] using wordTrace_append hprefix tailTrace_1410945
  have hstable : (prefixWord ++ tailWord_1410945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410945).length < 2 ^ (prefixWord ++ tailWord_1410945).sum := by decide
  have hdescent : baseEnd_1410945 < baseStart_1410945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410973 : List Nat := [1, 4, 2, 1, 2, 2, 3, 2, 4]
def baseStart_1410973 : Nat := 118140960795 + 1410973 * 2 ^ 59
def prefixEnd_1410973 : Nat := 4983230072969 + 3 ^ 40 * 1410973 * 2
def baseEnd_1410973 : Nat := 322003262007294797932693

theorem tailTrace_1410973 : CollatzResearch.WordTrace tailWord_1410973 prefixEnd_1410973 322003262007294797932693 := by
  unfold tailWord_1410973
  simp only [CollatzResearch.WordTrace]
  refine ⟨51462413117293270848509573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34308275411528847232339715 51462413117293270848509573)
  ·
    refine ⟨9649202459492488284095545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51462413117293270848509573 9649202459492488284095545)
    ·
      refine ⟨7236901844619366213071659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9649202459492488284095545 7236901844619366213071659)
      ·
        refine ⟨10855352766929049319607489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7236901844619366213071659 10855352766929049319607489)
        ·
          refine ⟨8141514575196786989705617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10855352766929049319607489 8141514575196786989705617)
          ·
            refine ⟨6106135931397590242279213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8141514575196786989705617 6106135931397590242279213)
            ·
              refine ⟨2289800974274096340854705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6106135931397590242279213 2289800974274096340854705)
              ·
                refine ⟨1717350730705572255641029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2289800974274096340854705 1717350730705572255641029)
                ·
                  refine ⟨322003262007294797932693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1717350730705572255641029 322003262007294797932693)
                  ·
                    rfl

theorem cell21_1410973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_1410973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1410973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1410973 prefixEnd_1410973 := by exact prefixLift 1410973
  have htrace : WordTrace (prefixWord ++ tailWord_1410973) baseStart_1410973 baseEnd_1410973 := by
    simpa [prefixWord, tailWord_1410973, baseEnd_1410973] using wordTrace_append hprefix tailTrace_1410973
  have hstable : (prefixWord ++ tailWord_1410973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410973).length < 2 ^ (prefixWord ++ tailWord_1410973).sum := by decide
  have hdescent : baseEnd_1410973 < baseStart_1410973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411001 : List Nat := [1, 2, 1, 4, 2, 1, 1, 4, 5]
def baseStart_1411001 : Nat := 118140960795 + 1411001 * 2 ^ 59
def prefixEnd_1411001 : Nat := 4983230072969 + 3 ^ 40 * 1411001 * 2
def baseEnd_1411001 : Nat := 322009651988772971465969

theorem tailTrace_1411001 : CollatzResearch.WordTrace tailWord_1411001 prefixEnd_1411001 322009651988772971465969 := by
  unfold tailWord_1411001
  simp only [CollatzResearch.WordTrace]
  refine ⟨51463434361191831630528857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34308956240794554420352571 51463434361191831630528857)
  ·
    refine ⟨38597575770893873722896643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51463434361191831630528857 38597575770893873722896643)
    ·
      refine ⟨57896363656340810584344965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38597575770893873722896643 57896363656340810584344965)
      ·
        refine ⟨10855568185563901984564681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57896363656340810584344965 10855568185563901984564681)
        ·
          refine ⟨8141676139172926488423511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10855568185563901984564681 8141676139172926488423511)
          ·
            refine ⟨12212514208759389732635267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8141676139172926488423511 12212514208759389732635267)
            ·
              refine ⟨18318771313139084598952901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12212514208759389732635267 18318771313139084598952901)
              ·
                refine ⟨3434769621213578362303669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18318771313139084598952901 3434769621213578362303669)
                ·
                  refine ⟨322009651988772971465969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3434769621213578362303669 322009651988772971465969)
                  ·
                    rfl

theorem cell21_1411001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 5].length) (baseStart_1411001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1411001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1411001 prefixEnd_1411001 := by exact prefixLift 1411001
  have htrace : WordTrace (prefixWord ++ tailWord_1411001) baseStart_1411001 baseEnd_1411001 := by
    simpa [prefixWord, tailWord_1411001, baseEnd_1411001] using wordTrace_append hprefix tailTrace_1411001
  have hstable : (prefixWord ++ tailWord_1411001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411001).length < 2 ^ (prefixWord ++ tailWord_1411001).sum := by decide
  have hdescent : baseEnd_1411001 < baseStart_1411001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
