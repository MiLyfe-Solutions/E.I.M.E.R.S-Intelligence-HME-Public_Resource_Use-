import V185TrunkScan23Chunk0791

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4684095 : List Nat := [1, 1, 2, 2, 4, 1, 4, 1, 7]
def baseStart_4684095 : Nat := 118140960795 + 4684095 * 2 ^ 59
def prefixEnd_4684095 : Nat := 4983230072969 + 3 ^ 40 * 4684095 * 2
def baseEnd_4684095 : Nat := 267243574035772910052305

theorem tailTrace_4684095 : CollatzResearch.WordTrace tailWord_4684095 prefixEnd_4684095 267243574035772910052305 := by
  unfold tailWord_4684095
  simp only [CollatzResearch.WordTrace]
  refine ⟨170842979965331269581469739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113895319976887513054313159 170842979965331269581469739)
  ·
    refine ⟨256264469947996904372204609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170842979965331269581469739 256264469947996904372204609)
    ·
      refine ⟨192198352460997678279153457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256264469947996904372204609 192198352460997678279153457)
      ·
        refine ⟨144148764345748258709365093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192198352460997678279153457 144148764345748258709365093)
        ·
          refine ⟨27027893314827798508005955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144148764345748258709365093 27027893314827798508005955)
          ·
            refine ⟨40541839972241697762008933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27027893314827798508005955 40541839972241697762008933)
            ·
              refine ⟨7601594994795318330376675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40541839972241697762008933 7601594994795318330376675)
              ·
                refine ⟨11402392492192977495565013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7601594994795318330376675 11402392492192977495565013)
                ·
                  refine ⟨267243574035772910052305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11402392492192977495565013 267243574035772910052305)
                  ·
                    rfl

theorem cell23_4684095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 7].length) (baseStart_4684095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684095 prefixEnd_4684095 := by exact prefixLift 4684095
  have htrace : WordTrace (prefixWord ++ tailWord_4684095) baseStart_4684095 baseEnd_4684095 := by
    simpa [prefixWord, tailWord_4684095, baseEnd_4684095] using wordTrace_append hprefix tailTrace_4684095
  have hstable : (prefixWord ++ tailWord_4684095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684095).length < 2 ^ (prefixWord ++ tailWord_4684095).sum := by decide
  have hdescent : baseEnd_4684095 < baseStart_4684095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684199 : List Nat := [1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_4684199 : Nat := 118140960795 + 4684199 * 2 ^ 59
def prefixEnd_4684199 : Nat := 4983230072969 + 3 ^ 40 * 4684199 * 2
def baseEnd_4684199 : Nat := 2405245568310023783570267

theorem tailTrace_4684199 : CollatzResearch.WordTrace tailWord_4684199 prefixEnd_4684199 2405245568310023783570267 := by
  unfold tailWord_4684199
  simp only [CollatzResearch.WordTrace]
  refine ⟨170846773156954495343255651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113897848771302996895503767 170846773156954495343255651)
  ·
    refine ⟨256270159735431743014883477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170846773156954495343255651 256270159735431743014883477)
    ·
      refine ⟨12012663737598362953822663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 256270159735431743014883477 12012663737598362953822663)
      ·
        refine ⟨18018995606397544430733995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12012663737598362953822663 18018995606397544430733995)
        ·
          refine ⟨27028493409596316646100993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18018995606397544430733995 27028493409596316646100993)
          ·
            refine ⟨20271370057197237484575745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27028493409596316646100993 20271370057197237484575745)
            ·
              refine ⟨15203527542897928113431809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20271370057197237484575745 15203527542897928113431809)
              ·
                refine ⟨11402645657173446085073857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15203527542897928113431809 11402645657173446085073857)
                ·
                  refine ⟨8551984242880084563805393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11402645657173446085073857 8551984242880084563805393)
                  ·
                    refine ⟨6413988182160063422854045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8551984242880084563805393 6413988182160063422854045)
                    ·
                      refine ⟨2405245568310023783570267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6413988182160063422854045 2405245568310023783570267)
                      ·
                        rfl

theorem cell23_4684199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_4684199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684199 prefixEnd_4684199 := by exact prefixLift 4684199
  have htrace : WordTrace (prefixWord ++ tailWord_4684199) baseStart_4684199 baseEnd_4684199 := by
    simpa [prefixWord, tailWord_4684199, baseEnd_4684199] using wordTrace_append hprefix tailTrace_4684199
  have hstable : (prefixWord ++ tailWord_4684199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684199).length < 2 ^ (prefixWord ++ tailWord_4684199).sum := by decide
  have hdescent : baseEnd_4684199 < baseStart_4684199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684232 : List Nat := [2, 1, 3, 1, 3, 2, 2, 1, 3, 5]
def baseStart_4684232 : Nat := 118140960795 + 4684232 * 2 ^ 59
def prefixEnd_4684232 : Nat := 4983230072969 + 3 ^ 40 * 4684232 * 2
def baseEnd_4684232 : Nat := 801754171057207384819205

theorem tailTrace_4684232 : CollatzResearch.WordTrace tailWord_4684232 prefixEnd_4684232 801754171057207384819205 := by
  unfold tailWord_4684232
  simp only [CollatzResearch.WordTrace]
  refine ⟨85423988382917470989603475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113898651177223294652804633 85423988382917470989603475)
  ·
    refine ⟨128135982574376206484405213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85423988382917470989603475 128135982574376206484405213)
    ·
      refine ⟨48050993465391077431651955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128135982574376206484405213 48050993465391077431651955)
      ·
        refine ⟨72076490198086616147477933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48050993465391077431651955 72076490198086616147477933)
        ·
          refine ⟨27028683824282481055304225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72076490198086616147477933 27028683824282481055304225)
          ·
            refine ⟨20271512868211860791478169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27028683824282481055304225 20271512868211860791478169)
            ·
              refine ⟨15203634651158895593608627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20271512868211860791478169 15203634651158895593608627)
              ·
                refine ⟨22805451976738343390412941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15203634651158895593608627 22805451976738343390412941)
                ·
                  refine ⟨8552044491276878771404853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22805451976738343390412941 8552044491276878771404853)
                  ·
                    refine ⟨801754171057207384819205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8552044491276878771404853 801754171057207384819205)
                    ·
                      rfl

theorem cell23_4684232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_4684232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684232 prefixEnd_4684232 := by exact prefixLift 4684232
  have htrace : WordTrace (prefixWord ++ tailWord_4684232) baseStart_4684232 baseEnd_4684232 := by
    simpa [prefixWord, tailWord_4684232, baseEnd_4684232] using wordTrace_append hprefix tailTrace_4684232
  have hstable : (prefixWord ++ tailWord_4684232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684232).length < 2 ^ (prefixWord ++ tailWord_4684232).sum := by decide
  have hdescent : baseEnd_4684232 < baseStart_4684232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684246 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3]
def baseStart_4684246 : Nat := 118140960795 + 4684246 * 2 ^ 59
def prefixEnd_4684246 : Nat := 4983230072969 + 3 ^ 40 * 4684246 * 2
def baseEnd_4684246 : Nat := 2405269701900785099682551

theorem tailTrace_4684246 : CollatzResearch.WordTrace tailWord_4684246 prefixEnd_4684246 2405269701900785099682551 := by
  unfold tailWord_4684246
  simp only [CollatzResearch.WordTrace]
  refine ⟨10678030461736513898138537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113898991591856148246811061 10678030461736513898138537)
  ·
    refine ⟨8008522846302385423603903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10678030461736513898138537 8008522846302385423603903)
    ·
      refine ⟨12012784269453578135405855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8008522846302385423603903 12012784269453578135405855)
      ·
        refine ⟨18019176404180367203108783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12012784269453578135405855 18019176404180367203108783)
        ·
          refine ⟨27028764606270550804663175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18019176404180367203108783 27028764606270550804663175)
          ·
            refine ⟨40543146909405826206994763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27028764606270550804663175 40543146909405826206994763)
            ·
              refine ⟨60814720364108739310492145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40543146909405826206994763 60814720364108739310492145)
              ·
                refine ⟨45611040273081554482869109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60814720364108739310492145 45611040273081554482869109)
                ·
                  refine ⟨4276035025601395732768979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45611040273081554482869109 4276035025601395732768979)
                  ·
                    refine ⟨6414052538402093599153469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4276035025601395732768979 6414052538402093599153469)
                    ·
                      refine ⟨2405269701900785099682551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6414052538402093599153469 2405269701900785099682551)
                      ·
                        rfl

theorem cell23_4684246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_4684246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684246 prefixEnd_4684246 := by exact prefixLift 4684246
  have htrace : WordTrace (prefixWord ++ tailWord_4684246) baseStart_4684246 baseEnd_4684246 := by
    simpa [prefixWord, tailWord_4684246, baseEnd_4684246] using wordTrace_append hprefix tailTrace_4684246
  have hstable : (prefixWord ++ tailWord_4684246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684246).length < 2 ^ (prefixWord ++ tailWord_4684246).sum := by decide
  have hdescent : baseEnd_4684246 < baseStart_4684246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684272 : List Nat := [2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 5]
def baseStart_4684272 : Nat := 118140960795 + 4684272 * 2 ^ 59
def prefixEnd_4684272 : Nat := 4983230072969 + 3 ^ 40 * 4684272 * 2
def baseEnd_4684272 : Nat := 2405283052397801997957431

theorem tailTrace_4684272 : CollatzResearch.WordTrace tailWord_4684272 prefixEnd_4684272 2405283052397801997957431 := by
  unfold tailWord_4684272
  simp only [CollatzResearch.WordTrace]
  refine ⟨85424717842845014405331535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113899623790460019207108713 85424717842845014405331535)
  ·
    refine ⟨128137076764267521607997303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85424717842845014405331535 128137076764267521607997303)
    ·
      refine ⟨192205615146401282411995955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128137076764267521607997303 192205615146401282411995955)
      ·
        refine ⟨288308422719601923617993933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192205615146401282411995955 288308422719601923617993933)
        ·
          refine ⟨108115658519850721356747725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 288308422719601923617993933 108115658519850721356747725)
          ·
            refine ⟨40543371944944020508780397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108115658519850721356747725 40543371944944020508780397)
            ·
              refine ⟨15203764479354007690792649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40543371944944020508780397 15203764479354007690792649)
              ·
                refine ⟨11402823359515505768094487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15203764479354007690792649 11402823359515505768094487)
                ·
                  refine ⟨17104235039273258652141731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11402823359515505768094487 17104235039273258652141731)
                  ·
                    refine ⟨25656352558909887978212597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17104235039273258652141731 25656352558909887978212597)
                    ·
                      refine ⟨2405283052397801997957431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25656352558909887978212597 2405283052397801997957431)
                      ·
                        rfl

theorem cell23_4684272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 5].length) (baseStart_4684272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684272 prefixEnd_4684272 := by exact prefixLift 4684272
  have htrace : WordTrace (prefixWord ++ tailWord_4684272) baseStart_4684272 baseEnd_4684272 := by
    simpa [prefixWord, tailWord_4684272, baseEnd_4684272] using wordTrace_append hprefix tailTrace_4684272
  have hstable : (prefixWord ++ tailWord_4684272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684272).length < 2 ^ (prefixWord ++ tailWord_4684272).sum := by decide
  have hdescent : baseEnd_4684272 < baseStart_4684272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684275 : List Nat := [1, 1, 1, 2, 2, 2, 4, 10]
def baseStart_4684275 : Nat := 118140960795 + 4684275 * 2 ^ 59
def prefixEnd_4684275 : Nat := 4983230072969 + 3 ^ 40 * 4684275 * 2
def baseEnd_4684275 : Nat := 89084614549620943934071

theorem tailTrace_4684275 : CollatzResearch.WordTrace tailWord_4684275 prefixEnd_4684275 89084614549620943934071 := by
  unfold tailWord_4684275
  simp only [CollatzResearch.WordTrace]
  refine ⟨170849545104679160323022279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113899696736452773548681519 170849545104679160323022279)
  ·
    refine ⟨256274317657018740484533419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170849545104679160323022279 256274317657018740484533419)
    ·
      refine ⟨384411476485528110726800129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256274317657018740484533419 384411476485528110726800129)
      ·
        refine ⟨288308607364146083045100097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 384411476485528110726800129 288308607364146083045100097)
        ·
          refine ⟨216231455523109562283825073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288308607364146083045100097 216231455523109562283825073)
          ·
            refine ⟨162173591642332171712868805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216231455523109562283825073 162173591642332171712868805)
            ·
              refine ⟨30407548432937282196162901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 162173591642332171712868805 30407548432937282196162901)
              ·
                refine ⟨89084614549620943934071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30407548432937282196162901 89084614549620943934071)
                ·
                  rfl

theorem cell23_4684275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 10].length) (baseStart_4684275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684275 prefixEnd_4684275 := by exact prefixLift 4684275
  have htrace : WordTrace (prefixWord ++ tailWord_4684275) baseStart_4684275 baseEnd_4684275 := by
    simpa [prefixWord, tailWord_4684275, baseEnd_4684275] using wordTrace_append hprefix tailTrace_4684275
  have hstable : (prefixWord ++ tailWord_4684275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684275).length < 2 ^ (prefixWord ++ tailWord_4684275).sum := by decide
  have hdescent : baseEnd_4684275 < baseStart_4684275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684282 : List Nat := [3, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4]
def baseStart_4684282 : Nat := 118140960795 + 4684282 * 2 ^ 59
def prefixEnd_4684282 : Nat := 4983230072969 + 3 ^ 40 * 4684282 * 2
def baseEnd_4684282 : Nat := 2405288187204346958832385

theorem tailTrace_4684282 : CollatzResearch.WordTrace tailWord_4684282 prefixEnd_4684282 2405288187204346958832385 := by
  unfold tailWord_4684282
  simp only [CollatzResearch.WordTrace]
  refine ⟨42712450103913450129631775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113899866943769200345684733 42712450103913450129631775)
  ·
    refine ⟨64068675155870175194447663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42712450103913450129631775 64068675155870175194447663)
    ·
      refine ⟨96103012733805262791671495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64068675155870175194447663 96103012733805262791671495)
      ·
        refine ⟨144154519100707894187507243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96103012733805262791671495 144154519100707894187507243)
        ·
          refine ⟨216231778651061841281260865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144154519100707894187507243 216231778651061841281260865)
          ·
            refine ⟨162173833988296380960945649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216231778651061841281260865 162173833988296380960945649)
            ·
              refine ⟨121630375491222285720709237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162173833988296380960945649 121630375491222285720709237)
              ·
                refine ⟨11402847702302089286316491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121630375491222285720709237 11402847702302089286316491)
                ·
                  refine ⟨17104271553453133929474737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11402847702302089286316491 17104271553453133929474737)
                  ·
                    refine ⟨12828203665089850447106053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17104271553453133929474737 12828203665089850447106053)
                    ·
                      refine ⟨2405288187204346958832385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12828203665089850447106053 2405288187204346958832385)
                      ·
                        rfl

theorem cell23_4684282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_4684282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684282 prefixEnd_4684282 := by exact prefixLift 4684282
  have htrace : WordTrace (prefixWord ++ tailWord_4684282) baseStart_4684282 baseEnd_4684282 := by
    simpa [prefixWord, tailWord_4684282, baseEnd_4684282] using wordTrace_append hprefix tailTrace_4684282
  have hstable : (prefixWord ++ tailWord_4684282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684282).length < 2 ^ (prefixWord ++ tailWord_4684282).sum := by decide
  have hdescent : baseEnd_4684282 < baseStart_4684282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684320 : List Nat := [2, 1, 1, 6, 2, 2, 1, 1, 3, 2, 2]
def baseStart_4684320 : Nat := 118140960795 + 4684320 * 2 ^ 59
def prefixEnd_4684320 : Nat := 4983230072969 + 3 ^ 40 * 4684320 * 2
def baseEnd_4684320 : Nat := 2405307699469217810157211

theorem tailTrace_4684320 : CollatzResearch.WordTrace tailWord_4684320 prefixEnd_4684320 2405307699469217810157211 := by
  unfold tailWord_4684320
  simp only [CollatzResearch.WordTrace]
  refine ⟨85425593194758066504205207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113900790926344088672273609 85425593194758066504205207)
  ·
    refine ⟨128138389792137099756307811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85425593194758066504205207 128138389792137099756307811)
    ·
      refine ⟨192207584688205649634461717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128138389792137099756307811 192207584688205649634461717)
      ·
        refine ⟨9009730532259639826615393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 192207584688205649634461717 9009730532259639826615393)
        ·
          refine ⟨6757297899194729869961545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9009730532259639826615393 6757297899194729869961545)
          ·
            refine ⟨5067973424396047402471159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6757297899194729869961545 5067973424396047402471159)
            ·
              refine ⟨7601960136594071103706739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5067973424396047402471159 7601960136594071103706739)
              ·
                refine ⟨11402940204891106655560109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7601960136594071103706739 11402940204891106655560109)
                ·
                  refine ⟨4276102576834164995835041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11402940204891106655560109 4276102576834164995835041)
                  ·
                    refine ⟨3207076932625623746876281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4276102576834164995835041 3207076932625623746876281)
                    ·
                      refine ⟨2405307699469217810157211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3207076932625623746876281 2405307699469217810157211)
                      ·
                        rfl

theorem cell23_4684320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_4684320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684320 prefixEnd_4684320 := by exact prefixLift 4684320
  have htrace : WordTrace (prefixWord ++ tailWord_4684320) baseStart_4684320 baseEnd_4684320 := by
    simpa [prefixWord, tailWord_4684320, baseEnd_4684320] using wordTrace_append hprefix tailTrace_4684320
  have hstable : (prefixWord ++ tailWord_4684320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684320).length < 2 ^ (prefixWord ++ tailWord_4684320).sum := by decide
  have hdescent : baseEnd_4684320 < baseStart_4684320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684322 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 2, 7]
def baseStart_4684322 : Nat := 118140960795 + 4684322 * 2 ^ 59
def prefixEnd_4684322 : Nat := 4983230072969 + 3 ^ 40 * 4684322 * 2
def baseEnd_4684322 : Nat := 801769575476842267444067

theorem tailTrace_4684322 : CollatzResearch.WordTrace tailWord_4684322 prefixEnd_4684322 801769575476842267444067 := by
  unfold tailWord_4684322
  simp only [CollatzResearch.WordTrace]
  refine ⟨42712814833877221837495805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113900839557005924899988813 42712814833877221837495805)
  ·
    refine ⟨16017305562703958189060927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42712814833877221837495805 16017305562703958189060927)
    ·
      refine ⟨24025958344055937283591391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16017305562703958189060927 24025958344055937283591391)
      ·
        refine ⟨36038937516083905925387087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24025958344055937283591391 36038937516083905925387087)
        ·
          refine ⟨54058406274125858888080631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36038937516083905925387087 54058406274125858888080631)
          ·
            refine ⟨81087609411188788332120947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54058406274125858888080631 81087609411188788332120947)
            ·
              refine ⟨121631414116783182498181421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81087609411188788332120947 121631414116783182498181421)
              ·
                refine ⟨45611780293793693436818033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121631414116783182498181421 45611780293793693436818033)
                ·
                  refine ⟨34208835220345270077613525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45611780293793693436818033 34208835220345270077613525)
                  ·
                    refine ⟨801769575476842267444067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34208835220345270077613525 801769575476842267444067)
                    ·
                      rfl

theorem cell23_4684322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_4684322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684322 prefixEnd_4684322 := by exact prefixLift 4684322
  have htrace : WordTrace (prefixWord ++ tailWord_4684322) baseStart_4684322 baseEnd_4684322 := by
    simpa [prefixWord, tailWord_4684322, baseEnd_4684322] using wordTrace_append hprefix tailTrace_4684322
  have hstable : (prefixWord ++ tailWord_4684322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684322).length < 2 ^ (prefixWord ++ tailWord_4684322).sum := by decide
  have hdescent : baseEnd_4684322 < baseStart_4684322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684346 : List Nat := [3, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2]
def baseStart_4684346 : Nat := 118140960795 + 4684346 * 2 ^ 59
def prefixEnd_4684346 : Nat := 4983230072969 + 3 ^ 40 * 4684346 * 2
def baseEnd_4684346 : Nat := 2405321049966234708432091

theorem tailTrace_4684346 : CollatzResearch.WordTrace tailWord_4684346 prefixEnd_4684346 2405321049966234708432091 := by
  unfold tailWord_4684346
  simp only [CollatzResearch.WordTrace]
  refine ⟨42713033671855484862214223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113901423124947959632571261 42713033671855484862214223)
  ·
    refine ⟨64069550507783227293321335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42713033671855484862214223 64069550507783227293321335)
    ·
      refine ⟨96104325761674840939982003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64069550507783227293321335 96104325761674840939982003)
      ·
        refine ⟨144156488642512261409973005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96104325761674840939982003 144156488642512261409973005)
        ·
          refine ⟨54058683240942098028739877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144156488642512261409973005 54058683240942098028739877)
          ·
            refine ⟨10136003107676643380388727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54058683240942098028739877 10136003107676643380388727)
            ·
              refine ⟨15204004661514965070583091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10136003107676643380388727 15204004661514965070583091)
              ·
                refine ⟨22806006992272447605874637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15204004661514965070583091 22806006992272447605874637)
                ·
                  refine ⟨8552252622102167852202989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22806006992272447605874637 8552252622102167852202989)
                  ·
                    refine ⟨3207094733288312944576121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8552252622102167852202989 3207094733288312944576121)
                    ·
                      refine ⟨2405321049966234708432091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3207094733288312944576121 2405321049966234708432091)
                      ·
                        rfl

theorem cell23_4684346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2].length) (baseStart_4684346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684346 prefixEnd_4684346 := by exact prefixLift 4684346
  have htrace : WordTrace (prefixWord ++ tailWord_4684346) baseStart_4684346 baseEnd_4684346 := by
    simpa [prefixWord, tailWord_4684346, baseEnd_4684346] using wordTrace_append hprefix tailTrace_4684346
  have hstable : (prefixWord ++ tailWord_4684346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684346).length < 2 ^ (prefixWord ++ tailWord_4684346).sum := by decide
  have hdescent : baseEnd_4684346 < baseStart_4684346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684376 : List Nat := [2, 1, 2, 2, 1, 2, 2, 3, 4, 2, 2]
def baseStart_4684376 : Nat := 118140960795 + 4684376 * 2 ^ 59
def prefixEnd_4684376 : Nat := 4983230072969 + 3 ^ 40 * 4684376 * 2
def baseEnd_4684376 : Nat := 2405336454385869591056953

theorem tailTrace_4684376 : CollatzResearch.WordTrace tailWord_4684376 prefixEnd_4684376 2405336454385869591056953 := by
  unfold tailWord_4684376
  simp only [CollatzResearch.WordTrace]
  refine ⟨85426614438656627286224491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113902152584875503048299321 85426614438656627286224491)
  ·
    refine ⟨128139921657984940929336737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85426614438656627286224491 128139921657984940929336737)
    ·
      refine ⟨96104941243488705697002553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128139921657984940929336737 96104941243488705697002553)
      ·
        refine ⟨72078705932616529272751915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96104941243488705697002553 72078705932616529272751915)
        ·
          refine ⟨108118058898924793909127873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72078705932616529272751915 108118058898924793909127873)
          ·
            refine ⟨81088544174193595431845905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108118058898924793909127873 81088544174193595431845905)
            ·
              refine ⟨60816408130645196573884429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81088544174193595431845905 60816408130645196573884429)
              ·
                refine ⟨22806153048991948715206661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60816408130645196573884429 22806153048991948715206661)
                ·
                  refine ⟨4276153696685990384101249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22806153048991948715206661 4276153696685990384101249)
                  ·
                    refine ⟨3207115272514492788075937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4276153696685990384101249 3207115272514492788075937)
                    ·
                      refine ⟨2405336454385869591056953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3207115272514492788075937 2405336454385869591056953)
                      ·
                        rfl

theorem cell23_4684376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 4, 2, 2].length) (baseStart_4684376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684376 prefixEnd_4684376 := by exact prefixLift 4684376
  have htrace : WordTrace (prefixWord ++ tailWord_4684376) baseStart_4684376 baseEnd_4684376 := by
    simpa [prefixWord, tailWord_4684376, baseEnd_4684376] using wordTrace_append hprefix tailTrace_4684376
  have hstable : (prefixWord ++ tailWord_4684376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684376).length < 2 ^ (prefixWord ++ tailWord_4684376).sum := by decide
  have hdescent : baseEnd_4684376 < baseStart_4684376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684416 : List Nat := [2, 1, 1, 2, 1, 6, 2, 3, 5]
def baseStart_4684416 : Nat := 118140960795 + 4684416 * 2 ^ 59
def prefixEnd_4684416 : Nat := 4983230072969 + 3 ^ 40 * 4684416 * 2
def baseEnd_4684416 : Nat := 267261888179116603839641

theorem tailTrace_4684416 : CollatzResearch.WordTrace tailWord_4684416 prefixEnd_4684416 267261888179116603839641 := by
  unfold tailWord_4684416
  simp only [CollatzResearch.WordTrace]
  refine ⟨85427343898584170701952551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113903125198112227602603401 85427343898584170701952551)
  ·
    refine ⟨128141015847876256052928827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85427343898584170701952551 128141015847876256052928827)
    ·
      refine ⟨192211523771814384079393241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128141015847876256052928827 192211523771814384079393241)
      ·
        refine ⟨144158642828860788059544931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192211523771814384079393241 144158642828860788059544931)
        ·
          refine ⟨216237964243291182089317397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144158642828860788059544931 216237964243291182089317397)
          ·
            refine ⟨10136154573904274160436753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 216237964243291182089317397 10136154573904274160436753)
            ·
              refine ⟨7602115930428205620327565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10136154573904274160436753 7602115930428205620327565)
              ·
                refine ⟨2850793473910577107622837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7602115930428205620327565 2850793473910577107622837)
                ·
                  refine ⟨267261888179116603839641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2850793473910577107622837 267261888179116603839641)
                  ·
                    rfl

theorem cell23_4684416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3, 5].length) (baseStart_4684416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684416 prefixEnd_4684416 := by exact prefixLift 4684416
  have htrace : WordTrace (prefixWord ++ tailWord_4684416) baseStart_4684416 baseEnd_4684416 := by
    simpa [prefixWord, tailWord_4684416, baseEnd_4684416] using wordTrace_append hprefix tailTrace_4684416
  have hstable : (prefixWord ++ tailWord_4684416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684416).length < 2 ^ (prefixWord ++ tailWord_4684416).sum := by decide
  have hdescent : baseEnd_4684416 < baseStart_4684416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684556 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 2, 6, 2]
def baseStart_4684556 : Nat := 118140960795 + 4684556 * 2 ^ 59
def prefixEnd_4684556 : Nat := 4983230072969 + 3 ^ 40 * 4684556 * 2
def baseEnd_4684556 : Nat := 2405428880903678886806125

theorem tailTrace_4684556 : CollatzResearch.WordTrace tailWord_4684556 prefixEnd_4684556 2405428880903678886806125 := by
  unfold tailWord_4684556
  simp only [CollatzResearch.WordTrace]
  refine ⟨85429897008330572657000761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113906529344440763542667681 85429897008330572657000761)
  ·
    refine ⟨64072422756247929492750571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85429897008330572657000761 64072422756247929492750571)
    ·
      refine ⟨96108634134371894239125857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64072422756247929492750571 96108634134371894239125857)
      ·
        refine ⟨72081475600778920679344393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96108634134371894239125857 72081475600778920679344393)
        ·
          refine ⟨54061106700584190509508295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72081475600778920679344393 54061106700584190509508295)
          ·
            refine ⟨81091660050876285764262443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54061106700584190509508295 81091660050876285764262443)
            ·
              refine ⟨121637490076314428646393665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81091660050876285764262443 121637490076314428646393665)
              ·
                refine ⟨91228117557235821484795249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121637490076314428646393665 91228117557235821484795249)
                ·
                  refine ⟨68421088167926866113596437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91228117557235821484795249 68421088167926866113596437)
                  ·
                    refine ⟨3207238507871571849074833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68421088167926866113596437 3207238507871571849074833)
                    ·
                      refine ⟨2405428880903678886806125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3207238507871571849074833 2405428880903678886806125)
                      ·
                        rfl

theorem cell23_4684556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 6, 2].length) (baseStart_4684556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684556 prefixEnd_4684556 := by exact prefixLift 4684556
  have htrace : WordTrace (prefixWord ++ tailWord_4684556) baseStart_4684556 baseEnd_4684556 := by
    simpa [prefixWord, tailWord_4684556, baseEnd_4684556] using wordTrace_append hprefix tailTrace_4684556
  have hstable : (prefixWord ++ tailWord_4684556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684556).length < 2 ^ (prefixWord ++ tailWord_4684556).sum := by decide
  have hdescent : baseEnd_4684556 < baseStart_4684556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684559 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 5]
def baseStart_4684559 : Nat := 118140960795 + 4684559 * 2 ^ 59
def prefixEnd_4684559 : Nat := 4983230072969 + 3 ^ 40 * 4684559 * 2
def baseEnd_4684559 : Nat := 2405430421345642375068611

theorem tailTrace_4684559 : CollatzResearch.WordTrace tailWord_4684559 prefixEnd_4684559 2405430421345642375068611 := by
  unfold tailWord_4684559
  simp only [CollatzResearch.WordTrace]
  refine ⟨170859903435650276826360731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113906602290433517884240487 170859903435650276826360731)
  ·
    refine ⟨256289855153475415239541097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170859903435650276826360731 256289855153475415239541097)
    ·
      refine ⟨192217391365106561429655823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256289855153475415239541097 192217391365106561429655823)
      ·
        refine ⟨288326087047659842144483735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192217391365106561429655823 288326087047659842144483735)
        ·
          refine ⟨432489130571489763216725603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288326087047659842144483735 432489130571489763216725603)
          ·
            refine ⟨648733695857234644825088405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432489130571489763216725603 648733695857234644825088405)
            ·
              refine ⟨30409391993307873976176019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 648733695857234644825088405 30409391993307873976176019)
              ·
                refine ⟨45614087989961810964264029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30409391993307873976176019 45614087989961810964264029)
                ·
                  refine ⟨17105282996235679111599011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45614087989961810964264029 17105282996235679111599011)
                  ·
                    refine ⟨25657924494353518667398517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17105282996235679111599011 25657924494353518667398517)
                    ·
                      refine ⟨2405430421345642375068611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25657924494353518667398517 2405430421345642375068611)
                      ·
                        rfl

theorem cell23_4684559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 5].length) (baseStart_4684559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684559 prefixEnd_4684559 := by exact prefixLift 4684559
  have htrace : WordTrace (prefixWord ++ tailWord_4684559) baseStart_4684559 baseEnd_4684559 := by
    simpa [prefixWord, tailWord_4684559, baseEnd_4684559] using wordTrace_append hprefix tailTrace_4684559
  have hstable : (prefixWord ++ tailWord_4684559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684559).length < 2 ^ (prefixWord ++ tailWord_4684559).sum := by decide
  have hdescent : baseEnd_4684559 < baseStart_4684559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684590 : List Nat := [4, 1, 3, 2, 1, 2, 1, 3, 1, 1, 4]
def baseStart_4684590 : Nat := 118140960795 + 4684590 * 2 ^ 59
def prefixEnd_4684590 : Nat := 4983230072969 + 3 ^ 40 * 4684590 * 2
def baseEnd_4684590 : Nat := 2405446339245931753780969

theorem tailTrace_4684590 : CollatzResearch.WordTrace tailWord_4684590 prefixEnd_4684590 2405446339245931753780969 := by
  unfold tailWord_4684590
  simp only [CollatzResearch.WordTrace]
  refine ⟨21357629262317246140092403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113907356065691979413826149 21357629262317246140092403)
  ·
    refine ⟨32036443893475869210138605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21357629262317246140092403 32036443893475869210138605)
    ·
      refine ⟨12013666460053450953801977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32036443893475869210138605 12013666460053450953801977)
      ·
        refine ⟨9010249845040088215351483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12013666460053450953801977 9010249845040088215351483)
        ·
          refine ⟨13515374767560132323027225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9010249845040088215351483 13515374767560132323027225)
          ·
            refine ⟨10136531075670099242270419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13515374767560132323027225 10136531075670099242270419)
            ·
              refine ⟨15204796613505148863405629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10136531075670099242270419 15204796613505148863405629)
              ·
                refine ⟨5701798730064430823777111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15204796613505148863405629 5701798730064430823777111)
                ·
                  refine ⟨8552698095096646235665667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5701798730064430823777111 8552698095096646235665667)
                  ·
                    refine ⟨12829047142644969353498501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8552698095096646235665667 12829047142644969353498501)
                    ·
                      refine ⟨2405446339245931753780969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12829047142644969353498501 2405446339245931753780969)
                      ·
                        rfl

theorem cell23_4684590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_4684590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684590 prefixEnd_4684590 := by exact prefixLift 4684590
  have htrace : WordTrace (prefixWord ++ tailWord_4684590) baseStart_4684590 baseEnd_4684590 := by
    simpa [prefixWord, tailWord_4684590, baseEnd_4684590] using wordTrace_append hprefix tailTrace_4684590
  have hstable : (prefixWord ++ tailWord_4684590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684590).length < 2 ^ (prefixWord ++ tailWord_4684590).sum := by decide
  have hdescent : baseEnd_4684590 < baseStart_4684590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684593 : List Nat := [1, 2, 2, 3, 2, 1, 3, 3, 1, 2, 3]
def baseStart_4684593 : Nat := 118140960795 + 4684593 * 2 ^ 59
def prefixEnd_4684593 : Nat := 4983230072969 + 3 ^ 40 * 4684593 * 2
def baseEnd_4684593 : Nat := 2405447879687895242043455

theorem tailTrace_4684593 : CollatzResearch.WordTrace tailWord_4684593 prefixEnd_4684593 2405447879687895242043455 := by
  unfold tailWord_4684593
  simp only [CollatzResearch.WordTrace]
  refine ⟨170861143517527100633098433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113907429011684733755398955 170861143517527100633098433)
  ·
    refine ⟨128145857638145325474823825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170861143517527100633098433 128145857638145325474823825)
    ·
      refine ⟨96109393228608994106117869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128145857638145325474823825 96109393228608994106117869)
      ·
        refine ⟨36041022460728372789794201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96109393228608994106117869 36041022460728372789794201)
        ·
          refine ⟨27030766845546279592345651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36041022460728372789794201 27030766845546279592345651)
          ·
            refine ⟨40546150268319419388518477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27030766845546279592345651 40546150268319419388518477)
            ·
              refine ⟨15204806350619782270694429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40546150268319419388518477 15204806350619782270694429)
              ·
                refine ⟨5701802381482418351510411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15204806350619782270694429 5701802381482418351510411)
                ·
                  refine ⟨8552703572223627527265617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5701802381482418351510411 8552703572223627527265617)
                  ·
                    refine ⟨6414527679167720645449213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8552703572223627527265617 6414527679167720645449213)
                    ·
                      refine ⟨2405447879687895242043455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6414527679167720645449213 2405447879687895242043455)
                      ·
                        rfl

theorem cell23_4684593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_4684593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684593 prefixEnd_4684593 := by exact prefixLift 4684593
  have htrace : WordTrace (prefixWord ++ tailWord_4684593) baseStart_4684593 baseEnd_4684593 := by
    simpa [prefixWord, tailWord_4684593, baseEnd_4684593] using wordTrace_append hprefix tailTrace_4684593
  have hstable : (prefixWord ++ tailWord_4684593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684593).length < 2 ^ (prefixWord ++ tailWord_4684593).sum := by decide
  have hdescent : baseEnd_4684593 < baseStart_4684593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684607 : List Nat := [1, 1, 2, 2, 5, 1, 2, 4, 1, 2, 2]
def baseStart_4684607 : Nat := 118140960795 + 4684607 * 2 ^ 59
def prefixEnd_4684607 : Nat := 4983230072969 + 3 ^ 40 * 4684607 * 2
def baseEnd_4684607 : Nat := 2405455068417058187268391

theorem tailTrace_4684607 : CollatzResearch.WordTrace tailWord_4684607 prefixEnd_4684607 2405455068417058187268391 := by
  unfold tailWord_4684607
  simp only [CollatzResearch.WordTrace]
  refine ⟨170861654139476381024108075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113907769426317587349405383 170861654139476381024108075)
  ·
    refine ⟨256292481209214571536162113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170861654139476381024108075 256292481209214571536162113)
    ·
      refine ⟨192219360906910928652121585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256292481209214571536162113 192219360906910928652121585)
      ·
        refine ⟨144164520680183196489091189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192219360906910928652121585 144164520680183196489091189)
        ·
          refine ⟨13515423813767174670852299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 144164520680183196489091189 13515423813767174670852299)
          ·
            refine ⟨20273135720650762006278449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13515423813767174670852299 20273135720650762006278449)
            ·
              refine ⟨15204851790488071504708837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20273135720650762006278449 15204851790488071504708837)
              ·
                refine ⟨2850909710716513407132907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15204851790488071504708837 2850909710716513407132907)
                ·
                  refine ⟨4276364566074770110699361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2850909710716513407132907 4276364566074770110699361)
                  ·
                    refine ⟨3207273424556077583024521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4276364566074770110699361 3207273424556077583024521)
                    ·
                      refine ⟨2405455068417058187268391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3207273424556077583024521 2405455068417058187268391)
                      ·
                        rfl

theorem cell23_4684607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4, 1, 2, 2].length) (baseStart_4684607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684607 prefixEnd_4684607 := by exact prefixLift 4684607
  have htrace : WordTrace (prefixWord ++ tailWord_4684607) baseStart_4684607 baseEnd_4684607 := by
    simpa [prefixWord, tailWord_4684607, baseEnd_4684607] using wordTrace_append hprefix tailTrace_4684607
  have hstable : (prefixWord ++ tailWord_4684607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684607).length < 2 ^ (prefixWord ++ tailWord_4684607).sum := by decide
  have hdescent : baseEnd_4684607 < baseStart_4684607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684619 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 5]
def baseStart_4684619 : Nat := 118140960795 + 4684619 * 2 ^ 59
def prefixEnd_4684619 : Nat := 4983230072969 + 3 ^ 40 * 4684619 * 2
def baseEnd_4684619 : Nat := 2405461230184912140318335

theorem tailTrace_4684619 : CollatzResearch.WordTrace tailWord_4684619 prefixEnd_4684619 2405461230184912140318335 := by
  unfold tailWord_4684619
  simp only [CollatzResearch.WordTrace]
  refine ⟨170862091815432907073544911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113908061210288604715696607 170862091815432907073544911)
  ·
    refine ⟨256293137723149360610317367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170862091815432907073544911 256293137723149360610317367)
    ·
      refine ⟨384439706584724040915476051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256293137723149360610317367 384439706584724040915476051)
      ·
        refine ⟨576659559877086061373214077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384439706584724040915476051 576659559877086061373214077)
        ·
          refine ⟨216247334953907273014955279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 576659559877086061373214077 216247334953907273014955279)
          ·
            refine ⟨324371002430860909522432919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216247334953907273014955279 324371002430860909522432919)
            ·
              refine ⟨486556503646291364283649379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324371002430860909522432919 486556503646291364283649379)
              ·
                refine ⟨729834755469437046425474069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 486556503646291364283649379 729834755469437046425474069)
                ·
                  refine ⟨34211004162629861551194097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 729834755469437046425474069 34211004162629861551194097)
                  ·
                    refine ⟨25658253121972396163395573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34211004162629861551194097 25658253121972396163395573)
                    ·
                      refine ⟨2405461230184912140318335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25658253121972396163395573 2405461230184912140318335)
                      ·
                        rfl

theorem cell23_4684619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 5].length) (baseStart_4684619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684619 prefixEnd_4684619 := by exact prefixLift 4684619
  have htrace : WordTrace (prefixWord ++ tailWord_4684619) baseStart_4684619 baseEnd_4684619 := by
    simpa [prefixWord, tailWord_4684619, baseEnd_4684619] using wordTrace_append hprefix tailTrace_4684619
  have hstable : (prefixWord ++ tailWord_4684619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684619).length < 2 ^ (prefixWord ++ tailWord_4684619).sum := by decide
  have hdescent : baseEnd_4684619 < baseStart_4684619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684666 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3]
def baseStart_4684666 : Nat := 118140960795 + 4684666 * 2 ^ 59
def prefixEnd_4684666 : Nat := 4983230072969 + 3 ^ 40 * 4684666 * 2
def baseEnd_4684666 : Nat := 2405485363775673456430619

theorem tailTrace_4684666 : CollatzResearch.WordTrace tailWord_4684666 prefixEnd_4684666 2405485363775673456430619 := by
  unfold tailWord_4684666
  simp only [CollatzResearch.WordTrace]
  refine ⟨42715951511565658525126463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113909204030841756067003901 42715951511565658525126463)
  ·
    refine ⟨64073927267348487787689695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42715951511565658525126463 64073927267348487787689695)
    ·
      refine ⟨96110890901022731681534543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64073927267348487787689695 96110890901022731681534543)
      ·
        refine ⟨144166336351534097522301815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96110890901022731681534543 144166336351534097522301815)
        ·
          refine ⟨216249504527301146283452723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144166336351534097522301815 216249504527301146283452723)
          ·
            refine ⟨324374256790951719425179085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216249504527301146283452723 324374256790951719425179085)
            ·
              refine ⟨121640346296606894784442157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 324374256790951719425179085 121640346296606894784442157)
              ·
                refine ⟨45615129861227585544165809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121640346296606894784442157 45615129861227585544165809)
                ·
                  refine ⟨34211347395920689158124357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45615129861227585544165809 34211347395920689158124357)
                  ·
                    refine ⟨6414627636735129217148317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34211347395920689158124357 6414627636735129217148317)
                    ·
                      refine ⟨2405485363775673456430619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6414627636735129217148317 2405485363775673456430619)
                      ·
                        rfl

theorem cell23_4684666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3].length) (baseStart_4684666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684666 prefixEnd_4684666 := by exact prefixLift 4684666
  have htrace : WordTrace (prefixWord ++ tailWord_4684666) baseStart_4684666 baseEnd_4684666 := by
    simpa [prefixWord, tailWord_4684666, baseEnd_4684666] using wordTrace_append hprefix tailTrace_4684666
  have hstable : (prefixWord ++ tailWord_4684666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684666).length < 2 ^ (prefixWord ++ tailWord_4684666).sum := by decide
  have hdescent : baseEnd_4684666 < baseStart_4684666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684676 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_4684676 : Nat := 118140960795 + 4684676 * 2 ^ 59
def prefixEnd_4684676 : Nat := 4983230072969 + 3 ^ 40 * 4684676 * 2
def baseEnd_4684676 : Nat := 2405490498582218417305573

theorem tailTrace_4684676 : CollatzResearch.WordTrace tailWord_4684676 prefixEnd_4684676 2405490498582218417305573 := by
  unfold tailWord_4684676
  simp only [CollatzResearch.WordTrace]
  refine ⟨85432085388113202904184941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113909447184150937205579921 85432085388113202904184941)
  ·
    refine ⟨32037032020542451089069353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85432085388113202904184941 32037032020542451089069353)
    ·
      refine ⟨24027774015406838316802015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32037032020542451089069353 24027774015406838316802015)
      ·
        refine ⟨36041661023110257475203023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24027774015406838316802015 36041661023110257475203023)
        ·
          refine ⟨54062491534665386212804535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36041661023110257475203023 54062491534665386212804535)
          ·
            refine ⟨81093737301998079319206803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54062491534665386212804535 81093737301998079319206803)
            ·
              refine ⟨121640605952997118978810205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81093737301998079319206803 121640605952997118978810205)
              ·
                refine ⟨45615227232373919617053827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121640605952997118978810205 45615227232373919617053827)
                ·
                  refine ⟨68422840848560879425580741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45615227232373919617053827 68422840848560879425580741)
                  ·
                    refine ⟨12829282659105164892296389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68422840848560879425580741 12829282659105164892296389)
                    ·
                      refine ⟨2405490498582218417305573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12829282659105164892296389 2405490498582218417305573)
                      ·
                        rfl

theorem cell23_4684676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_4684676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684676 prefixEnd_4684676 := by exact prefixLift 4684676
  have htrace : WordTrace (prefixWord ++ tailWord_4684676) baseStart_4684676 baseEnd_4684676 := by
    simpa [prefixWord, tailWord_4684676, baseEnd_4684676] using wordTrace_append hprefix tailTrace_4684676
  have hstable : (prefixWord ++ tailWord_4684676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684676).length < 2 ^ (prefixWord ++ tailWord_4684676).sum := by decide
  have hdescent : baseEnd_4684676 < baseStart_4684676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684750 : List Nat := [4, 1, 1, 1, 2, 5, 1, 1, 2, 5]
def baseStart_4684750 : Nat := 118140960795 + 4684750 * 2 ^ 59
def prefixEnd_4684750 : Nat := 4983230072969 + 3 ^ 40 * 4684750 * 2
def baseEnd_4684750 : Nat := 801842832050217042593411

theorem tailTrace_4684750 : CollatzResearch.WordTrace tailWord_4684750 prefixEnd_4684750 801842832050217042593411 := by
  unfold tailWord_4684750
  simp only [CollatzResearch.WordTrace]
  refine ⟨21358358722244789555820463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113911246518638877631042469 21358358722244789555820463)
  ·
    refine ⟨32037538083367184333730695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21358358722244789555820463 32037538083367184333730695)
    ·
      refine ⟨48056307125050776500596043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32037538083367184333730695 48056307125050776500596043)
      ·
        refine ⟨72084460687576164750894065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48056307125050776500596043 72084460687576164750894065)
        ·
          refine ⟨54063345515682123563170549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72084460687576164750894065 54063345515682123563170549)
          ·
            refine ⟨5068438642095199084047239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54063345515682123563170549 5068438642095199084047239)
            ·
              refine ⟨7602657963142798626070859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5068438642095199084047239 7602657963142798626070859)
              ·
                refine ⟨11403986944714197939106289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7602657963142798626070859 11403986944714197939106289)
                ·
                  refine ⟨8552990208535648454329717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11403986944714197939106289 8552990208535648454329717)
                  ·
                    refine ⟨801842832050217042593411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8552990208535648454329717 801842832050217042593411)
                    ·
                      rfl

theorem cell23_4684750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_4684750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684750 prefixEnd_4684750 := by exact prefixLift 4684750
  have htrace : WordTrace (prefixWord ++ tailWord_4684750) baseStart_4684750 baseEnd_4684750 := by
    simpa [prefixWord, tailWord_4684750, baseEnd_4684750] using wordTrace_append hprefix tailTrace_4684750
  have hstable : (prefixWord ++ tailWord_4684750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684750).length < 2 ^ (prefixWord ++ tailWord_4684750).sum := by decide
  have hdescent : baseEnd_4684750 < baseStart_4684750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684753 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 1, 6, 2]
def baseStart_4684753 : Nat := 118140960795 + 4684753 * 2 ^ 59
def prefixEnd_4684753 : Nat := 4983230072969 + 3 ^ 40 * 4684753 * 2
def baseEnd_4684753 : Nat := 2405530036592614616042719

theorem tailTrace_4684753 : CollatzResearch.WordTrace tailWord_4684753 prefixEnd_4684753 2405530036592614616042719 := by
  unfold tailWord_4684753
  simp only [CollatzResearch.WordTrace]
  refine ⟨170866979196947447958922913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113911319464631631972615275 170866979196947447958922913)
  ·
    refine ⟨128150234397710585969192185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170866979196947447958922913 128150234397710585969192185)
    ·
      refine ⟨96112675798282939476894139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128150234397710585969192185 96112675798282939476894139)
      ·
        refine ⟨144169013697424409215341209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96112675798282939476894139 144169013697424409215341209)
        ·
          refine ⟨108126760273068306911505907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144169013697424409215341209 108126760273068306911505907)
          ·
            refine ⟨162190140409602460367258861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108126760273068306911505907 162190140409602460367258861)
            ·
              refine ⟨60821302653600922637722073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162190140409602460367258861 60821302653600922637722073)
              ·
                refine ⟨45615976990200691978291555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60821302653600922637722073 45615976990200691978291555)
                ·
                  refine ⟨68423965485301037967437333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45615976990200691978291555 68423965485301037967437333)
                  ·
                    refine ⟨3207373382123486154723625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68423965485301037967437333 3207373382123486154723625)
                    ·
                      refine ⟨2405530036592614616042719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3207373382123486154723625 2405530036592614616042719)
                      ·
                        rfl

theorem cell23_4684753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 6, 2].length) (baseStart_4684753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684753 prefixEnd_4684753 := by exact prefixLift 4684753
  have htrace : WordTrace (prefixWord ++ tailWord_4684753) baseStart_4684753 baseEnd_4684753 := by
    simpa [prefixWord, tailWord_4684753, baseEnd_4684753] using wordTrace_append hprefix tailTrace_4684753
  have hstable : (prefixWord ++ tailWord_4684753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684753).length < 2 ^ (prefixWord ++ tailWord_4684753).sum := by decide
  have hdescent : baseEnd_4684753 < baseStart_4684753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684790 : List Nat := [5, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3]
def baseStart_4684790 : Nat := 118140960795 + 4684790 * 2 ^ 59
def prefixEnd_4684790 : Nat := 4983230072969 + 3 ^ 40 * 4684790 * 2
def baseEnd_4684790 : Nat := 2405549035376830971280049

theorem tailTrace_4684790 : CollatzResearch.WordTrace tailWord_4684790 prefixEnd_4684790 2405549035376830971280049 := by
  unfold tailWord_4684790
  simp only [CollatzResearch.WordTrace]
  refine ⟨10679270543613337704876239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113912219131875602185346549 10679270543613337704876239)
  ·
    refine ⟨16018905815420006557314359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10679270543613337704876239 16018905815420006557314359)
    ·
      refine ⟨24028358723130009835971539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16018905815420006557314359 24028358723130009835971539)
      ·
        refine ⟨36042538084695014753957309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24028358723130009835971539 36042538084695014753957309)
        ·
          refine ⟨13515951781760630532733991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36042538084695014753957309 13515951781760630532733991)
          ·
            refine ⟨20273927672640945799100987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13515951781760630532733991 20273927672640945799100987)
            ·
              refine ⟨30410891508961418698651481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20273927672640945799100987 30410891508961418698651481)
              ·
                refine ⟨22808168631721064023988611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30410891508961418698651481 22808168631721064023988611)
                ·
                  refine ⟨34212252947581596035982917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22808168631721064023988611 34212252947581596035982917)
                  ·
                    refine ⟨6414797427671549256746797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34212252947581596035982917 6414797427671549256746797)
                    ·
                      refine ⟨2405549035376830971280049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6414797427671549256746797 2405549035376830971280049)
                      ·
                        rfl

theorem cell23_4684790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_4684790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684790 prefixEnd_4684790 := by exact prefixLift 4684790
  have htrace : WordTrace (prefixWord ++ tailWord_4684790) baseStart_4684790 baseEnd_4684790 := by
    simpa [prefixWord, tailWord_4684790, baseEnd_4684790] using wordTrace_append hprefix tailTrace_4684790
  have hstable : (prefixWord ++ tailWord_4684790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684790).length < 2 ^ (prefixWord ++ tailWord_4684790).sum := by decide
  have hdescent : baseEnd_4684790 < baseStart_4684790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684814 : List Nat := [4, 1, 1, 2, 2, 4, 1, 3, 1, 4]
def baseStart_4684814 : Nat := 118140960795 + 4684814 * 2 ^ 59
def prefixEnd_4684814 : Nat := 4983230072969 + 3 ^ 40 * 4684814 * 2
def baseEnd_4684814 : Nat := 801853786304179625793313

theorem tailTrace_4684814 : CollatzResearch.WordTrace tailWord_4684814 prefixEnd_4684814 801853786304179625793313 := by
  unfold tailWord_4684814
  simp only [CollatzResearch.WordTrace]
  refine ⟨21358650506215806922111687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113912802699817636917928997 21358650506215806922111687)
  ·
    refine ⟨32037975759323710383167531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21358650506215806922111687 32037975759323710383167531)
    ·
      refine ⟨48056963638985565574751297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32037975759323710383167531 48056963638985565574751297)
      ·
        refine ⟨36042722729239174181063473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48056963638985565574751297 36042722729239174181063473)
        ·
          refine ⟨27032042046929380635797605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36042722729239174181063473 27032042046929380635797605)
          ·
            refine ⟨5068507883799258869212051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27032042046929380635797605 5068507883799258869212051)
            ·
              refine ⟨7602761825698888303818077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5068507883799258869212051 7602761825698888303818077)
              ·
                refine ⟨2851035684637083113931779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7602761825698888303818077 2851035684637083113931779)
                ·
                  refine ⟨4276553526955624670897669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2851035684637083113931779 4276553526955624670897669)
                  ·
                    refine ⟨801853786304179625793313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4276553526955624670897669 801853786304179625793313)
                    ·
                      rfl

theorem cell23_4684814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_4684814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684814 prefixEnd_4684814 := by exact prefixLift 4684814
  have htrace : WordTrace (prefixWord ++ tailWord_4684814) baseStart_4684814 baseEnd_4684814 := by
    simpa [prefixWord, tailWord_4684814, baseEnd_4684814] using wordTrace_append hprefix tailTrace_4684814
  have hstable : (prefixWord ++ tailWord_4684814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684814).length < 2 ^ (prefixWord ++ tailWord_4684814).sum := by decide
  have hdescent : baseEnd_4684814 < baseStart_4684814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684816 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 5]
def baseStart_4684816 : Nat := 118140960795 + 4684816 * 2 ^ 59
def prefixEnd_4684816 : Nat := 4983230072969 + 3 ^ 40 * 4684816 * 2
def baseEnd_4684816 : Nat := 2405562385873847869554929

theorem tailTrace_4684816 : CollatzResearch.WordTrace tailWord_4684816 prefixEnd_4684816 2405562385873847869554929 := by
  unfold tailWord_4684816
  simp only [CollatzResearch.WordTrace]
  refine ⟨85434638497859604859233151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113912851330479473145644201 85434638497859604859233151)
  ·
    refine ⟨128151957746789407288849727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85434638497859604859233151 128151957746789407288849727)
    ·
      refine ⟨192227936620184110933274591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128151957746789407288849727 192227936620184110933274591)
      ·
        refine ⟨288341904930276166399911887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192227936620184110933274591 288341904930276166399911887)
        ·
          refine ⟨432512857395414249599867831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288341904930276166399911887 432512857395414249599867831)
          ·
            refine ⟨648769286093121374399801747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432512857395414249599867831 648769286093121374399801747)
            ·
              refine ⟨973153929139682061599702621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 648769286093121374399801747 973153929139682061599702621)
              ·
                refine ⟨364932723427380773099888483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 973153929139682061599702621 364932723427380773099888483)
                ·
                  refine ⟨547399085141071159649832725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 364932723427380773099888483 547399085141071159649832725)
                  ·
                    refine ⟨25659332115987710608585909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 547399085141071159649832725 25659332115987710608585909)
                    ·
                      refine ⟨2405562385873847869554929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25659332115987710608585909 2405562385873847869554929)
                      ·
                        rfl

theorem cell23_4684816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 5].length) (baseStart_4684816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684816 prefixEnd_4684816 := by exact prefixLift 4684816
  have htrace : WordTrace (prefixWord ++ tailWord_4684816) baseStart_4684816 baseEnd_4684816 := by
    simpa [prefixWord, tailWord_4684816, baseEnd_4684816] using wordTrace_append hprefix tailTrace_4684816
  have hstable : (prefixWord ++ tailWord_4684816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684816).length < 2 ^ (prefixWord ++ tailWord_4684816).sum := by decide
  have hdescent : baseEnd_4684816 < baseStart_4684816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684843 : List Nat := [1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 4]
def baseStart_4684843 : Nat := 118140960795 + 4684843 * 2 ^ 59
def prefixEnd_4684843 : Nat := 4983230072969 + 3 ^ 40 * 4684843 * 2
def baseEnd_4684843 : Nat := 2405576249851519263917305

theorem tailTrace_4684843 : CollatzResearch.WordTrace tailWord_4684843 prefixEnd_4684843 2405576249851519263917305 := by
  unfold tailWord_4684843
  simp only [CollatzResearch.WordTrace]
  refine ⟨170870261766621393329699183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113913507844414262219799455 170870261766621393329699183)
  ·
    refine ⟨256305392649932089994548775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170870261766621393329699183 256305392649932089994548775)
    ·
      refine ⟨384458088974898134991823163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256305392649932089994548775 384458088974898134991823163)
      ·
        refine ⟨576687133462347202487734745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384458088974898134991823163 576687133462347202487734745)
        ·
          refine ⟨432515350096760401865801059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 576687133462347202487734745 432515350096760401865801059)
          ·
            refine ⟨648773025145140602798701589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432515350096760401865801059 648773025145140602798701589)
            ·
              refine ⟨30411235553678465756189137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 648773025145140602798701589 30411235553678465756189137)
              ·
                refine ⟨22808426665258849317141853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30411235553678465756189137 22808426665258849317141853)
                ·
                  refine ⟨8553159999472068493928195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22808426665258849317141853 8553159999472068493928195)
                  ·
                    refine ⟨12829739999208102740892293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8553159999472068493928195 12829739999208102740892293)
                    ·
                      refine ⟨2405576249851519263917305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12829739999208102740892293 2405576249851519263917305)
                      ·
                        rfl

theorem cell23_4684843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 4].length) (baseStart_4684843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684843 prefixEnd_4684843 := by exact prefixLift 4684843
  have htrace : WordTrace (prefixWord ++ tailWord_4684843) baseStart_4684843 baseEnd_4684843 := by
    simpa [prefixWord, tailWord_4684843, baseEnd_4684843] using wordTrace_append hprefix tailTrace_4684843
  have hstable : (prefixWord ++ tailWord_4684843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684843).length < 2 ^ (prefixWord ++ tailWord_4684843).sum := by decide
  have hdescent : baseEnd_4684843 < baseStart_4684843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684853 : List Nat := [1, 3, 3, 1, 1, 1, 1, 5, 1, 6]
def baseStart_4684853 : Nat := 118140960795 + 4684853 * 2 ^ 59
def prefixEnd_4684853 : Nat := 4983230072969 + 3 ^ 40 * 4684853 * 2
def baseEnd_4684853 : Nat := 801860461552688074930753

theorem tailTrace_4684853 : CollatzResearch.WordTrace tailWord_4684853 prefixEnd_4684853 801860461552688074930753 := by
  unfold tailWord_4684853
  simp only [CollatzResearch.WordTrace]
  refine ⟨170870626496585165037563213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113913750997723443358375475 170870626496585165037563213)
  ·
    refine ⟨64076484936219436889086205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170870626496585165037563213 64076484936219436889086205)
    ·
      refine ⟨24028681851082288833407327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64076484936219436889086205 24028681851082288833407327)
      ·
        refine ⟨36043022776623433250110991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24028681851082288833407327 36043022776623433250110991)
        ·
          refine ⟨54064534164935149875166487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36043022776623433250110991 54064534164935149875166487)
          ·
            refine ⟨81096801247402724812749731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54064534164935149875166487 81096801247402724812749731)
            ·
              refine ⟨121645201871104087219124597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81096801247402724812749731 121645201871104087219124597)
              ·
                refine ⟨11404237675416008176792931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121645201871104087219124597 11404237675416008176792931)
                ·
                  refine ⟨17106356513124012265189397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11404237675416008176792931 17106356513124012265189397)
                  ·
                    refine ⟨801860461552688074930753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17106356513124012265189397 801860461552688074930753)
                    ·
                      rfl

theorem cell23_4684853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_4684853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684853 prefixEnd_4684853 := by exact prefixLift 4684853
  have htrace : WordTrace (prefixWord ++ tailWord_4684853) baseStart_4684853 baseEnd_4684853 := by
    simpa [prefixWord, tailWord_4684853, baseEnd_4684853] using wordTrace_append hprefix tailTrace_4684853
  have hstable : (prefixWord ++ tailWord_4684853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684853).length < 2 ^ (prefixWord ++ tailWord_4684853).sum := by decide
  have hdescent : baseEnd_4684853 < baseStart_4684853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684857 : List Nat := [1, 2, 1, 5, 2, 3, 1, 2, 1, 5]
def baseStart_4684857 : Nat := 118140960795 + 4684857 * 2 ^ 59
def prefixEnd_4684857 : Nat := 4983230072969 + 3 ^ 40 * 4684857 * 2
def baseEnd_4684857 : Nat := 801861146193560736380747

theorem tailTrace_4684857 : CollatzResearch.WordTrace tailWord_4684857 prefixEnd_4684857 801861146193560736380747 := by
  unfold tailWord_4684857
  simp only [CollatzResearch.WordTrace]
  refine ⟨170870772388570673720708825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113913848259047115813805883 170870772388570673720708825)
  ·
    refine ⟨128153079291428005290531619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170870772388570673720708825 128153079291428005290531619)
    ·
      refine ⟨192229618937142007935797429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128153079291428005290531619 192229618937142007935797429)
      ·
        refine ⟨18021526775357063243981009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 192229618937142007935797429 18021526775357063243981009)
        ·
          refine ⟨13516145081517797432985757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18021526775357063243981009 13516145081517797432985757)
          ·
            refine ⟨5068554405569174037369659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13516145081517797432985757 5068554405569174037369659)
            ·
              refine ⟨7602831608353761056054489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5068554405569174037369659 7602831608353761056054489)
              ·
                refine ⟨5702123706265320792040867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7602831608353761056054489 5702123706265320792040867)
                ·
                  refine ⟨8553185559397981188061301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5702123706265320792040867 8553185559397981188061301)
                  ·
                    refine ⟨801861146193560736380747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8553185559397981188061301 801861146193560736380747)
                    ·
                      rfl

theorem cell23_4684857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 5].length) (baseStart_4684857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684857 prefixEnd_4684857 := by exact prefixLift 4684857
  have htrace : WordTrace (prefixWord ++ tailWord_4684857) baseStart_4684857 baseEnd_4684857 := by
    simpa [prefixWord, tailWord_4684857, baseEnd_4684857] using wordTrace_append hprefix tailTrace_4684857
  have hstable : (prefixWord ++ tailWord_4684857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684857).length < 2 ^ (prefixWord ++ tailWord_4684857).sum := by decide
  have hdescent : baseEnd_4684857 < baseStart_4684857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684860 : List Nat := [2, 2, 2, 2, 2, 3, 1, 1, 3, 1, 4]
def baseStart_4684860 : Nat := 118140960795 + 4684860 * 2 ^ 59
def prefixEnd_4684860 : Nat := 4983230072969 + 3 ^ 40 * 4684860 * 2
def baseEnd_4684860 : Nat := 2405584979022645697404727

theorem tailTrace_4684860 : CollatzResearch.WordTrace tailWord_4684860 prefixEnd_4684860 2405584979022645697404727 := by
  unfold tailWord_4684860
  simp only [CollatzResearch.WordTrace]
  refine ⟨85435440903779902616534017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113913921205039870155378689 85435440903779902616534017)
  ·
    refine ⟨64076580677834926962400513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85435440903779902616534017 64076580677834926962400513)
    ·
      refine ⟨48057435508376195221800385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64076580677834926962400513 48057435508376195221800385)
      ·
        refine ⟨36043076631282146416350289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48057435508376195221800385 36043076631282146416350289)
        ·
          refine ⟨27032307473461609812262717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36043076631282146416350289 27032307473461609812262717)
          ·
            refine ⟨10137115302548103679598519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27032307473461609812262717 10137115302548103679598519)
            ·
              refine ⟨15205672953822155519397779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10137115302548103679598519 15205672953822155519397779)
              ·
                refine ⟨22808509430733233279096669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15205672953822155519397779 22808509430733233279096669)
                ·
                  refine ⟨8553191036524962479661251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22808509430733233279096669 8553191036524962479661251)
                  ·
                    refine ⟨12829786554787443719491877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8553191036524962479661251 12829786554787443719491877)
                    ·
                      refine ⟨2405584979022645697404727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12829786554787443719491877 2405584979022645697404727)
                      ·
                        rfl

theorem cell23_4684860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_4684860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684860 prefixEnd_4684860 := by exact prefixLift 4684860
  have htrace : WordTrace (prefixWord ++ tailWord_4684860) baseStart_4684860 baseEnd_4684860 := by
    simpa [prefixWord, tailWord_4684860, baseEnd_4684860] using wordTrace_append hprefix tailTrace_4684860
  have hstable : (prefixWord ++ tailWord_4684860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684860).length < 2 ^ (prefixWord ++ tailWord_4684860).sum := by decide
  have hdescent : baseEnd_4684860 < baseStart_4684860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684880 : List Nat := [2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 3]
def baseStart_4684880 : Nat := 118140960795 + 4684880 * 2 ^ 59
def prefixEnd_4684880 : Nat := 4983230072969 + 3 ^ 40 * 4684880 * 2
def baseEnd_4684880 : Nat := 2405595248635735619154635

theorem tailTrace_4684880 : CollatzResearch.WordTrace tailWord_4684880 prefixEnd_4684880 2405595248635735619154635 := by
  unfold tailWord_4684880
  simp only [CollatzResearch.WordTrace]
  refine ⟨85435805633743674324398047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113914407511658232432530729 85435805633743674324398047)
  ·
    refine ⟨128153708450615511486597071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85435805633743674324398047 128153708450615511486597071)
    ·
      refine ⟨192230562675923267229895607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128153708450615511486597071 192230562675923267229895607)
      ·
        refine ⟨288345844013884900844843411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192230562675923267229895607 288345844013884900844843411)
        ·
          refine ⟨432518766020827351267265117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288345844013884900844843411 432518766020827351267265117)
          ·
            refine ⟨162194537257810256725224419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 432518766020827351267265117 162194537257810256725224419)
            ·
              refine ⟨243291805886715385087836629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162194537257810256725224419 243291805886715385087836629)
              ·
                refine ⟨5702151700469891837996171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 243291805886715385087836629 5702151700469891837996171)
                ·
                  refine ⟨8553227550704837756994257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5702151700469891837996171 8553227550704837756994257)
                  ·
                    refine ⟨6414920663028628317745693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8553227550704837756994257 6414920663028628317745693)
                    ·
                      refine ⟨2405595248635735619154635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6414920663028628317745693 2405595248635735619154635)
                      ·
                        rfl

theorem cell23_4684880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 3].length) (baseStart_4684880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684880 prefixEnd_4684880 := by exact prefixLift 4684880
  have htrace : WordTrace (prefixWord ++ tailWord_4684880) baseStart_4684880 baseEnd_4684880 := by
    simpa [prefixWord, tailWord_4684880, baseEnd_4684880] using wordTrace_append hprefix tailTrace_4684880
  have hstable : (prefixWord ++ tailWord_4684880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684880).length < 2 ^ (prefixWord ++ tailWord_4684880).sum := by decide
  have hdescent : baseEnd_4684880 < baseStart_4684880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684894 : List Nat := [4, 4, 1, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_4684894 : Nat := 118140960795 + 4684894 * 2 ^ 59
def prefixEnd_4684894 : Nat := 4983230072969 + 3 ^ 40 * 4684894 * 2
def baseEnd_4684894 : Nat := 2405602437364898564379571

theorem tailTrace_4684894 : CollatzResearch.WordTrace tailWord_4684894 prefixEnd_4684894 2405602437364898564379571 := by
  unfold tailWord_4684894
  simp only [CollatzResearch.WordTrace]
  refine ⟨21359015236179578629975717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113914747926291086026537157 21359015236179578629975717)
  ·
    refine ⟨4004815356783670993120447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21359015236179578629975717 4004815356783670993120447)
    ·
      refine ⟨6007223035175506489680671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4004815356783670993120447 6007223035175506489680671)
      ·
        refine ⟨9010834552763259734521007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6007223035175506489680671 9010834552763259734521007)
        ·
          refine ⟨13516251829144889601781511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9010834552763259734521007 13516251829144889601781511)
          ·
            refine ⟨20274377743717334402672267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13516251829144889601781511 20274377743717334402672267)
            ·
              refine ⟨30411566615576001604008401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20274377743717334402672267 30411566615576001604008401)
              ·
                refine ⟨22808674961682001203006301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30411566615576001604008401 22808674961682001203006301)
                ·
                  refine ⟨8553253110630750451127363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22808674961682001203006301 8553253110630750451127363)
                  ·
                    refine ⟨12829879665946125676691045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8553253110630750451127363 12829879665946125676691045)
                    ·
                      refine ⟨2405602437364898564379571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12829879665946125676691045 2405602437364898564379571)
                      ·
                        rfl

theorem cell23_4684894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_4684894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684894 prefixEnd_4684894 := by exact prefixLift 4684894
  have htrace : WordTrace (prefixWord ++ tailWord_4684894) baseStart_4684894 baseEnd_4684894 := by
    simpa [prefixWord, tailWord_4684894, baseEnd_4684894] using wordTrace_append hprefix tailTrace_4684894
  have hstable : (prefixWord ++ tailWord_4684894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684894).length < 2 ^ (prefixWord ++ tailWord_4684894).sum := by decide
  have hdescent : baseEnd_4684894 < baseStart_4684894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684953 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 6, 1, 5]
def baseStart_4684953 : Nat := 118140960795 + 4684953 * 2 ^ 59
def prefixEnd_4684953 : Nat := 4983230072969 + 3 ^ 40 * 4684953 * 2
def baseEnd_4684953 : Nat := 2405632732723513833541799

theorem tailTrace_4684953 : CollatzResearch.WordTrace tailWord_4684953 prefixEnd_4684953 2405632732723513833541799 := by
  unfold tailWord_4684953
  simp only [CollatzResearch.WordTrace]
  refine ⟨170874273796222882116203513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113916182530815254744135675 170874273796222882116203513)
  ·
    refine ⟨128155705347167161587152635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170874273796222882116203513 128155705347167161587152635)
    ·
      refine ⟨192233558020750742380728953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128155705347167161587152635 192233558020750742380728953)
      ·
        refine ⟨144175168515563056785546715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192233558020750742380728953 144175168515563056785546715)
        ·
          refine ⟨216262752773344585178320073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144175168515563056785546715 216262752773344585178320073)
          ·
            refine ⟨162197064580008438883740055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216262752773344585178320073 162197064580008438883740055)
            ·
              refine ⟨243295596870012658325610083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162197064580008438883740055 243295596870012658325610083)
              ·
                refine ⟨364943395305018987488415125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243295596870012658325610083 364943395305018987488415125)
                ·
                  refine ⟨17106721654922765038519459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 364943395305018987488415125 17106721654922765038519459)
                  ·
                    refine ⟨25660082482384147557779189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17106721654922765038519459 25660082482384147557779189)
                    ·
                      refine ⟨2405632732723513833541799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25660082482384147557779189 2405632732723513833541799)
                      ·
                        rfl

theorem cell23_4684953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_4684953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684953 prefixEnd_4684953 := by exact prefixLift 4684953
  have htrace : WordTrace (prefixWord ++ tailWord_4684953) baseStart_4684953 baseEnd_4684953 := by
    simpa [prefixWord, tailWord_4684953, baseEnd_4684953] using wordTrace_append hprefix tailTrace_4684953
  have hstable : (prefixWord ++ tailWord_4684953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684953).length < 2 ^ (prefixWord ++ tailWord_4684953).sum := by decide
  have hdescent : baseEnd_4684953 < baseStart_4684953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685000 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 4, 3, 3]
def baseStart_4685000 : Nat := 118140960795 + 4685000 * 2 ^ 59
def prefixEnd_4685000 : Nat := 4983230072969 + 3 ^ 40 * 4685000 * 2
def baseEnd_4685000 : Nat := 2405656866314275149654083

theorem tailTrace_4685000 : CollatzResearch.WordTrace tailWord_4685000 prefixEnd_4685000 2405656866314275149654083 := by
  unfold tailWord_4685000
  simp only [CollatzResearch.WordTrace]
  refine ⟨85437994013526304571582227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113917325351368406095442969 85437994013526304571582227)
  ·
    refine ⟨128156991020289456857373341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85437994013526304571582227 128156991020289456857373341)
    ·
      refine ⟨48058871632608546321515003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128156991020289456857373341 48058871632608546321515003)
      ·
        refine ⟨72088307448912819482272505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48058871632608546321515003 72088307448912819482272505)
        ·
          refine ⟨54066230586684614611704379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72088307448912819482272505 54066230586684614611704379)
          ·
            refine ⟨81099345880026921917556569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54066230586684614611704379 81099345880026921917556569)
            ·
              refine ⟨60824509410020191438167427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81099345880026921917556569 60824509410020191438167427)
              ·
                refine ⟨91236764115030287157251141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60824509410020191438167427 91236764115030287157251141)
                ·
                  refine ⟨17106893271568178841984589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91236764115030287157251141 17106893271568178841984589)
                  ·
                    refine ⟨6415084976838067065744221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17106893271568178841984589 6415084976838067065744221)
                    ·
                      refine ⟨2405656866314275149654083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6415084976838067065744221 2405656866314275149654083)
                      ·
                        rfl

theorem cell23_4685000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_4685000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685000 prefixEnd_4685000 := by exact prefixLift 4685000
  have htrace : WordTrace (prefixWord ++ tailWord_4685000) baseStart_4685000 baseEnd_4685000 := by
    simpa [prefixWord, tailWord_4685000, baseEnd_4685000] using wordTrace_append hprefix tailTrace_4685000
  have hstable : (prefixWord ++ tailWord_4685000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685000).length < 2 ^ (prefixWord ++ tailWord_4685000).sum := by decide
  have hdescent : baseEnd_4685000 < baseStart_4685000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685003 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 3, 7]
def baseStart_4685003 : Nat := 118140960795 + 4685003 * 2 ^ 59
def prefixEnd_4685003 : Nat := 4983230072969 + 3 ^ 40 * 4685003 * 2
def baseEnd_4685003 : Nat := 801886135585412879305523

theorem tailTrace_4685003 : CollatzResearch.WordTrace tailWord_4685003 prefixEnd_4685003 801886135585412879305523 := by
  unfold tailWord_4685003
  simp only [CollatzResearch.WordTrace]
  refine ⟨170876097446041740655523663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113917398297361160437015775 170876097446041740655523663)
  ·
    refine ⟨256314146169062610983285495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170876097446041740655523663 256314146169062610983285495)
    ·
      refine ⟨384471219253593916474928243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256314146169062610983285495 384471219253593916474928243)
      ·
        refine ⟨576706828880390874712392365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384471219253593916474928243 576706828880390874712392365)
        ·
          refine ⟨216265060830146578017147137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 576706828880390874712392365 216265060830146578017147137)
          ·
            refine ⟨162198795622609933512860353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216265060830146578017147137 162198795622609933512860353)
            ·
              refine ⟨121649096716957450134645265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162198795622609933512860353 121649096716957450134645265)
              ·
                refine ⟨91236822537718087600983949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121649096716957450134645265 91236822537718087600983949)
                ·
                  refine ⟨34213808451644282850368981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91236822537718087600983949 34213808451644282850368981)
                  ·
                    refine ⟨801886135585412879305523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34213808451644282850368981 801886135585412879305523)
                    ·
                      rfl

theorem cell23_4685003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 7].length) (baseStart_4685003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685003 prefixEnd_4685003 := by exact prefixLift 4685003
  have htrace : WordTrace (prefixWord ++ tailWord_4685003) baseStart_4685003 baseEnd_4685003 := by
    simpa [prefixWord, tailWord_4685003, baseEnd_4685003] using wordTrace_append hprefix tailTrace_4685003
  have hstable : (prefixWord ++ tailWord_4685003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685003).length < 2 ^ (prefixWord ++ tailWord_4685003).sum := by decide
  have hdescent : baseEnd_4685003 < baseStart_4685003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685037 : List Nat := [1, 5, 1, 2, 2, 1, 1, 3, 2, 5]
def baseStart_4685037 : Nat := 118140960795 + 4685037 * 2 ^ 59
def prefixEnd_4685037 : Nat := 4983230072969 + 3 ^ 40 * 4685037 * 2
def baseEnd_4685037 : Nat := 801891955032830501630471

theorem tailTrace_4685037 : CollatzResearch.WordTrace tailWord_4685037 prefixEnd_4685037 801891955032830501630471 := by
  unfold tailWord_4685037
  simp only [CollatzResearch.WordTrace]
  refine ⟨170877337527918564462261365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113918225018612376308174243 170877337527918564462261365)
  ·
    refine ⟨16019750393242365418337003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 170877337527918564462261365 16019750393242365418337003)
    ·
      refine ⟨24029625589863548127505505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16019750393242365418337003 24029625589863548127505505)
      ·
        refine ⟨18022219192397661095629129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24029625589863548127505505 18022219192397661095629129)
        ·
          refine ⟨13516664394298245821721847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18022219192397661095629129 13516664394298245821721847)
          ·
            refine ⟨20274996591447368732582771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13516664394298245821721847 20274996591447368732582771)
            ·
              refine ⟨30412494887171053098874157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20274996591447368732582771 30412494887171053098874157)
              ·
                refine ⟨11404685582689144912077809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30412494887171053098874157 11404685582689144912077809)
                ·
                  refine ⟨8553514187016858684058357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11404685582689144912077809 8553514187016858684058357)
                  ·
                    refine ⟨801891955032830501630471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8553514187016858684058357 801891955032830501630471)
                    ·
                      rfl

theorem cell23_4685037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_4685037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685037 prefixEnd_4685037 := by exact prefixLift 4685037
  have htrace : WordTrace (prefixWord ++ tailWord_4685037) baseStart_4685037 baseEnd_4685037 := by
    simpa [prefixWord, tailWord_4685037, baseEnd_4685037] using wordTrace_append hprefix tailTrace_4685037
  have hstable : (prefixWord ++ tailWord_4685037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685037).length < 2 ^ (prefixWord ++ tailWord_4685037).sum := by decide
  have hdescent : baseEnd_4685037 < baseStart_4685037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685057 : List Nat := [1, 2, 4, 1, 1, 3, 2, 2, 2, 1, 4]
def baseStart_4685057 : Nat := 118140960795 + 4685057 * 2 ^ 59
def prefixEnd_4685057 : Nat := 4983230072969 + 3 ^ 40 * 4685057 * 2
def baseEnd_4685057 : Nat := 2405686134711581426641321

theorem tailTrace_4685057 : CollatzResearch.WordTrace tailWord_4685057 prefixEnd_4685057 2405686134711581426641321 := by
  unfold tailWord_4685057
  simp only [CollatzResearch.WordTrace]
  refine ⟨170878066987846107877989425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113918711325230738585326283 170878066987846107877989425)
  ·
    refine ⟨128158550240884580908492069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170878066987846107877989425 128158550240884580908492069)
    ·
      refine ⟨24029728170165858920342263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128158550240884580908492069 24029728170165858920342263)
      ·
        refine ⟨36044592255248788380513395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24029728170165858920342263 36044592255248788380513395)
        ·
          refine ⟨54066888382873182570770093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36044592255248788380513395 54066888382873182570770093)
          ·
            refine ⟨20275083143577443464038785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54066888382873182570770093 20275083143577443464038785)
            ·
              refine ⟨15206312357683082598029089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20275083143577443464038785 15206312357683082598029089)
              ·
                refine ⟨11404734268262311948521817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15206312357683082598029089 11404734268262311948521817)
                ·
                  refine ⟨8553550701196733961391363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11404734268262311948521817 8553550701196733961391363)
                  ·
                    refine ⟨12830326051795100942087045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8553550701196733961391363 12830326051795100942087045)
                    ·
                      refine ⟨2405686134711581426641321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12830326051795100942087045 2405686134711581426641321)
                      ·
                        rfl

theorem cell23_4685057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_4685057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685057 prefixEnd_4685057 := by exact prefixLift 4685057
  have htrace : WordTrace (prefixWord ++ tailWord_4685057) baseStart_4685057 baseEnd_4685057 := by
    simpa [prefixWord, tailWord_4685057, baseEnd_4685057] using wordTrace_append hprefix tailTrace_4685057
  have hstable : (prefixWord ++ tailWord_4685057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685057).length < 2 ^ (prefixWord ++ tailWord_4685057).sum := by decide
  have hdescent : baseEnd_4685057 < baseStart_4685057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685058 : List Nat := [3, 4, 1, 1, 3, 2, 2, 2, 5]
def baseStart_4685058 : Nat := 118140960795 + 4685058 * 2 ^ 59
def prefixEnd_4685058 : Nat := 4983230072969 + 3 ^ 40 * 4685058 * 2
def baseEnd_4685058 : Nat := 267298516465803991414313

theorem tailTrace_4685058 : CollatzResearch.WordTrace tailWord_4685058 prefixEnd_4685058 267298516465803991414313 := by
  unfold tailWord_4685058
  simp only [CollatzResearch.WordTrace]
  refine ⟨42719525865210621262193957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113918735640561656699183885 42719525865210621262193957)
  ·
    refine ⟨8009911099726991486661367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42719525865210621262193957 8009911099726991486661367)
    ·
      refine ⟨12014866649590487229992051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8009911099726991486661367 12014866649590487229992051)
      ·
        refine ⟨18022299974385730844988077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12014866649590487229992051 18022299974385730844988077)
        ·
          refine ⟨6758362490394649066870529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18022299974385730844988077 6758362490394649066870529)
          ·
            refine ⟨5068771867795986800152897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6758362490394649066870529 5068771867795986800152897)
            ·
              refine ⟨3801578900846990100114673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5068771867795986800152897 3801578900846990100114673)
              ·
                refine ⟨2851184175635242575086005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3801578900846990100114673 2851184175635242575086005)
                ·
                  refine ⟨267298516465803991414313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2851184175635242575086005 267298516465803991414313)
                  ·
                    rfl

theorem cell23_4685058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_4685058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685058 prefixEnd_4685058 := by exact prefixLift 4685058
  have htrace : WordTrace (prefixWord ++ tailWord_4685058) baseStart_4685058 baseEnd_4685058 := by
    simpa [prefixWord, tailWord_4685058, baseEnd_4685058] using wordTrace_append hprefix tailTrace_4685058
  have hstable : (prefixWord ++ tailWord_4685058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685058).length < 2 ^ (prefixWord ++ tailWord_4685058).sum := by decide
  have hdescent : baseEnd_4685058 < baseStart_4685058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685157 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 6, 4]
def baseStart_4685157 : Nat := 118140960795 + 4685157 * 2 ^ 59
def prefixEnd_4685157 : Nat := 4983230072969 + 3 ^ 40 * 4685157 * 2
def baseEnd_4685157 : Nat := 801912494259010345130287

theorem tailTrace_4685157 : CollatzResearch.WordTrace tailWord_4685157 prefixEnd_4685157 801912494259010345130287 := by
  unfold tailWord_4685157
  simp only [CollatzResearch.WordTrace]
  refine ⟨170881714287483824956629725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113921142858322549971086483 170881714287483824956629725)
  ·
    refine ⟨64080642857806434358736147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170881714287483824956629725 64080642857806434358736147)
    ·
      refine ⟨96120964286709651538104221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64080642857806434358736147 96120964286709651538104221)
      ·
        refine ⟨36045361607516119326789083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96120964286709651538104221 36045361607516119326789083)
        ·
          refine ⟨54068042411274178990183625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36045361607516119326789083 54068042411274178990183625)
          ·
            refine ⟨40551031808455634242637719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54068042411274178990183625 40551031808455634242637719)
            ·
              refine ⟨60826547712683451363956579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40551031808455634242637719 60826547712683451363956579)
              ·
                refine ⟨91239821569025177045934869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60826547712683451363956579 91239821569025177045934869)
                ·
                  refine ⟨4276866636048055174028197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 91239821569025177045934869 4276866636048055174028197)
                  ·
                    refine ⟨801912494259010345130287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4276866636048055174028197 801912494259010345130287)
                    ·
                      rfl

theorem cell23_4685157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6, 4].length) (baseStart_4685157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685157 prefixEnd_4685157 := by exact prefixLift 4685157
  have htrace : WordTrace (prefixWord ++ tailWord_4685157) baseStart_4685157 baseEnd_4685157 := by
    simpa [prefixWord, tailWord_4685157, baseEnd_4685157] using wordTrace_append hprefix tailTrace_4685157
  have hstable : (prefixWord ++ tailWord_4685157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685157).length < 2 ^ (prefixWord ++ tailWord_4685157).sum := by decide
  have hdescent : baseEnd_4685157 < baseStart_4685157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685164 : List Nat := [2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 4]
def baseStart_4685164 : Nat := 118140960795 + 4685164 * 2 ^ 59
def prefixEnd_4685164 : Nat := 4983230072969 + 3 ^ 40 * 4685164 * 2
def baseEnd_4685164 : Nat := 2405741077141612508003329

theorem tailTrace_4685164 : CollatzResearch.WordTrace tailWord_4685164 prefixEnd_4685164 2405741077141612508003329 := by
  unfold tailWord_4685164
  simp only [CollatzResearch.WordTrace]
  refine ⟨85440984799229232576067273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113921313065638976768089697 85440984799229232576067273)
  ·
    refine ⟨64080738599421924432050455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85440984799229232576067273 64080738599421924432050455)
    ·
      refine ⟨96121107899132886648075683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64080738599421924432050455 96121107899132886648075683)
      ·
        refine ⟨144181661848699329972113525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96121107899132886648075683 144181661848699329972113525)
        ·
          refine ⟨13517030798315562184885643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 144181661848699329972113525 13517030798315562184885643)
          ·
            refine ⟨20275546197473343277328465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13517030798315562184885643 20275546197473343277328465)
            ·
              refine ⟨15206659648105007457996349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20275546197473343277328465 15206659648105007457996349)
              ·
                refine ⟨5702497368039377796748631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15206659648105007457996349 5702497368039377796748631)
                ·
                  refine ⟨8553746052059066695122947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5702497368039377796748631 8553746052059066695122947)
                  ·
                    refine ⟨12830619078088600042684421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8553746052059066695122947 12830619078088600042684421)
                    ·
                      refine ⟨2405741077141612508003329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12830619078088600042684421 2405741077141612508003329)
                      ·
                        rfl

theorem cell23_4685164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 4].length) (baseStart_4685164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685164 prefixEnd_4685164 := by exact prefixLift 4685164
  have htrace : WordTrace (prefixWord ++ tailWord_4685164) baseStart_4685164 baseEnd_4685164 := by
    simpa [prefixWord, tailWord_4685164, baseEnd_4685164] using wordTrace_append hprefix tailTrace_4685164
  have hstable : (prefixWord ++ tailWord_4685164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685164).length < 2 ^ (prefixWord ++ tailWord_4685164).sum := by decide
  have hdescent : baseEnd_4685164 < baseStart_4685164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685167 : List Nat := [1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 5]
def baseStart_4685167 : Nat := 118140960795 + 4685167 * 2 ^ 59
def prefixEnd_4685167 : Nat := 4983230072969 + 3 ^ 40 * 4685167 * 2
def baseEnd_4685167 : Nat := 2405742617583575996265815

theorem tailTrace_4685167 : CollatzResearch.WordTrace tailWord_4685167 prefixEnd_4685167 2405742617583575996265815 := by
  unfold tailWord_4685167
  simp only [CollatzResearch.WordTrace]
  refine ⟨170882079017447596664493755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113921386011631731109662503 170882079017447596664493755)
  ·
    refine ⟨256323118526171394996740633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170882079017447596664493755 256323118526171394996740633)
    ·
      refine ⟨192242338894628546247555475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256323118526171394996740633 192242338894628546247555475)
      ·
        refine ⟨288363508341942819371333213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192242338894628546247555475 288363508341942819371333213)
        ·
          refine ⟨108136315628228557264249955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 288363508341942819371333213 108136315628228557264249955)
          ·
            refine ⟨162204473442342835896374933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108136315628228557264249955 162204473442342835896374933)
            ·
              refine ⟨7603334692609820432642575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 162204473442342835896374933 7603334692609820432642575)
              ·
                refine ⟨11405002038914730648963863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7603334692609820432642575 11405002038914730648963863)
                ·
                  refine ⟨17107503058372095973445795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11405002038914730648963863 17107503058372095973445795)
                  ·
                    refine ⟨25661254587558143960168693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17107503058372095973445795 25661254587558143960168693)
                    ·
                      refine ⟨2405742617583575996265815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25661254587558143960168693 2405742617583575996265815)
                      ·
                        rfl

theorem cell23_4685167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 5].length) (baseStart_4685167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685167 prefixEnd_4685167 := by exact prefixLift 4685167
  have htrace : WordTrace (prefixWord ++ tailWord_4685167) baseStart_4685167 baseEnd_4685167 := by
    simpa [prefixWord, tailWord_4685167, baseEnd_4685167] using wordTrace_append hprefix tailTrace_4685167
  have hstable : (prefixWord ++ tailWord_4685167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685167).length < 2 ^ (prefixWord ++ tailWord_4685167).sum := by decide
  have hdescent : baseEnd_4685167 < baseStart_4685167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685187 : List Nat := [1, 1, 1, 3, 5, 2, 2, 8]
def baseStart_4685187 : Nat := 118140960795 + 4685187 * 2 ^ 59
def prefixEnd_4685187 : Nat := 4983230072969 + 3 ^ 40 * 4685187 * 2
def baseEnd_4685187 : Nat := 89101958785061700667249

theorem tailTrace_4685187 : CollatzResearch.WordTrace tailWord_4685187 prefixEnd_4685187 89101958785061700667249 := by
  unfold tailWord_4685187
  simp only [CollatzResearch.WordTrace]
  refine ⟨170882808477375140080221815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113921872318250093386814543 170882808477375140080221815)
  ·
    refine ⟨256324212716062710120332723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170882808477375140080221815 256324212716062710120332723)
    ·
      refine ⟨384486319074094065180499085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256324212716062710120332723 384486319074094065180499085)
      ·
        refine ⟨144182369652785274442687157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 384486319074094065180499085 144182369652785274442687157)
        ·
          refine ⟨13517097154948619479001921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 144182369652785274442687157 13517097154948619479001921)
          ·
            refine ⟨10137822866211464609251441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13517097154948619479001921 10137822866211464609251441)
            ·
              refine ⟨7603367149658598456938581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10137822866211464609251441 7603367149658598456938581)
              ·
                refine ⟨89101958785061700667249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7603367149658598456938581 89101958785061700667249)
                ·
                  rfl

theorem cell23_4685187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 8].length) (baseStart_4685187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685187 prefixEnd_4685187 := by exact prefixLift 4685187
  have htrace : WordTrace (prefixWord ++ tailWord_4685187) baseStart_4685187 baseEnd_4685187 := by
    simpa [prefixWord, tailWord_4685187, baseEnd_4685187] using wordTrace_append hprefix tailTrace_4685187
  have hstable : (prefixWord ++ tailWord_4685187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685187).length < 2 ^ (prefixWord ++ tailWord_4685187).sum := by decide
  have hdescent : baseEnd_4685187 < baseStart_4685187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685191 : List Nat := [1, 1, 4, 2, 2, 2, 4, 1, 2, 4]
def baseStart_4685191 : Nat := 118140960795 + 4685191 * 2 ^ 59
def prefixEnd_4685191 : Nat := 4983230072969 + 3 ^ 40 * 4685191 * 2
def baseEnd_4685191 : Nat := 801918313706427967455235

theorem tailTrace_4685191 : CollatzResearch.WordTrace tailWord_4685191 prefixEnd_4685191 801918313706427967455235 := by
  unfold tailWord_4685191
  simp only [CollatzResearch.WordTrace]
  refine ⟨170882954369360648763367427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113921969579573765842244951 170882954369360648763367427)
  ·
    refine ⟨256324431554040973145051141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170882954369360648763367427 256324431554040973145051141)
    ·
      refine ⟨48060830916382682464697089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 256324431554040973145051141 48060830916382682464697089)
      ·
        refine ⟨36045623187287011848522817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48060830916382682464697089 36045623187287011848522817)
        ·
          refine ⟨27034217390465258886392113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36045623187287011848522817 27034217390465258886392113)
          ·
            refine ⟨20275663042848944164794085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27034217390465258886392113 20275663042848944164794085)
            ·
              refine ⟨3801686820534177030898891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20275663042848944164794085 3801686820534177030898891)
              ·
                refine ⟨5702530230801265546348337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3801686820534177030898891 5702530230801265546348337)
                ·
                  refine ⟨4276897673100949159761253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5702530230801265546348337 4276897673100949159761253)
                  ·
                    refine ⟨801918313706427967455235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4276897673100949159761253 801918313706427967455235)
                    ·
                      rfl

theorem cell23_4685191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_4685191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685191 prefixEnd_4685191 := by exact prefixLift 4685191
  have htrace : WordTrace (prefixWord ++ tailWord_4685191) baseStart_4685191 baseEnd_4685191 := by
    simpa [prefixWord, tailWord_4685191, baseEnd_4685191] using wordTrace_append hprefix tailTrace_4685191
  have hstable : (prefixWord ++ tailWord_4685191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685191).length < 2 ^ (prefixWord ++ tailWord_4685191).sum := by decide
  have hdescent : baseEnd_4685191 < baseStart_4685191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685198 : List Nat := [4, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4]
def baseStart_4685198 : Nat := 118140960795 + 4685198 * 2 ^ 59
def prefixEnd_4685198 : Nat := 4983230072969 + 3 ^ 40 * 4685198 * 2
def baseEnd_4685198 : Nat := 2405758535483865374978173

theorem tailTrace_4685198 : CollatzResearch.WordTrace tailWord_4685198 prefixEnd_4685198 2405758535483865374978173 := by
  unfold tailWord_4685198
  simp only [CollatzResearch.WordTrace]
  refine ⟨21360401210041911119859031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113922139786890192639248165 21360401210041911119859031)
  ·
    refine ⟨32040601815062866679788547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21360401210041911119859031 32040601815062866679788547)
    ·
      refine ⟨48060902722594300019682821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32040601815062866679788547 48060902722594300019682821)
      ·
        refine ⟨9011419260486431253690529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48060902722594300019682821 9011419260486431253690529)
        ·
          refine ⟨6758564445364823440267897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9011419260486431253690529 6758564445364823440267897)
          ·
            refine ⟨5068923334023617580200923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6758564445364823440267897 5068923334023617580200923)
            ·
              refine ⟨7603385001035426370301385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5068923334023617580200923 7603385001035426370301385)
              ·
                refine ⟨5702538750776569777726039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7603385001035426370301385 5702538750776569777726039)
                ·
                  refine ⟨8553808126164854666589059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5702538750776569777726039 8553808126164854666589059)
                  ·
                    refine ⟨12830712189247281999883589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8553808126164854666589059 12830712189247281999883589)
                    ·
                      refine ⟨2405758535483865374978173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12830712189247281999883589 2405758535483865374978173)
                      ·
                        rfl

theorem cell23_4685198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_4685198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685198 prefixEnd_4685198 := by exact prefixLift 4685198
  have htrace : WordTrace (prefixWord ++ tailWord_4685198) baseStart_4685198 baseEnd_4685198 := by
    simpa [prefixWord, tailWord_4685198, baseEnd_4685198] using wordTrace_append hprefix tailTrace_4685198
  have hstable : (prefixWord ++ tailWord_4685198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685198).length < 2 ^ (prefixWord ++ tailWord_4685198).sum := by decide
  have hdescent : baseEnd_4685198 < baseStart_4685198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685218 : List Nat := [3, 3, 1, 2, 1, 3, 3, 1, 1, 2, 3]
def baseStart_4685218 : Nat := 118140960795 + 4685218 * 2 ^ 59
def prefixEnd_4685218 : Nat := 4983230072969 + 3 ^ 40 * 4685218 * 2
def baseEnd_4685218 : Nat := 2405768805096955296728081

theorem tailTrace_4685218 : CollatzResearch.WordTrace tailWord_4685218 prefixEnd_4685218 2405768805096955296728081 := by
  unfold tailWord_4685218
  simp only [CollatzResearch.WordTrace]
  refine ⟨42720984785065708093650077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113922626093508554916400205 42720984785065708093650077)
  ·
    refine ⟨16020369294399640535118779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42720984785065708093650077 16020369294399640535118779)
    ·
      refine ⟨24030553941599460802678169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16020369294399640535118779 24030553941599460802678169)
      ·
        refine ⟨18022915456199595602008627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24030553941599460802678169 18022915456199595602008627)
        ·
          refine ⟨27034373184299393403012941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18022915456199595602008627 27034373184299393403012941)
          ·
            refine ⟨10137889944112272526129853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27034373184299393403012941 10137889944112272526129853)
            ·
              refine ⟨3801708729042102197298695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10137889944112272526129853 3801708729042102197298695)
              ·
                refine ⟨5702563093563153295948043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3801708729042102197298695 5702563093563153295948043)
                ·
                  refine ⟨8553844640344729943922065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5702563093563153295948043 8553844640344729943922065)
                  ·
                    refine ⟨6415383480258547457941549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8553844640344729943922065 6415383480258547457941549)
                    ·
                      refine ⟨2405768805096955296728081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6415383480258547457941549 2405768805096955296728081)
                      ·
                        rfl

theorem cell23_4685218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_4685218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685218 prefixEnd_4685218 := by exact prefixLift 4685218
  have htrace : WordTrace (prefixWord ++ tailWord_4685218) baseStart_4685218 baseEnd_4685218 := by
    simpa [prefixWord, tailWord_4685218, baseEnd_4685218] using wordTrace_append hprefix tailTrace_4685218
  have hstable : (prefixWord ++ tailWord_4685218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685218).length < 2 ^ (prefixWord ++ tailWord_4685218).sum := by decide
  have hdescent : baseEnd_4685218 < baseStart_4685218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685257 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 4, 4, 3]
def baseStart_4685257 : Nat := 118140960795 + 4685257 * 2 ^ 59
def prefixEnd_4685257 : Nat := 4983230072969 + 3 ^ 40 * 4685257 * 2
def baseEnd_4685257 : Nat := 2405788830842480644140401

theorem tailTrace_4685257 : CollatzResearch.WordTrace tailWord_4685257 prefixEnd_4685257 2405788830842480644140401 := by
  unfold tailWord_4685257
  simp only [CollatzResearch.WordTrace]
  refine ⟨170885361587121542035270025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113923574391414361356846683 170885361587121542035270025)
  ·
    refine ⟨128164021190341156526452519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170885361587121542035270025 128164021190341156526452519)
    ·
      refine ⟨192246031785511734789678779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128164021190341156526452519 192246031785511734789678779)
      ·
        refine ⟨288369047678267602184518169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192246031785511734789678779 288369047678267602184518169)
        ·
          refine ⟨216276785758700701638388627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288369047678267602184518169 216276785758700701638388627)
          ·
            refine ⟨324415178638051052457582941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216276785758700701638388627 324415178638051052457582941)
            ·
              refine ⟨121655691989269144671593603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 324415178638051052457582941 121655691989269144671593603)
              ·
                refine ⟨182483537983903717007390405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121655691989269144671593603 182483537983903717007390405)
                ·
                  refine ⟨34215663371981946938885701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 182483537983903717007390405 34215663371981946938885701)
                  ·
                    refine ⟨6415436882246615051041069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34215663371981946938885701 6415436882246615051041069)
                    ·
                      refine ⟨2405788830842480644140401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6415436882246615051041069 2405788830842480644140401)
                      ·
                        rfl

theorem cell23_4685257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 4, 3].length) (baseStart_4685257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685257 prefixEnd_4685257 := by exact prefixLift 4685257
  have htrace : WordTrace (prefixWord ++ tailWord_4685257) baseStart_4685257 baseEnd_4685257 := by
    simpa [prefixWord, tailWord_4685257, baseEnd_4685257] using wordTrace_append hprefix tailTrace_4685257
  have hstable : (prefixWord ++ tailWord_4685257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685257).length < 2 ^ (prefixWord ++ tailWord_4685257).sum := by decide
  have hdescent : baseEnd_4685257 < baseStart_4685257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685294 : List Nat := [4, 1, 2, 1, 2, 1, 4, 1, 7]
def baseStart_4685294 : Nat := 118140960795 + 4685294 * 2 ^ 59
def prefixEnd_4685294 : Nat := 4983230072969 + 3 ^ 40 * 4685294 * 2
def baseEnd_4685294 : Nat := 267311981069632999930859

theorem tailTrace_4685294 : CollatzResearch.WordTrace tailWord_4685294 prefixEnd_4685294 267311981069632999930859 := by
  unfold tailWord_4685294
  simp only [CollatzResearch.WordTrace]
  refine ⟨21360838885998437169295867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113924474058658331569577957 21360838885998437169295867)
  ·
    refine ⟨32041258328997655753943801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21360838885998437169295867 32041258328997655753943801)
    ·
      refine ⟨24030943746748241815457851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32041258328997655753943801 24030943746748241815457851)
      ·
        refine ⟨36046415620122362723186777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24030943746748241815457851 36046415620122362723186777)
        ·
          refine ⟨27034811715091772042390083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36046415620122362723186777 27034811715091772042390083)
          ·
            refine ⟨40552217572637658063585125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27034811715091772042390083 40552217572637658063585125)
            ·
              refine ⟨7603540794869560886922211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40552217572637658063585125 7603540794869560886922211)
              ·
                refine ⟨11405311192304341330383317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7603540794869560886922211 11405311192304341330383317)
                ·
                  refine ⟨267311981069632999930859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11405311192304341330383317 267311981069632999930859)
                  ·
                    rfl

theorem cell23_4685294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 7].length) (baseStart_4685294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685294 prefixEnd_4685294 := by exact prefixLift 4685294
  have htrace : WordTrace (prefixWord ++ tailWord_4685294) baseStart_4685294 baseEnd_4685294 := by
    simpa [prefixWord, tailWord_4685294, baseEnd_4685294] using wordTrace_append hprefix tailTrace_4685294
  have hstable : (prefixWord ++ tailWord_4685294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685294).length < 2 ^ (prefixWord ++ tailWord_4685294).sum := by decide
  have hdescent : baseEnd_4685294 < baseStart_4685294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685301 : List Nat := [1, 3, 5, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_4685301 : Nat := 118140960795 + 4685301 * 2 ^ 59
def prefixEnd_4685301 : Nat := 4983230072969 + 3 ^ 40 * 4685301 * 2
def baseEnd_4685301 : Nat := 2405811423991278471990199

theorem tailTrace_4685301 : CollatzResearch.WordTrace tailWord_4685301 prefixEnd_4685301 2405811423991278471990199 := by
  unfold tailWord_4685301
  simp only [CollatzResearch.WordTrace]
  refine ⟨170886966398962137549871757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113924644265974758366581171 170886966398962137549871757)
  ·
    refine ⟨64082612399610801581201909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170886966398962137549871757 64082612399610801581201909)
    ·
      refine ⟨6007744912463512648237679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64082612399610801581201909 6007744912463512648237679)
      ·
        refine ⟨9011617368695268972356519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6007744912463512648237679 9011617368695268972356519)
        ·
          refine ⟨13517426053042903458534779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9011617368695268972356519 13517426053042903458534779)
          ·
            refine ⟨20276139079564355187802169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13517426053042903458534779 20276139079564355187802169)
            ·
              refine ⟨15207104309673266390851627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20276139079564355187802169 15207104309673266390851627)
              ·
                refine ⟨22810656464509899586277441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15207104309673266390851627 22810656464509899586277441)
                ·
                  refine ⟨17107992348382424689708081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22810656464509899586277441 17107992348382424689708081)
                  ·
                    refine ⟨12830994261286818517281061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17107992348382424689708081 12830994261286818517281061)
                    ·
                      refine ⟨2405811423991278471990199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12830994261286818517281061 2405811423991278471990199)
                      ·
                        rfl

theorem cell23_4685301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_4685301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685301 prefixEnd_4685301 := by exact prefixLift 4685301
  have htrace : WordTrace (prefixWord ++ tailWord_4685301) baseStart_4685301 baseEnd_4685301 := by
    simpa [prefixWord, tailWord_4685301, baseEnd_4685301] using wordTrace_append hprefix tailTrace_4685301
  have hstable : (prefixWord ++ tailWord_4685301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685301).length < 2 ^ (prefixWord ++ tailWord_4685301).sum := by decide
  have hdescent : baseEnd_4685301 < baseStart_4685301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685304 : List Nat := [2, 1, 2, 1, 1, 5, 2, 1, 2, 3, 3]
def baseStart_4685304 : Nat := 118140960795 + 4685304 * 2 ^ 59
def prefixEnd_4685304 : Nat := 4983230072969 + 3 ^ 40 * 4685304 * 2
def baseEnd_4685304 : Nat := 2405812964433241960252685

theorem tailTrace_4685304 : CollatzResearch.WordTrace tailWord_4685304 prefixEnd_4685304 2405812964433241960252685 := by
  unfold tailWord_4685304
  simp only [CollatzResearch.WordTrace]
  refine ⟨85443537908975634531115483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113924717211967512708153977 85443537908975634531115483)
  ·
    refine ⟨128165306863463451796673225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85443537908975634531115483 128165306863463451796673225)
    ·
      refine ⟨96123980147597588847504919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128165306863463451796673225 96123980147597588847504919)
      ·
        refine ⟨144185970221396383271257379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96123980147597588847504919 144185970221396383271257379)
        ·
          refine ⟨216278955332094574906886069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144185970221396383271257379 216278955332094574906886069)
          ·
            refine ⟨20276152062383866397520569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 216278955332094574906886069 20276152062383866397520569)
            ·
              refine ⟨15207114046787899798140427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20276152062383866397520569 15207114046787899798140427)
              ·
                refine ⟨22810671070181849697210641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15207114046787899798140427 22810671070181849697210641)
                ·
                  refine ⟨17108003302636387272907981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22810671070181849697210641 17108003302636387272907981)
                  ·
                    refine ⟨6415501238488645227340493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17108003302636387272907981 6415501238488645227340493)
                    ·
                      refine ⟨2405812964433241960252685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6415501238488645227340493 2405812964433241960252685)
                      ·
                        rfl

theorem cell23_4685304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 2, 3, 3].length) (baseStart_4685304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685304 prefixEnd_4685304 := by exact prefixLift 4685304
  have htrace : WordTrace (prefixWord ++ tailWord_4685304) baseStart_4685304 baseEnd_4685304 := by
    simpa [prefixWord, tailWord_4685304, baseEnd_4685304] using wordTrace_append hprefix tailTrace_4685304
  have hstable : (prefixWord ++ tailWord_4685304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685304).length < 2 ^ (prefixWord ++ tailWord_4685304).sum := by decide
  have hdescent : baseEnd_4685304 < baseStart_4685304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685307 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 4, 5]
def baseStart_4685307 : Nat := 118140960795 + 4685307 * 2 ^ 59
def prefixEnd_4685307 : Nat := 4983230072969 + 3 ^ 40 * 4685307 * 2
def baseEnd_4685307 : Nat := 801938168291735149505057

theorem tailTrace_4685307 : CollatzResearch.WordTrace tailWord_4685307 prefixEnd_4685307 801938168291735149505057 := by
  unfold tailWord_4685307
  simp only [CollatzResearch.WordTrace]
  refine ⟨170887185236940400574590175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113924790157960267049726783 170887185236940400574590175)
  ·
    refine ⟨256330777855410600861885263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170887185236940400574590175 256330777855410600861885263)
    ·
      refine ⟨384496166783115901292827895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256330777855410600861885263 384496166783115901292827895)
      ·
        refine ⟨576744250174673851939241843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384496166783115901292827895 576744250174673851939241843)
        ·
          refine ⟨865116375262010777908862765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 576744250174673851939241843 865116375262010777908862765)
          ·
            refine ⟨324418640723254041715823537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 865116375262010777908862765 324418640723254041715823537)
            ·
              refine ⟨243313980542440531286867653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 324418640723254041715823537 243313980542440531286867653)
              ·
                refine ⟨45621371351707599616287685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 243313980542440531286867653 45621371351707599616287685)
                ·
                  refine ⟨8554007128445174928053941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45621371351707599616287685 8554007128445174928053941)
                  ·
                    refine ⟨801938168291735149505057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8554007128445174928053941 801938168291735149505057)
                    ·
                      rfl

theorem cell23_4685307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 5].length) (baseStart_4685307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685307 prefixEnd_4685307 := by exact prefixLift 4685307
  have htrace : WordTrace (prefixWord ++ tailWord_4685307) baseStart_4685307 baseEnd_4685307 := by
    simpa [prefixWord, tailWord_4685307, baseEnd_4685307] using wordTrace_append hprefix tailTrace_4685307
  have hstable : (prefixWord ++ tailWord_4685307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685307).length < 2 ^ (prefixWord ++ tailWord_4685307).sum := by decide
  have hdescent : baseEnd_4685307 < baseStart_4685307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685317 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 3, 2, 5]
def baseStart_4685317 : Nat := 118140960795 + 4685317 * 2 ^ 59
def prefixEnd_4685317 : Nat := 4983230072969 + 3 ^ 40 * 4685317 * 2
def baseEnd_4685317 : Nat := 2405819639681750409390125

theorem tailTrace_4685317 : CollatzResearch.WordTrace tailWord_4685317 prefixEnd_4685317 2405819639681750409390125 := by
  unfold tailWord_4685317
  simp only [CollatzResearch.WordTrace]
  refine ⟨170887549966904172282454205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113925033311269448188302803 170887549966904172282454205)
  ·
    refine ⟨64082831237589064605920327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170887549966904172282454205 64082831237589064605920327)
    ·
      refine ⟨96124246856383596908880491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64082831237589064605920327 96124246856383596908880491)
      ·
        refine ⟨144186370284575395363320737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96124246856383596908880491 144186370284575395363320737)
        ·
          refine ⟨108139777713431546522490553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144186370284575395363320737 108139777713431546522490553)
          ·
            refine ⟨81104833285073659891867915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108139777713431546522490553 81104833285073659891867915)
            ·
              refine ⟨121657249927610489837801873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81104833285073659891867915 121657249927610489837801873)
              ·
                refine ⟨91242937445707867378351405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121657249927610489837801873 91242937445707867378351405)
                ·
                  refine ⟨34216101542140450266881777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91242937445707867378351405 34216101542140450266881777)
                  ·
                    refine ⟨25662076156605337700161333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34216101542140450266881777 25662076156605337700161333)
                    ·
                      refine ⟨2405819639681750409390125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25662076156605337700161333 2405819639681750409390125)
                      ·
                        rfl

theorem cell23_4685317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_4685317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685317 prefixEnd_4685317 := by exact prefixLift 4685317
  have htrace : WordTrace (prefixWord ++ tailWord_4685317) baseStart_4685317 baseEnd_4685317 := by
    simpa [prefixWord, tailWord_4685317, baseEnd_4685317] using wordTrace_append hprefix tailTrace_4685317
  have hstable : (prefixWord ++ tailWord_4685317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685317).length < 2 ^ (prefixWord ++ tailWord_4685317).sum := by decide
  have hdescent : baseEnd_4685317 < baseStart_4685317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685327 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 4]
def baseStart_4685327 : Nat := 118140960795 + 4685327 * 2 ^ 59
def prefixEnd_4685327 : Nat := 4983230072969 + 3 ^ 40 * 4685327 * 2
def baseEnd_4685327 : Nat := 2405824774488295370265079

theorem tailTrace_4685327 : CollatzResearch.WordTrace tailWord_4685327 prefixEnd_4685327 2405824774488295370265079 := by
  unfold tailWord_4685327
  simp only [CollatzResearch.WordTrace]
  refine ⟨170887914696867943990318235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113925276464578629326878823 170887914696867943990318235)
  ·
    refine ⟨256331872045301915985477353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170887914696867943990318235 256331872045301915985477353)
    ·
      refine ⟨192248904033976436989108015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256331872045301915985477353 192248904033976436989108015)
      ·
        refine ⟨288373356050964655483662023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192248904033976436989108015 288373356050964655483662023)
        ·
          refine ⟨432560034076446983225493035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288373356050964655483662023 432560034076446983225493035)
          ·
            refine ⟨648840051114670474838239553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432560034076446983225493035 648840051114670474838239553)
            ·
              refine ⟨486630038336002856128679665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 648840051114670474838239553 486630038336002856128679665)
              ·
                refine ⟨364972528752002142096509749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 486630038336002856128679665 364972528752002142096509749)
                ·
                  refine ⟨34216174570500200821547789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 364972528752002142096509749 34216174570500200821547789)
                  ·
                    refine ⟨12831065463937575308080421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34216174570500200821547789 12831065463937575308080421)
                    ·
                      refine ⟨2405824774488295370265079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12831065463937575308080421 2405824774488295370265079)
                      ·
                        rfl

theorem cell23_4685327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 4].length) (baseStart_4685327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685327 prefixEnd_4685327 := by exact prefixLift 4685327
  have htrace : WordTrace (prefixWord ++ tailWord_4685327) baseStart_4685327 baseEnd_4685327 := by
    simpa [prefixWord, tailWord_4685327, baseEnd_4685327] using wordTrace_append hprefix tailTrace_4685327
  have hstable : (prefixWord ++ tailWord_4685327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685327).length < 2 ^ (prefixWord ++ tailWord_4685327).sum := by decide
  have hdescent : baseEnd_4685327 < baseStart_4685327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685381 : List Nat := [1, 3, 1, 1, 1, 4, 4, 1, 2, 2, 3]
def baseStart_4685381 : Nat := 118140960795 + 4685381 * 2 ^ 59
def prefixEnd_4685381 : Nat := 4983230072969 + 3 ^ 40 * 4685381 * 2
def baseEnd_4685381 : Nat := 2405852502443638158989831

theorem tailTrace_4685381 : CollatzResearch.WordTrace tailWord_4685381 prefixEnd_4685381 2405852502443638158989831 := by
  unfold tailWord_4685381
  simp only [CollatzResearch.WordTrace]
  refine ⟨170889884238672311212783997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113926589492448207475189331 170889884238672311212783997)
  ·
    refine ⟨64083706589502116704793999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170889884238672311212783997 64083706589502116704793999)
    ·
      refine ⟨96125559884253175057190999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64083706589502116704793999 96125559884253175057190999)
      ·
        refine ⟨144188339826379762585786499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96125559884253175057190999 144188339826379762585786499)
        ·
          refine ⟨216282509739569643878679749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144188339826379762585786499 216282509739569643878679749)
          ·
            refine ⟨40552970576169308227252453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 216282509739569643878679749 40552970576169308227252453)
            ·
              refine ⟨7603681983031745292609835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40552970576169308227252453 7603681983031745292609835)
              ·
                refine ⟨11405522974547617938914753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7603681983031745292609835 11405522974547617938914753)
                ·
                  refine ⟨8554142230910713454186065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11405522974547617938914753 8554142230910713454186065)
                  ·
                    refine ⟨6415606673183035090639549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8554142230910713454186065 6415606673183035090639549)
                    ·
                      refine ⟨2405852502443638158989831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6415606673183035090639549 2405852502443638158989831)
                      ·
                        rfl

theorem cell23_4685381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 2, 3].length) (baseStart_4685381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685381 prefixEnd_4685381 := by exact prefixLift 4685381
  have htrace : WordTrace (prefixWord ++ tailWord_4685381) baseStart_4685381 baseEnd_4685381 := by
    simpa [prefixWord, tailWord_4685381, baseEnd_4685381] using wordTrace_append hprefix tailTrace_4685381
  have hstable : (prefixWord ++ tailWord_4685381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685381).length < 2 ^ (prefixWord ++ tailWord_4685381).sum := by decide
  have hdescent : baseEnd_4685381 < baseStart_4685381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685387 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 8]
def baseStart_4685387 : Nat := 118140960795 + 4685387 * 2 ^ 59
def prefixEnd_4685387 : Nat := 4983230072969 + 3 ^ 40 * 4685387 * 2
def baseEnd_4685387 : Nat := 2405855583327565135514803

theorem tailTrace_4685387 : CollatzResearch.WordTrace tailWord_4685387 prefixEnd_4685387 2405855583327565135514803 := by
  unfold tailWord_4685387
  simp only [CollatzResearch.WordTrace]
  refine ⟨170890103076650574237502415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113926735384433716158334943 170890103076650574237502415)
  ·
    refine ⟨256335154614975861356253623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170890103076650574237502415 256335154614975861356253623)
    ·
      refine ⟨384502731922463792034380435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256335154614975861356253623 384502731922463792034380435)
      ·
        refine ⟨576754097883695688051570653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384502731922463792034380435 576754097883695688051570653)
        ·
          refine ⟨216282786706385883019338995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 576754097883695688051570653 216282786706385883019338995)
          ·
            refine ⟨324424180059578824529008493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216282786706385883019338995 324424180059578824529008493)
            ·
              refine ⟨121659067522342059198378185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 324424180059578824529008493 121659067522342059198378185)
              ·
                refine ⟨91244300641756544398783639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121659067522342059198378185 91244300641756544398783639)
                ·
                  refine ⟨136866450962634816598175459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91244300641756544398783639 136866450962634816598175459)
                  ·
                    refine ⟨205299676443952224897263189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 136866450962634816598175459 205299676443952224897263189)
                    ·
                      refine ⟨2405855583327565135514803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 205299676443952224897263189 2405855583327565135514803)
                      ·
                        rfl

theorem cell23_4685387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 8].length) (baseStart_4685387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685387 prefixEnd_4685387 := by exact prefixLift 4685387
  have htrace : WordTrace (prefixWord ++ tailWord_4685387) baseStart_4685387 baseEnd_4685387 := by
    simpa [prefixWord, tailWord_4685387, baseEnd_4685387] using wordTrace_append hprefix tailTrace_4685387
  have hstable : (prefixWord ++ tailWord_4685387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685387).length < 2 ^ (prefixWord ++ tailWord_4685387).sum := by decide
  have hdescent : baseEnd_4685387 < baseStart_4685387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685445 : List Nat := [1, 3, 1, 1, 4, 1, 4, 3, 1, 1, 3]
def baseStart_4685445 : Nat := 118140960795 + 4685445 * 2 ^ 59
def prefixEnd_4685445 : Nat := 4983230072969 + 3 ^ 40 * 4685445 * 2
def baseEnd_4685445 : Nat := 2405885365205525908589537

theorem tailTrace_4685445 : CollatzResearch.WordTrace tailWord_4685445 prefixEnd_4685445 2405885365205525908589537 := by
  unfold tailWord_4685445
  simp only [CollatzResearch.WordTrace]
  refine ⟨170892218510440450143113789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113928145673626966762075859 170892218510440450143113789)
  ·
    refine ⟨64084581941415168803667671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170892218510440450143113789 64084581941415168803667671)
    ·
      refine ⟨96126872912122753205501507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64084581941415168803667671 96126872912122753205501507)
      ·
        refine ⟨144190309368184129808252261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96126872912122753205501507 144190309368184129808252261)
        ·
          refine ⟨27035683006534524339047299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144190309368184129808252261 27035683006534524339047299)
          ·
            refine ⟨40553524509801786508570949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27035683006534524339047299 40553524509801786508570949)
            ·
              refine ⟨7603785845587834970357053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40553524509801786508570949 7603785845587834970357053)
              ·
                refine ⟨2851419692095438113883895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7603785845587834970357053 2851419692095438113883895)
                ·
                  refine ⟨4277129538143157170825843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2851419692095438113883895 4277129538143157170825843)
                  ·
                    refine ⟨6415694307214735756238765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4277129538143157170825843 6415694307214735756238765)
                    ·
                      refine ⟨2405885365205525908589537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6415694307214735756238765 2405885365205525908589537)
                      ·
                        rfl

theorem cell23_4685445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3, 1, 1, 3].length) (baseStart_4685445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685445 prefixEnd_4685445 := by exact prefixLift 4685445
  have htrace : WordTrace (prefixWord ++ tailWord_4685445) baseStart_4685445 baseEnd_4685445 := by
    simpa [prefixWord, tailWord_4685445, baseEnd_4685445] using wordTrace_append hprefix tailTrace_4685445
  have hstable : (prefixWord ++ tailWord_4685445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685445).length < 2 ^ (prefixWord ++ tailWord_4685445).sum := by decide
  have hdescent : baseEnd_4685445 < baseStart_4685445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685451 : List Nat := [1, 1, 1, 1, 4, 1, 5, 3, 1, 1, 4]
def baseStart_4685451 : Nat := 118140960795 + 4685451 * 2 ^ 59
def prefixEnd_4685451 : Nat := 4983230072969 + 3 ^ 40 * 4685451 * 2
def baseEnd_4685451 : Nat := 2405888446089452885114509

theorem tailTrace_4685451 : CollatzResearch.WordTrace tailWord_4685451 prefixEnd_4685451 2405888446089452885114509 := by
  unfold tailWord_4685451
  simp only [CollatzResearch.WordTrace]
  refine ⟨170892437348418713167832207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113928291565612475445221471 170892437348418713167832207)
  ·
    refine ⟨256338656022628069751748311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170892437348418713167832207 256338656022628069751748311)
    ·
      refine ⟨384507984033942104627622467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256338656022628069751748311 384507984033942104627622467)
      ·
        refine ⟨576761976050913156941433701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384507984033942104627622467 576761976050913156941433701)
        ·
          refine ⟨108142870509546216926518819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 576761976050913156941433701 108142870509546216926518819)
          ·
            refine ⟨162214305764319325389778229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108142870509546216926518819 162214305764319325389778229)
            ·
              refine ⟨15207591165404936755291709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 162214305764319325389778229 15207591165404936755291709)
              ·
                refine ⟨5702846687026851283234391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15207591165404936755291709 5702846687026851283234391)
                ·
                  refine ⟨8554270030540276924851587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5702846687026851283234391 8554270030540276924851587)
                  ·
                    refine ⟨12831405045810415387277381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8554270030540276924851587 12831405045810415387277381)
                    ·
                      refine ⟨2405888446089452885114509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12831405045810415387277381 2405888446089452885114509)
                      ·
                        rfl

theorem cell23_4685451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 1, 4].length) (baseStart_4685451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685451 prefixEnd_4685451 := by exact prefixLift 4685451
  have htrace : WordTrace (prefixWord ++ tailWord_4685451) baseStart_4685451 baseEnd_4685451 := by
    simpa [prefixWord, tailWord_4685451, baseEnd_4685451] using wordTrace_append hprefix tailTrace_4685451
  have hstable : (prefixWord ++ tailWord_4685451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685451).length < 2 ^ (prefixWord ++ tailWord_4685451).sum := by decide
  have hdescent : baseEnd_4685451 < baseStart_4685451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685485 : List Nat := [1, 5, 2, 1, 1, 1, 1, 4, 3, 2, 2]
def baseStart_4685485 : Nat := 118140960795 + 4685485 * 2 ^ 59
def prefixEnd_4685485 : Nat := 4983230072969 + 3 ^ 40 * 4685485 * 2
def baseEnd_4685485 : Nat := 2405905904431705752089353

theorem tailTrace_4685485 : CollatzResearch.WordTrace tailWord_4685485 prefixEnd_4685485 2405905904431705752089353 := by
  unfold tailWord_4685485
  simp only [CollatzResearch.WordTrace]
  refine ⟨170893677430295536974569909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113929118286863691316379939 170893677430295536974569909)
  ·
    refine ⟨16021282259090206591365929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 170893677430295536974569909 16021282259090206591365929)
    ·
      refine ⟨12015961694317654943524447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16021282259090206591365929 12015961694317654943524447)
      ·
        refine ⟨18023942541476482415286671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12015961694317654943524447 18023942541476482415286671)
        ·
          refine ⟨27035913812214723622930007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18023942541476482415286671 27035913812214723622930007)
          ·
            refine ⟨40553870718322085434395011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27035913812214723622930007 40553870718322085434395011)
            ·
              refine ⟨60830806077483128151592517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40553870718322085434395011 60830806077483128151592517)
              ·
                refine ⟨11405776139528086528423597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60830806077483128151592517 11405776139528086528423597)
                ·
                  refine ⟨4277166052323032448158849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11405776139528086528423597 4277166052323032448158849)
                  ·
                    refine ⟨3207874539242274336119137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4277166052323032448158849 3207874539242274336119137)
                    ·
                      refine ⟨2405905904431705752089353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3207874539242274336119137 2405905904431705752089353)
                      ·
                        rfl

theorem cell23_4685485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_4685485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685485 prefixEnd_4685485 := by exact prefixLift 4685485
  have htrace : WordTrace (prefixWord ++ tailWord_4685485) baseStart_4685485 baseEnd_4685485 := by
    simpa [prefixWord, tailWord_4685485, baseEnd_4685485] using wordTrace_append hprefix tailTrace_4685485
  have hstable : (prefixWord ++ tailWord_4685485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685485).length < 2 ^ (prefixWord ++ tailWord_4685485).sum := by decide
  have hdescent : baseEnd_4685485 < baseStart_4685485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685501 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 3, 3, 3]
def baseStart_4685501 : Nat := 118140960795 + 4685501 * 2 ^ 59
def prefixEnd_4685501 : Nat := 4983230072969 + 3 ^ 40 * 4685501 * 2
def baseEnd_4685501 : Nat := 2405914120122177689489279

theorem tailTrace_4685501 : CollatzResearch.WordTrace tailWord_4685501 prefixEnd_4685501 2405914120122177689489279 := by
  unfold tailWord_4685501
  simp only [CollatzResearch.WordTrace]
  refine ⟨170894260998237571707152357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113929507332158381138101571 170894260998237571707152357)
  ·
    refine ⟨32042673937169544695091067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170894260998237571707152357 32042673937169544695091067)
    ·
      refine ⟨48064010905754317042636601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32042673937169544695091067 48064010905754317042636601)
      ·
        refine ⟨36048008179315737781977451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48064010905754317042636601 36048008179315737781977451)
        ·
          refine ⟨54072012268973606672966177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36048008179315737781977451 54072012268973606672966177)
          ·
            refine ⟨40554009201730205004724633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54072012268973606672966177 40554009201730205004724633)
            ·
              refine ⟨30415506901297653753543475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40554009201730205004724633 30415506901297653753543475)
              ·
                refine ⟨45623260351946480630315213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30415506901297653753543475 45623260351946480630315213)
                ·
                  refine ⟨17108722631979930236368205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45623260351946480630315213 17108722631979930236368205)
                  ·
                    refine ⟨6415770986992473838638077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17108722631979930236368205 6415770986992473838638077)
                    ·
                      refine ⟨2405914120122177689489279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6415770986992473838638077 2405914120122177689489279)
                      ·
                        rfl

theorem cell23_4685501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_4685501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685501 prefixEnd_4685501 := by exact prefixLift 4685501
  have htrace : WordTrace (prefixWord ++ tailWord_4685501) baseStart_4685501 baseEnd_4685501 := by
    simpa [prefixWord, tailWord_4685501, baseEnd_4685501] using wordTrace_append hprefix tailTrace_4685501
  have hstable : (prefixWord ++ tailWord_4685501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685501).length < 2 ^ (prefixWord ++ tailWord_4685501).sum := by decide
  have hdescent : baseEnd_4685501 < baseStart_4685501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685518 : List Nat := [4, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3]
def baseStart_4685518 : Nat := 118140960795 + 4685518 * 2 ^ 59
def prefixEnd_4685518 : Nat := 4983230072969 + 3 ^ 40 * 4685518 * 2
def baseEnd_4685518 : Nat := 2405922849293304122976701

theorem tailTrace_4685518 : CollatzResearch.WordTrace tailWord_4685518 prefixEnd_4685518 2405922849293304122976701 := by
  unfold tailWord_4685518
  simp only [CollatzResearch.WordTrace]
  refine ⟨21361860129896997951315151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113929920692783989073680805 21361860129896997951315151)
  ·
    refine ⟨32042790194845496926972727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21361860129896997951315151 32042790194845496926972727)
    ·
      refine ⟨48064185292268245390459091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32042790194845496926972727 48064185292268245390459091)
      ·
        refine ⟨72096277938402368085688637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48064185292268245390459091 72096277938402368085688637)
        ·
          refine ⟨27036104226900888032133239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72096277938402368085688637 27036104226900888032133239)
          ·
            refine ⟨40554156340351332048199859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27036104226900888032133239 40554156340351332048199859)
            ·
              refine ⟨60831234510526998072299789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40554156340351332048199859 60831234510526998072299789)
              ·
                refine ⟨22811712941447624277112421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60831234510526998072299789 22811712941447624277112421)
                ·
                  refine ⟨4277196176521429551958579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22811712941447624277112421 4277196176521429551958579)
                  ·
                    refine ⟨6415794264782144327937869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4277196176521429551958579 6415794264782144327937869)
                    ·
                      refine ⟨2405922849293304122976701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6415794264782144327937869 2405922849293304122976701)
                      ·
                        rfl

theorem cell23_4685518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_4685518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685518 prefixEnd_4685518 := by exact prefixLift 4685518
  have htrace : WordTrace (prefixWord ++ tailWord_4685518) baseStart_4685518 baseEnd_4685518 := by
    simpa [prefixWord, tailWord_4685518, baseEnd_4685518] using wordTrace_append hprefix tailTrace_4685518
  have hstable : (prefixWord ++ tailWord_4685518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685518).length < 2 ^ (prefixWord ++ tailWord_4685518).sum := by decide
  have hdescent : baseEnd_4685518 < baseStart_4685518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685528 : List Nat := [2, 1, 2, 2, 3, 1, 2, 2, 3, 3, 2]
def baseStart_4685528 : Nat := 118140960795 + 4685528 * 2 ^ 59
def prefixEnd_4685528 : Nat := 4983230072969 + 3 ^ 40 * 4685528 * 2
def baseEnd_4685528 : Nat := 2405927984099849083851655

theorem tailTrace_4685528 : CollatzResearch.WordTrace tailWord_4685528 prefixEnd_4685528 2405927984099849083851655 := by
  unfold tailWord_4685528
  simp only [CollatzResearch.WordTrace]
  refine ⟨85447622884569877659192619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113930163846093170212256825 85447622884569877659192619)
  ·
    refine ⟨128171434326854816488788929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85447622884569877659192619 128171434326854816488788929)
    ·
      refine ⟨96128575745141112366591697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128171434326854816488788929 96128575745141112366591697)
      ·
        refine ⟨72096431808855834274943773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96128575745141112366591697 72096431808855834274943773)
        ·
          refine ⟨27036161928320937853103915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72096431808855834274943773 27036161928320937853103915)
          ·
            refine ⟨40554242892481406779655873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27036161928320937853103915 40554242892481406779655873)
            ·
              refine ⟨30415682169361055084741905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40554242892481406779655873 30415682169361055084741905)
              ·
                refine ⟨22811761627020791313556429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30415682169361055084741905 22811761627020791313556429)
                ·
                  refine ⟨8554410610132796742583661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22811761627020791313556429 8554410610132796742583661)
                  ·
                    refine ⟨3207903978799798778468873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8554410610132796742583661 3207903978799798778468873)
                    ·
                      refine ⟨2405927984099849083851655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3207903978799798778468873 2405927984099849083851655)
                      ·
                        rfl

theorem cell23_4685528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 3, 2].length) (baseStart_4685528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685528 prefixEnd_4685528 := by exact prefixLift 4685528
  have htrace : WordTrace (prefixWord ++ tailWord_4685528) baseStart_4685528 baseEnd_4685528 := by
    simpa [prefixWord, tailWord_4685528, baseEnd_4685528] using wordTrace_append hprefix tailTrace_4685528
  have hstable : (prefixWord ++ tailWord_4685528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685528).length < 2 ^ (prefixWord ++ tailWord_4685528).sum := by decide
  have hdescent : baseEnd_4685528 < baseStart_4685528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685658 : List Nat := [3, 1, 1, 2, 1, 3, 1, 4, 3, 4]
def baseStart_4685658 : Nat := 118140960795 + 4685658 * 2 ^ 59
def prefixEnd_4685658 : Nat := 4983230072969 + 3 ^ 40 * 4685658 * 2
def baseEnd_4685658 : Nat := 801998245528311191742019

theorem tailTrace_4685658 : CollatzResearch.WordTrace tailWord_4685658 prefixEnd_4685658 801998245528311191742019 := by
  unfold tailWord_4685658
  simp only [CollatzResearch.WordTrace]
  refine ⟨42724996814667196880154407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113933324839112525013745085 42724996814667196880154407)
  ·
    refine ⟨64087495222000795320231611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42724996814667196880154407 64087495222000795320231611)
    ·
      refine ⟨96131242833001192980347417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64087495222000795320231611 96131242833001192980347417)
      ·
        refine ⟨72098432124750894735260563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96131242833001192980347417 72098432124750894735260563)
        ·
          refine ⟨108147648187126342102890845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72098432124750894735260563 108147648187126342102890845)
          ·
            refine ⟨40555368070172378288584067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108147648187126342102890845 40555368070172378288584067)
            ·
              refine ⟨60833052105258567432876101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40555368070172378288584067 60833052105258567432876101)
              ·
                refine ⟨11406197269735981393664269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60833052105258567432876101 11406197269735981393664269)
                ·
                  refine ⟨4277323976150993022624101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11406197269735981393664269 4277323976150993022624101)
                  ·
                    refine ⟨801998245528311191742019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4277323976150993022624101 801998245528311191742019)
                    ·
                      rfl

theorem cell23_4685658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 3, 4].length) (baseStart_4685658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685658 prefixEnd_4685658 := by exact prefixLift 4685658
  have htrace : WordTrace (prefixWord ++ tailWord_4685658) baseStart_4685658 baseEnd_4685658 := by
    simpa [prefixWord, tailWord_4685658, baseEnd_4685658] using wordTrace_append hprefix tailTrace_4685658
  have hstable : (prefixWord ++ tailWord_4685658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685658).length < 2 ^ (prefixWord ++ tailWord_4685658).sum := by decide
  have hdescent : baseEnd_4685658 < baseStart_4685658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685671 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 10]
def baseStart_4685671 : Nat := 118140960795 + 4685671 * 2 ^ 59
def prefixEnd_4685671 : Nat := 4983230072969 + 3 ^ 40 * 4685671 * 2
def baseEnd_4685671 : Nat := 267333490203715780484833

theorem tailTrace_4685671 : CollatzResearch.WordTrace tailWord_4685671 prefixEnd_4685671 267333490203715780484833 := by
  unfold tailWord_4685671
  simp only [CollatzResearch.WordTrace]
  refine ⟨170900461407621690740840867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113933640938414460493893911 170900461407621690740840867)
  ·
    refine ⟨256350692111432536111261301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170900461407621690740840867 256350692111432536111261301)
    ·
      refine ⟨24032877385446800260430747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 256350692111432536111261301 24032877385446800260430747)
      ·
        refine ⟨36049316078170200390646121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24032877385446800260430747 36049316078170200390646121)
        ·
          refine ⟨27036987058627650292984591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36049316078170200390646121 27036987058627650292984591)
          ·
            refine ⟨40555480587941475439476887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27036987058627650292984591 40555480587941475439476887)
            ·
              refine ⟨60833220881912213159215331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40555480587941475439476887 60833220881912213159215331)
              ·
                refine ⟨91249831322868319738822997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60833220881912213159215331 91249831322868319738822997)
                ·
                  refine ⟨267333490203715780484833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 91249831322868319738822997 267333490203715780484833)
                  ·
                    rfl

theorem cell23_4685671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 10].length) (baseStart_4685671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685671 prefixEnd_4685671 := by exact prefixLift 4685671
  have htrace : WordTrace (prefixWord ++ tailWord_4685671) baseStart_4685671 baseEnd_4685671 := by
    simpa [prefixWord, tailWord_4685671, baseEnd_4685671] using wordTrace_append hprefix tailTrace_4685671
  have hstable : (prefixWord ++ tailWord_4685671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685671).length < 2 ^ (prefixWord ++ tailWord_4685671).sum := by decide
  have hdescent : baseEnd_4685671 < baseStart_4685671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685685 : List Nat := [1, 3, 4, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_4685685 : Nat := 118140960795 + 4685685 * 2 ^ 59
def prefixEnd_4685685 : Nat := 4983230072969 + 3 ^ 40 * 4685685 * 2
def baseEnd_4685685 : Nat := 2406008600562604969588433

theorem tailTrace_4685685 : CollatzResearch.WordTrace tailWord_4685685 prefixEnd_4685685 2406008600562604969588433 := by
  unfold tailWord_4685685
  simp only [CollatzResearch.WordTrace]
  refine ⟨170900972029570971131850509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113933981353047314087900339 170900972029570971131850509)
  ·
    refine ⟨64087864511089114174443941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170900972029570971131850509 64087864511089114174443941)
    ·
      refine ⟨12016474595829208907708239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64087864511089114174443941 12016474595829208907708239)
      ·
        refine ⟨18024711893743813361562359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12016474595829208907708239 18024711893743813361562359)
        ·
          refine ⟨27037067840615720042343539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18024711893743813361562359 27037067840615720042343539)
          ·
            refine ⟨40555601760923580063515309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27037067840615720042343539 40555601760923580063515309)
            ·
              refine ⟨15208350660346342523818241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40555601760923580063515309 15208350660346342523818241)
              ·
                refine ⟨11406262995259756892863681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15208350660346342523818241 11406262995259756892863681)
                ·
                  refine ⟨8554697246444817669647761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11406262995259756892863681 8554697246444817669647761)
                  ·
                    refine ⟨6416022934833613252235821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8554697246444817669647761 6416022934833613252235821)
                    ·
                      refine ⟨2406008600562604969588433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6416022934833613252235821 2406008600562604969588433)
                      ·
                        rfl

theorem cell23_4685685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_4685685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685685 prefixEnd_4685685 := by exact prefixLift 4685685
  have htrace : WordTrace (prefixWord ++ tailWord_4685685) baseStart_4685685 baseEnd_4685685 := by
    simpa [prefixWord, tailWord_4685685, baseEnd_4685685] using wordTrace_append hprefix tailTrace_4685685
  have hstable : (prefixWord ++ tailWord_4685685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685685).length < 2 ^ (prefixWord ++ tailWord_4685685).sum := by decide
  have hdescent : baseEnd_4685685 < baseStart_4685685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685749 : List Nat := [1, 3, 3, 2, 1, 3, 1, 4, 1, 1, 3]
def baseStart_4685749 : Nat := 118140960795 + 4685749 * 2 ^ 59
def prefixEnd_4685749 : Nat := 4983230072969 + 3 ^ 40 * 4685749 * 2
def baseEnd_4685749 : Nat := 2406041463324492719188139

theorem tailTrace_4685749 : CollatzResearch.WordTrace tailWord_4685749 prefixEnd_4685749 2406041463324492719188139 := by
  unfold tailWord_4685749
  simp only [CollatzResearch.WordTrace]
  refine ⟨170903306301339110062180301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113935537534226073374786867 170903306301339110062180301)
  ·
    refine ⟨64088739863002166273317613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170903306301339110062180301 64088739863002166273317613)
    ·
      refine ⟨24033277448625812352494105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64088739863002166273317613 24033277448625812352494105)
      ·
        refine ⟨18024958086469359264370579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24033277448625812352494105 18024958086469359264370579)
        ·
          refine ⟨27037437129704038896555869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18024958086469359264370579 27037437129704038896555869)
          ·
            refine ⟨10139038923639014586208451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27037437129704038896555869 10139038923639014586208451)
            ·
              refine ⟨15208558385458521879312677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10139038923639014586208451 15208558385458521879312677)
              ·
                refine ⟨2851604697273472852371127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15208558385458521879312677 2851604697273472852371127)
                ·
                  refine ⟨4277407045910209278556691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2851604697273472852371127 4277407045910209278556691)
                  ·
                    refine ⟨6416110568865313917835037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4277407045910209278556691 6416110568865313917835037)
                    ·
                      refine ⟨2406041463324492719188139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6416110568865313917835037 2406041463324492719188139)
                      ·
                        rfl

theorem cell23_4685749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_4685749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685749 prefixEnd_4685749 := by exact prefixLift 4685749
  have htrace : WordTrace (prefixWord ++ tailWord_4685749) baseStart_4685749 baseEnd_4685749 := by
    simpa [prefixWord, tailWord_4685749, baseEnd_4685749] using wordTrace_append hprefix tailTrace_4685749
  have hstable : (prefixWord ++ tailWord_4685749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685749).length < 2 ^ (prefixWord ++ tailWord_4685749).sum := by decide
  have hdescent : baseEnd_4685749 < baseStart_4685749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685772 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 5, 2, 2]
def baseStart_4685772 : Nat := 118140960795 + 4685772 * 2 ^ 59
def prefixEnd_4685772 : Nat := 4983230072969 + 3 ^ 40 * 4685772 * 2
def baseEnd_4685772 : Nat := 2406053273379546129200533

theorem tailTrace_4685772 : CollatzResearch.WordTrace tailWord_4685772 prefixEnd_4685772 2406053273379546129200533 := by
  unfold tailWord_4685772
  simp only [CollatzResearch.WordTrace]
  refine ⟨85452072590127892495133785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113936096786837189993511713 85452072590127892495133785)
  ·
    refine ⟨64089054442595919371350339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85452072590127892495133785 64089054442595919371350339)
    ·
      refine ⟨96133581663893879057025509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64089054442595919371350339 96133581663893879057025509)
      ·
        refine ⟨18025046561980102323192283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96133581663893879057025509 18025046561980102323192283)
        ·
          refine ⟨27037569842970153484788425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18025046561980102323192283 27037569842970153484788425)
          ·
            refine ⟨20278177382227615113591319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27037569842970153484788425 20278177382227615113591319)
            ·
              refine ⟨30417266073341422670386979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20278177382227615113591319 30417266073341422670386979)
              ·
                refine ⟨45625899110012134005580469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30417266073341422670386979 45625899110012134005580469)
                ·
                  refine ⟨4277428041563637563023169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45625899110012134005580469 4277428041563637563023169)
                  ·
                    refine ⟨3208071031172728172267377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4277428041563637563023169 3208071031172728172267377)
                    ·
                      refine ⟨2406053273379546129200533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3208071031172728172267377 2406053273379546129200533)
                      ·
                        rfl

theorem cell23_4685772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_4685772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685772 prefixEnd_4685772 := by exact prefixLift 4685772
  have htrace : WordTrace (prefixWord ++ tailWord_4685772) baseStart_4685772 baseEnd_4685772 := by
    simpa [prefixWord, tailWord_4685772, baseEnd_4685772] using wordTrace_append hprefix tailTrace_4685772
  have hstable : (prefixWord ++ tailWord_4685772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685772).length < 2 ^ (prefixWord ++ tailWord_4685772).sum := by decide
  have hdescent : baseEnd_4685772 < baseStart_4685772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685775 : List Nat := [1, 1, 2, 1, 1, 5, 2, 4, 1, 2, 3]
def baseStart_4685775 : Nat := 118140960795 + 4685775 * 2 ^ 59
def prefixEnd_4685775 : Nat := 4983230072969 + 3 ^ 40 * 4685775 * 2
def baseEnd_4685775 : Nat := 2406054813821509617463019

theorem tailTrace_4685775 : CollatzResearch.WordTrace tailWord_4685775 prefixEnd_4685775 2406054813821509617463019 := by
  unfold tailWord_4685775
  simp only [CollatzResearch.WordTrace]
  refine ⟨170904254599244916502626779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113936169732829944335084519 170904254599244916502626779)
  ·
    refine ⟨256356381898867374753940169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170904254599244916502626779 256356381898867374753940169)
    ·
      refine ⟨192267286424150531065455127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256356381898867374753940169 192267286424150531065455127)
      ·
        refine ⟨288400929636225796598182691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192267286424150531065455127 288400929636225796598182691)
        ·
          refine ⟨432601394454338694897274037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288400929636225796598182691 432601394454338694897274037)
          ·
            refine ⟨40556380730094252646619441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 432601394454338694897274037 40556380730094252646619441)
            ·
              refine ⟨30417285547570689484964581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40556380730094252646619441 30417285547570689484964581)
              ·
                refine ⟨5703241040169504278430859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30417285547570689484964581 5703241040169504278430859)
                ·
                  refine ⟨8554861560254256417646289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5703241040169504278430859 8554861560254256417646289)
                  ·
                    refine ⟨6416146170190692313234717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8554861560254256417646289 6416146170190692313234717)
                    ·
                      refine ⟨2406054813821509617463019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6416146170190692313234717 2406054813821509617463019)
                      ·
                        rfl

theorem cell23_4685775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 2, 3].length) (baseStart_4685775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685775 prefixEnd_4685775 := by exact prefixLift 4685775
  have htrace : WordTrace (prefixWord ++ tailWord_4685775) baseStart_4685775 baseEnd_4685775 := by
    simpa [prefixWord, tailWord_4685775, baseEnd_4685775] using wordTrace_append hprefix tailTrace_4685775
  have hstable : (prefixWord ++ tailWord_4685775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685775).length < 2 ^ (prefixWord ++ tailWord_4685775).sum := by decide
  have hdescent : baseEnd_4685775 < baseStart_4685775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685799 : List Nat := [1, 1, 5, 2, 3, 2, 1, 2, 2, 4]
def baseStart_4685799 : Nat := 118140960795 + 4685799 * 2 ^ 59
def prefixEnd_4685799 : Nat := 4983230072969 + 3 ^ 40 * 4685799 * 2
def baseEnd_4685799 : Nat := 802022379119072507854303

theorem tailTrace_4685799 : CollatzResearch.WordTrace tailWord_4685799 prefixEnd_4685799 802022379119072507854303 := by
  unfold tailWord_4685799
  simp only [CollatzResearch.WordTrace]
  refine ⟨170905129951157968601500451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113936753300771979067666967 170905129951157968601500451)
  ·
    refine ⟨256357694926736952902250677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170905129951157968601500451 256357694926736952902250677)
    ·
      refine ⟨24033533899381589334586001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 256357694926736952902250677 24033533899381589334586001)
      ·
        refine ⟨18025150424536192000939501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24033533899381589334586001 18025150424536192000939501)
        ·
          refine ⟨6759431409201072000352313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18025150424536192000939501 6759431409201072000352313)
          ·
            refine ⟨5069573556900804000264235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6759431409201072000352313 5069573556900804000264235)
            ·
              refine ⟨7604360335351206000396353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5069573556900804000264235 7604360335351206000396353)
              ·
                refine ⟨5703270251513404500297265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7604360335351206000396353 5703270251513404500297265)
                ·
                  refine ⟨4277452688635053375222949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5703270251513404500297265 4277452688635053375222949)
                  ·
                    refine ⟨802022379119072507854303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4277452688635053375222949 802022379119072507854303)
                    ·
                      rfl

theorem cell23_4685799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_4685799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685799 prefixEnd_4685799 := by exact prefixLift 4685799
  have htrace : WordTrace (prefixWord ++ tailWord_4685799) baseStart_4685799 baseEnd_4685799 := by
    simpa [prefixWord, tailWord_4685799, baseEnd_4685799] using wordTrace_append hprefix tailTrace_4685799
  have hstable : (prefixWord ++ tailWord_4685799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685799).length < 2 ^ (prefixWord ++ tailWord_4685799).sum := by decide
  have hdescent : baseEnd_4685799 < baseStart_4685799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685806 : List Nat := [4, 1, 2, 1, 3, 1, 2, 4, 1, 2, 2]
def baseStart_4685806 : Nat := 118140960795 + 4685806 * 2 ^ 59
def prefixEnd_4685806 : Nat := 4983230072969 + 3 ^ 40 * 4685806 * 2
def baseEnd_4685806 : Nat := 2406070731721798996175377

theorem tailTrace_4685806 : CollatzResearch.WordTrace tailWord_4685806 prefixEnd_4685806 2406070731721798996175377 := by
  unfold tailWord_4685806
  simp only [CollatzResearch.WordTrace]
  refine ⟨21363173157766576099625659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113936923508088405864670181 21363173157766576099625659)
  ·
    refine ⟨32044759736649864149438489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21363173157766576099625659 32044759736649864149438489)
    ·
      refine ⟨24033569802487398112078867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32044759736649864149438489 24033569802487398112078867)
      ·
        refine ⟨36050354703731097168118301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24033569802487398112078867 36050354703731097168118301)
        ·
          refine ⟨13518883013899161438044363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36050354703731097168118301 13518883013899161438044363)
          ·
            refine ⟨20278324520848742157066545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13518883013899161438044363 20278324520848742157066545)
            ·
              refine ⟨15208743390636556617799909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20278324520848742157066545 15208743390636556617799909)
              ·
                refine ⟨2851639385744354365837483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15208743390636556617799909 2851639385744354365837483)
                ·
                  refine ⟨4277459078616531548756225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2851639385744354365837483 4277459078616531548756225)
                  ·
                    refine ⟨3208094308962398661567169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4277459078616531548756225 3208094308962398661567169)
                    ·
                      refine ⟨2406070731721798996175377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3208094308962398661567169 2406070731721798996175377)
                      ·
                        rfl

theorem cell23_4685806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_4685806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685806 prefixEnd_4685806 := by exact prefixLift 4685806
  have htrace : WordTrace (prefixWord ++ tailWord_4685806) baseStart_4685806 baseEnd_4685806 := by
    simpa [prefixWord, tailWord_4685806, baseEnd_4685806] using wordTrace_append hprefix tailTrace_4685806
  have hstable : (prefixWord ++ tailWord_4685806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685806).length < 2 ^ (prefixWord ++ tailWord_4685806).sum := by decide
  have hdescent : baseEnd_4685806 < baseStart_4685806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685868 : List Nat := [2, 2, 1, 1, 1, 2, 2, 5, 7]
def baseStart_4685868 : Nat := 118140960795 + 4685868 * 2 ^ 59
def prefixEnd_4685868 : Nat := 4983230072969 + 3 ^ 40 * 4685868 * 2
def baseEnd_4685868 : Nat := 267344729724708639288899

theorem tailTrace_4685868 : CollatzResearch.WordTrace tailWord_4685868 prefixEnd_4685868 267344729724708639288899 := by
  unfold tailWord_4685868
  simp only [CollatzResearch.WordTrace]
  refine ⟨85453823293953996692881129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113938431058605328923841505 85453823293953996692881129)
  ·
    refine ⟨64090367470465497519660847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85453823293953996692881129 64090367470465497519660847)
    ·
      refine ⟨96135551205698246279491271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64090367470465497519660847 96135551205698246279491271)
      ·
        refine ⟨144203326808547369419236907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96135551205698246279491271 144203326808547369419236907)
        ·
          refine ⟨216304990212821054128855361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144203326808547369419236907 216304990212821054128855361)
          ·
            refine ⟨162228742659615790596641521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216304990212821054128855361 162228742659615790596641521)
            ·
              refine ⟨121671556994711842947481141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162228742659615790596641521 121671556994711842947481141)
              ·
                refine ⟨11406708468254235276326357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121671556994711842947481141 11406708468254235276326357)
                ·
                  refine ⟨267344729724708639288899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11406708468254235276326357 267344729724708639288899)
                  ·
                    rfl

theorem cell23_4685868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 7].length) (baseStart_4685868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685868 prefixEnd_4685868 := by exact prefixLift 4685868
  have htrace : WordTrace (prefixWord ++ tailWord_4685868) baseStart_4685868 baseEnd_4685868 := by
    simpa [prefixWord, tailWord_4685868, baseEnd_4685868] using wordTrace_append hprefix tailTrace_4685868
  have hstable : (prefixWord ++ tailWord_4685868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685868).length < 2 ^ (prefixWord ++ tailWord_4685868).sum := by decide
  have hdescent : baseEnd_4685868 < baseStart_4685868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4685925 : List Nat := [1, 3, 1, 3, 2, 2, 2, 1, 1, 2, 5]
def baseStart_4685925 : Nat := 118140960795 + 4685925 * 2 ^ 59
def prefixEnd_4685925 : Nat := 4983230072969 + 3 ^ 40 * 4685925 * 2
def baseEnd_4685925 : Nat := 2406131835919684030587329

theorem tailTrace_4685925 : CollatzResearch.WordTrace tailWord_4685925 prefixEnd_4685925 2406131835919684030587329 := by
  unfold tailWord_4685925
  simp only [CollatzResearch.WordTrace]
  refine ⟨170909725548701492120587229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113939817032467661413724819 170909725548701492120587229)
  ·
    refine ⟨64091147080763059545220211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170909725548701492120587229 64091147080763059545220211)
    ·
      refine ⟨96136720621144589317830317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64091147080763059545220211 96136720621144589317830317)
      ·
        refine ⟨36051270232929220994186369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96136720621144589317830317 36051270232929220994186369)
        ·
          refine ⟨27038452674696915745639777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36051270232929220994186369 27038452674696915745639777)
          ·
            refine ⟨20278839506022686809229833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27038452674696915745639777 20278839506022686809229833)
            ·
              refine ⟨15209129629517015106922375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20278839506022686809229833 15209129629517015106922375)
              ·
                refine ⟨22813694444275522660383563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15209129629517015106922375 22813694444275522660383563)
                ·
                  refine ⟨34220541666413283990575345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22813694444275522660383563 34220541666413283990575345)
                  ·
                    refine ⟨25665406249809962992931509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34220541666413283990575345 25665406249809962992931509)
                    ·
                      refine ⟨2406131835919684030587329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25665406249809962992931509 2406131835919684030587329)
                      ·
                        rfl

theorem cell23_4685925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_4685925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4685925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4685925 prefixEnd_4685925 := by exact prefixLift 4685925
  have htrace : WordTrace (prefixWord ++ tailWord_4685925) baseStart_4685925 baseEnd_4685925 := by
    simpa [prefixWord, tailWord_4685925, baseEnd_4685925] using wordTrace_append hprefix tailTrace_4685925
  have hstable : (prefixWord ++ tailWord_4685925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4685925).length < 2 ^ (prefixWord ++ tailWord_4685925).sum := by decide
  have hdescent : baseEnd_4685925 < baseStart_4685925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4685925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686059 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 5, 2, 2]
def baseStart_4686059 : Nat := 118140960795 + 4686059 * 2 ^ 59
def prefixEnd_4686059 : Nat := 4983230072969 + 3 ^ 40 * 4686059 * 2
def baseEnd_4686059 : Nat := 2406200642327386506311713

theorem tailTrace_4686059 : CollatzResearch.WordTrace tailWord_4686059 prefixEnd_4686059 2406200642327386506311713 := by
  unfold tailWord_4686059
  simp only [CollatzResearch.WordTrace]
  refine ⟨170914612930216033005965231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113943075286810688670643487 170914612930216033005965231)
  ·
    refine ⟨256371919395324049508947847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170914612930216033005965231 256371919395324049508947847)
    ·
      refine ⟨384557879092986074263421771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256371919395324049508947847 384557879092986074263421771)
      ·
        refine ⟨576836818639479111395132657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384557879092986074263421771 576836818639479111395132657)
        ·
          refine ⟨432627613979609333546349493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 576836818639479111395132657 432627613979609333546349493)
          ·
            refine ⟨40558838810588375019970265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 432627613979609333546349493 40558838810588375019970265)
            ·
              refine ⟨30419129107941281264977699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40558838810588375019970265 30419129107941281264977699)
              ·
                refine ⟨45628693661911921897466549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30419129107941281264977699 45628693661911921897466549)
                ·
                  refine ⟨4277690030804242677887489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45628693661911921897466549 4277690030804242677887489)
                  ·
                    refine ⟨3208267523103182008415617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4277690030804242677887489 3208267523103182008415617)
                    ·
                      refine ⟨2406200642327386506311713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3208267523103182008415617 2406200642327386506311713)
                      ·
                        rfl

theorem cell23_4686059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5, 2, 2].length) (baseStart_4686059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686059 prefixEnd_4686059 := by exact prefixLift 4686059
  have htrace : WordTrace (prefixWord ++ tailWord_4686059) baseStart_4686059 baseEnd_4686059 := by
    simpa [prefixWord, tailWord_4686059, baseEnd_4686059] using wordTrace_append hprefix tailTrace_4686059
  have hstable : (prefixWord ++ tailWord_4686059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686059).length < 2 ^ (prefixWord ++ tailWord_4686059).sum := by decide
  have hdescent : baseEnd_4686059 < baseStart_4686059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686065 : List Nat := [1, 2, 2, 2, 2, 1, 4, 9]
def baseStart_4686065 : Nat := 118140960795 + 4686065 * 2 ^ 59
def prefixEnd_4686065 : Nat := 4983230072969 + 3 ^ 40 * 4686065 * 2
def baseEnd_4686065 : Nat := 89118656415233832697655

theorem tailTrace_4686065 : CollatzResearch.WordTrace tailWord_4686065 prefixEnd_4686065 89118656415233832697655 := by
  unfold tailWord_4686065
  simp only [CollatzResearch.WordTrace]
  refine ⟨170914831768194296030683649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113943221178796197353789099 170914831768194296030683649)
  ·
    refine ⟨128186123826145722023012737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170914831768194296030683649 128186123826145722023012737)
    ·
      refine ⟨96139592869609291517259553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128186123826145722023012737 96139592869609291517259553)
      ·
        refine ⟨72104694652206968637944665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96139592869609291517259553 72104694652206968637944665)
        ·
          refine ⟨54078520989155226478458499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72104694652206968637944665 54078520989155226478458499)
          ·
            refine ⟨81117781483732839717687749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54078520989155226478458499 81117781483732839717687749)
            ·
              refine ⟨15209584028199907447066453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81117781483732839717687749 15209584028199907447066453)
              ·
                refine ⟨89118656415233832697655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15209584028199907447066453 89118656415233832697655)
                ·
                  rfl

theorem cell23_4686065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 9].length) (baseStart_4686065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686065 prefixEnd_4686065 := by exact prefixLift 4686065
  have htrace : WordTrace (prefixWord ++ tailWord_4686065) baseStart_4686065 baseEnd_4686065 := by
    simpa [prefixWord, tailWord_4686065, baseEnd_4686065] using wordTrace_append hprefix tailTrace_4686065
  have hstable : (prefixWord ++ tailWord_4686065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686065).length < 2 ^ (prefixWord ++ tailWord_4686065).sum := by decide
  have hdescent : baseEnd_4686065 < baseStart_4686065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686076 : List Nat := [2, 2, 2, 1, 4, 2, 3, 1, 1, 1, 4]
def baseStart_4686076 : Nat := 118140960795 + 4686076 * 2 ^ 59
def prefixEnd_4686076 : Nat := 4983230072969 + 3 ^ 40 * 4686076 * 2
def baseEnd_4686076 : Nat := 2406209371498512939799135

theorem tailTrace_4686076 : CollatzResearch.WordTrace tailWord_4686076 prefixEnd_4686076 2406209371498512939799135 := by
  unfold tailWord_4686076
  simp only [CollatzResearch.WordTrace]
  refine ⟨85457616485577222454667041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113943488647436296606222721 85457616485577222454667041)
  ·
    refine ⟨64093212364182916841000281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85457616485577222454667041 64093212364182916841000281)
    ·
      refine ⟨48069909273137187630750211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64093212364182916841000281 48069909273137187630750211)
      ·
        refine ⟨72104863909705781446125317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48069909273137187630750211 72104863909705781446125317)
        ·
          refine ⟨13519661983069834021148497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72104863909705781446125317 13519661983069834021148497)
          ·
            refine ⟨10139746487302375515861373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13519661983069834021148497 10139746487302375515861373)
            ·
              refine ⟨3802404932738390818448015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10139746487302375515861373 3802404932738390818448015)
              ·
                refine ⟨5703607399107586227672023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3802404932738390818448015 5703607399107586227672023)
                ·
                  refine ⟨8555411098661379341508035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5703607399107586227672023 8555411098661379341508035)
                  ·
                    refine ⟨12833116647992069012262053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8555411098661379341508035 12833116647992069012262053)
                    ·
                      refine ⟨2406209371498512939799135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12833116647992069012262053 2406209371498512939799135)
                      ·
                        rfl

theorem cell23_4686076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 1, 1, 4].length) (baseStart_4686076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686076 prefixEnd_4686076 := by exact prefixLift 4686076
  have htrace : WordTrace (prefixWord ++ tailWord_4686076) baseStart_4686076 baseEnd_4686076 := by
    simpa [prefixWord, tailWord_4686076, baseEnd_4686076] using wordTrace_append hprefix tailTrace_4686076
  have hstable : (prefixWord ++ tailWord_4686076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686076).length < 2 ^ (prefixWord ++ tailWord_4686076).sum := by decide
  have hdescent : baseEnd_4686076 < baseStart_4686076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686082 : List Nat := [3, 4, 1, 1, 2, 12]
def baseStart_4686082 : Nat := 118140960795 + 4686082 * 2 ^ 59
def prefixEnd_4686082 : Nat := 4983230072969 + 3 ^ 40 * 4686082 * 2
def baseEnd_4686082 : Nat := 9902108857540905005449

theorem tailTrace_4686082 : CollatzResearch.WordTrace tailWord_4686082 prefixEnd_4686082 9902108857540905005449 := by
  unfold tailWord_4686082
  simp only [CollatzResearch.WordTrace]
  refine ⟨42728862952283176983513125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113943634539421805289368333 42728862952283176983513125)
  ·
    refine ⟨8011661803553095684408711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42728862952283176983513125 8011661803553095684408711)
    ·
      refine ⟨12017492705329643526613067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8011661803553095684408711 12017492705329643526613067)
      ·
        refine ⟨18026239057994465289919601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12017492705329643526613067 18026239057994465289919601)
        ·
          refine ⟨13519679293495848967439701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18026239057994465289919601 13519679293495848967439701)
          ·
            refine ⟨9902108857540905005449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 13519679293495848967439701 9902108857540905005449)
            ·
              rfl

theorem cell23_4686082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 12].length) (baseStart_4686082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686082 prefixEnd_4686082 := by exact prefixLift 4686082
  have htrace : WordTrace (prefixWord ++ tailWord_4686082) baseStart_4686082 baseEnd_4686082 := by
    simpa [prefixWord, tailWord_4686082, baseEnd_4686082] using wordTrace_append hprefix tailTrace_4686082
  have hstable : (prefixWord ++ tailWord_4686082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686082).length < 2 ^ (prefixWord ++ tailWord_4686082).sum := by decide
  have hdescent : baseEnd_4686082 < baseStart_4686082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686085 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 2, 2, 6]
def baseStart_4686085 : Nat := 118140960795 + 4686085 * 2 ^ 59
def prefixEnd_4686085 : Nat := 4983230072969 + 3 ^ 40 * 4686085 * 2
def baseEnd_4686085 : Nat := 2406213992824403404586593

theorem tailTrace_4686085 : CollatzResearch.WordTrace tailWord_4686085 prefixEnd_4686085 2406213992824403404586593 := by
  unfold tailWord_4686085
  simp only [CollatzResearch.WordTrace]
  refine ⟨170915561228121839446411709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113943707485414559630941139 170915561228121839446411709)
  ·
    refine ⟨64093335460545689792404391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170915561228121839446411709 64093335460545689792404391)
    ·
      refine ⟨96140003190818534688606587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64093335460545689792404391 96140003190818534688606587)
      ·
        refine ⟨144210004786227802032909881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96140003190818534688606587 144210004786227802032909881)
        ·
          refine ⟨108157503589670851524682411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144210004786227802032909881 108157503589670851524682411)
          ·
            refine ⟨162236255384506277287023617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108157503589670851524682411 162236255384506277287023617)
            ·
              refine ⟨121677191538379707965267713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162236255384506277287023617 121677191538379707965267713)
              ·
                refine ⟨91257893653784780973950785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121677191538379707965267713 91257893653784780973950785)
                ·
                  refine ⟨68443420240338585730463089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91257893653784780973950785 68443420240338585730463089)
                  ·
                    refine ⟨51332565180253939297847317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68443420240338585730463089 51332565180253939297847317)
                    ·
                      refine ⟨2406213992824403404586593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51332565180253939297847317 2406213992824403404586593)
                      ·
                        rfl

theorem cell23_4686085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_4686085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686085 prefixEnd_4686085 := by exact prefixLift 4686085
  have htrace : WordTrace (prefixWord ++ tailWord_4686085) baseStart_4686085 baseEnd_4686085 := by
    simpa [prefixWord, tailWord_4686085, baseEnd_4686085] using wordTrace_append hprefix tailTrace_4686085
  have hstable : (prefixWord ++ tailWord_4686085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686085).length < 2 ^ (prefixWord ++ tailWord_4686085).sum := by decide
  have hdescent : baseEnd_4686085 < baseStart_4686085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686087 : List Nat := [1, 1, 4, 5, 1, 2, 2, 2, 1, 1, 3]
def baseStart_4686087 : Nat := 118140960795 + 4686087 * 2 ^ 59
def prefixEnd_4686087 : Nat := 4983230072969 + 3 ^ 40 * 4686087 * 2
def baseEnd_4686087 : Nat := 2406215019785712396761585

theorem tailTrace_4686087 : CollatzResearch.WordTrace tailWord_4686087 prefixEnd_4686087 2406215019785712396761585 := by
  unfold tailWord_4686087
  simp only [CollatzResearch.WordTrace]
  refine ⟨170915634174114593787984515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113943756116076395858656343 170915634174114593787984515)
  ·
    refine ⟨256373451261171890681976773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170915634174114593787984515 256373451261171890681976773)
    ·
      refine ⟨48070022111469729502870645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 256373451261171890681976773 48070022111469729502870645)
      ·
        refine ⟨4506564572950287140894123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48070022111469729502870645 4506564572950287140894123)
        ·
          refine ⟨6759846859425430711341185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4506564572950287140894123 6759846859425430711341185)
          ·
            refine ⟨5069885144569073033505889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6759846859425430711341185 5069885144569073033505889)
            ·
              refine ⟨3802413858426804775129417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5069885144569073033505889 3802413858426804775129417)
              ·
                refine ⟨2851810393820103581347063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3802413858426804775129417 2851810393820103581347063)
                ·
                  refine ⟨4277715590730155372020595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2851810393820103581347063 4277715590730155372020595)
                  ·
                    refine ⟨6416573386095233058030893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4277715590730155372020595 6416573386095233058030893)
                    ·
                      refine ⟨2406215019785712396761585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6416573386095233058030893 2406215019785712396761585)
                      ·
                        rfl

theorem cell23_4686087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_4686087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686087 prefixEnd_4686087 := by exact prefixLift 4686087
  have htrace : WordTrace (prefixWord ++ tailWord_4686087) baseStart_4686087 baseEnd_4686087 := by
    simpa [prefixWord, tailWord_4686087, baseEnd_4686087] using wordTrace_append hprefix tailTrace_4686087
  have hstable : (prefixWord ++ tailWord_4686087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686087).length < 2 ^ (prefixWord ++ tailWord_4686087).sum := by decide
  have hdescent : baseEnd_4686087 < baseStart_4686087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686092 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 3, 3, 3]
def baseStart_4686092 : Nat := 118140960795 + 4686092 * 2 ^ 59
def prefixEnd_4686092 : Nat := 4983230072969 + 3 ^ 40 * 4686092 * 2
def baseEnd_4686092 : Nat := 2406217587188984877199061

theorem tailTrace_4686092 : CollatzResearch.WordTrace tailWord_4686092 prefixEnd_4686092 2406217587188984877199061 := by
  unfold tailWord_4686092
  simp only [CollatzResearch.WordTrace]
  refine ⟨85457908269548239820958265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113943877692730986427944353 85457908269548239820958265)
  ·
    refine ⟨64093431202161179865718699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85457908269548239820958265 64093431202161179865718699)
    ·
      refine ⟨96140146803241769798578049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64093431202161179865718699 96140146803241769798578049)
      ·
        refine ⟨72105110102431327348933537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96140146803241769798578049 72105110102431327348933537)
        ·
          refine ⟨54078832576823495511700153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72105110102431327348933537 54078832576823495511700153)
          ·
            refine ⟨40559124432617621633775115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54078832576823495511700153 40559124432617621633775115)
            ·
              refine ⟨60838686648926432450662673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40559124432617621633775115 60838686648926432450662673)
              ·
                refine ⟨45629014986694824337997005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60838686648926432450662673 45629014986694824337997005)
                ·
                  refine ⟨17110880620010559126748877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45629014986694824337997005 17110880620010559126748877)
                  ·
                    refine ⟨6416580232503959672530829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17110880620010559126748877 6416580232503959672530829)
                    ·
                      refine ⟨2406217587188984877199061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6416580232503959672530829 2406217587188984877199061)
                      ·
                        rfl

theorem cell23_4686092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_4686092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686092 prefixEnd_4686092 := by exact prefixLift 4686092
  have htrace : WordTrace (prefixWord ++ tailWord_4686092) baseStart_4686092 baseEnd_4686092 := by
    simpa [prefixWord, tailWord_4686092, baseEnd_4686092] using wordTrace_append hprefix tailTrace_4686092
  have hstable : (prefixWord ++ tailWord_4686092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686092).length < 2 ^ (prefixWord ++ tailWord_4686092).sum := by decide
  have hdescent : baseEnd_4686092 < baseStart_4686092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686110 : List Nat := [4, 3, 2, 1, 1, 2, 1, 2, 3, 2, 2]
def baseStart_4686110 : Nat := 118140960795 + 4686110 * 2 ^ 59
def prefixEnd_4686110 : Nat := 4983230072969 + 3 ^ 40 * 4686110 * 2
def baseEnd_4686110 : Nat := 2406226829840765806773979

theorem tailTrace_4686110 : CollatzResearch.WordTrace tailWord_4686110 prefixEnd_4686110 2406226829840765806773979 := by
  unfold tailWord_4686110
  simp only [CollatzResearch.WordTrace]
  refine ⟨21364559131628908589508973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113944315368687512477381189 21364559131628908589508973)
  ·
    refine ⟨8011709674360840721065865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21364559131628908589508973 8011709674360840721065865)
    ·
      refine ⟨6008782255770630540799399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8011709674360840721065865 6008782255770630540799399)
      ·
        refine ⟨9013173383655945811199099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6008782255770630540799399 9013173383655945811199099)
        ·
          refine ⟨13519760075483918716798649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9013173383655945811199099 13519760075483918716798649)
          ·
            refine ⟨10139820056612939037598987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13519760075483918716798649 10139820056612939037598987)
            ·
              refine ⟨15209730084919408556398481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10139820056612939037598987 15209730084919408556398481)
              ·
                refine ⟨11407297563689556417298861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15209730084919408556398481 11407297563689556417298861)
                ·
                  refine ⟨4277736586383583656487073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11407297563689556417298861 4277736586383583656487073)
                  ·
                    refine ⟨3208302439787687742365305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4277736586383583656487073 3208302439787687742365305)
                    ·
                      refine ⟨2406226829840765806773979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3208302439787687742365305 2406226829840765806773979)
                      ·
                        rfl

theorem cell23_4686110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_4686110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686110 prefixEnd_4686110 := by exact prefixLift 4686110
  have htrace : WordTrace (prefixWord ++ tailWord_4686110) baseStart_4686110 baseEnd_4686110 := by
    simpa [prefixWord, tailWord_4686110, baseEnd_4686110] using wordTrace_append hprefix tailTrace_4686110
  have hstable : (prefixWord ++ tailWord_4686110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686110).length < 2 ^ (prefixWord ++ tailWord_4686110).sum := by decide
  have hdescent : baseEnd_4686110 < baseStart_4686110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686130 : List Nat := [3, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3]
def baseStart_4686130 : Nat := 118140960795 + 4686130 * 2 ^ 59
def prefixEnd_4686130 : Nat := 4983230072969 + 3 ^ 40 * 4686130 * 2
def baseEnd_4686130 : Nat := 2406237099453855728523887

theorem tailTrace_4686130 : CollatzResearch.WordTrace tailWord_4686130 prefixEnd_4686130 2406237099453855728523887 := by
  unfold tailWord_4686130
  simp only [CollatzResearch.WordTrace]
  refine ⟨42729300628239703032949961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113944801675305874754533229 42729300628239703032949961)
  ·
    refine ⟨32046975471179777274712471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42729300628239703032949961 32046975471179777274712471)
    ·
      refine ⟨48070463206769665912068707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32046975471179777274712471 48070463206769665912068707)
      ·
        refine ⟨72105694810154498868103061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48070463206769665912068707 72105694810154498868103061)
        ·
          refine ⟨3379954444225992134442331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 72105694810154498868103061 3379954444225992134442331)
          ·
            refine ⟨5069931666338988201663497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3379954444225992134442331 5069931666338988201663497)
            ·
              refine ⟨3802448749754241151247623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5069931666338988201663497 3802448749754241151247623)
              ·
                refine ⟨5703673124631361726871435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3802448749754241151247623 5703673124631361726871435)
                ·
                  refine ⟨8555509686947042590307153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5703673124631361726871435 8555509686947042590307153)
                  ·
                    refine ⟨6416632265210281942730365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8555509686947042590307153 6416632265210281942730365)
                    ·
                      refine ⟨2406237099453855728523887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6416632265210281942730365 2406237099453855728523887)
                      ·
                        rfl

theorem cell23_4686130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3].length) (baseStart_4686130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686130 prefixEnd_4686130 := by exact prefixLift 4686130
  have htrace : WordTrace (prefixWord ++ tailWord_4686130) baseStart_4686130 baseEnd_4686130 := by
    simpa [prefixWord, tailWord_4686130, baseEnd_4686130] using wordTrace_append hprefix tailTrace_4686130
  have hstable : (prefixWord ++ tailWord_4686130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686130).length < 2 ^ (prefixWord ++ tailWord_4686130).sum := by decide
  have hdescent : baseEnd_4686130 < baseStart_4686130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686152 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 1, 6, 3]
def baseStart_4686152 : Nat := 118140960795 + 4686152 * 2 ^ 59
def prefixEnd_4686152 : Nat := 4983230072969 + 3 ^ 40 * 4686152 * 2
def baseEnd_4686152 : Nat := 2406248396028254642448785

theorem tailTrace_4686152 : CollatzResearch.WordTrace tailWord_4686152 prefixEnd_4686152 2406248396028254642448785 := by
  unfold tailWord_4686152
  simp only [CollatzResearch.WordTrace]
  refine ⟨85459002459439554944550355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113945336612586073259400473 85459002459439554944550355)
  ·
    refine ⟨128188503689159332416825533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85459002459439554944550355 128188503689159332416825533)
    ·
      refine ⟨48070688883434749656309575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128188503689159332416825533 48070688883434749656309575)
      ·
        refine ⟨72106033325152124484464363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48070688883434749656309575 72106033325152124484464363)
        ·
          refine ⟨108159049987728186726696545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72106033325152124484464363 108159049987728186726696545)
          ·
            refine ⟨81119287490796140045022409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108159049987728186726696545 81119287490796140045022409)
            ·
              refine ⟨60839465618097105033766807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81119287490796140045022409 60839465618097105033766807)
              ·
                refine ⟨91259198427145657550650211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60839465618097105033766807 91259198427145657550650211)
                ·
                  refine ⟨136888797640718486325975317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91259198427145657550650211 136888797640718486325975317)
                  ·
                    refine ⟨6416662389408679046530093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 136888797640718486325975317 6416662389408679046530093)
                    ·
                      refine ⟨2406248396028254642448785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6416662389408679046530093 2406248396028254642448785)
                      ·
                        rfl

theorem cell23_4686152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_4686152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686152 prefixEnd_4686152 := by exact prefixLift 4686152
  have htrace : WordTrace (prefixWord ++ tailWord_4686152) baseStart_4686152 baseEnd_4686152 := by
    simpa [prefixWord, tailWord_4686152, baseEnd_4686152] using wordTrace_append hprefix tailTrace_4686152
  have hstable : (prefixWord ++ tailWord_4686152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686152).length < 2 ^ (prefixWord ++ tailWord_4686152).sum := by decide
  have hdescent : baseEnd_4686152 < baseStart_4686152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686252 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 6]
def baseStart_4686252 : Nat := 118140960795 + 4686252 * 2 ^ 59
def prefixEnd_4686252 : Nat := 4983230072969 + 3 ^ 40 * 4686252 * 2
def baseEnd_4686252 : Nat := 2406299744093704251198325

theorem tailTrace_4686252 : CollatzResearch.WordTrace tailWord_4686252 prefixEnd_4686252 2406299744093704251198325 := by
  unfold tailWord_4686252
  simp only [CollatzResearch.WordTrace]
  refine ⟨85460826109258413483870505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113947768145677884645160673 85460826109258413483870505)
  ·
    refine ⟨64095619581943810112902879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85460826109258413483870505 64095619581943810112902879)
    ·
      refine ⟨96143429372915715169354319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64095619581943810112902879 96143429372915715169354319)
      ·
        refine ⟨144215144059373572754031479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96143429372915715169354319 144215144059373572754031479)
        ·
          refine ⟨216322716089060359131047219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144215144059373572754031479 216322716089060359131047219)
          ·
            refine ⟨324484074133590538696570829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216322716089060359131047219 324484074133590538696570829)
            ·
              refine ⟨121681527800096452011214061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 324484074133590538696570829 121681527800096452011214061)
              ·
                refine ⟨45630572925036169504205273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121681527800096452011214061 45630572925036169504205273)
                ·
                  refine ⟨34222929693777127128153955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45630572925036169504205273 34222929693777127128153955)
                  ·
                    refine ⟨51334394540665690692230933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34222929693777127128153955 51334394540665690692230933)
                    ·
                      refine ⟨2406299744093704251198325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51334394540665690692230933 2406299744093704251198325)
                      ·
                        rfl

theorem cell23_4686252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_4686252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686252 prefixEnd_4686252 := by exact prefixLift 4686252
  have htrace : WordTrace (prefixWord ++ tailWord_4686252) baseStart_4686252 baseEnd_4686252 := by
    simpa [prefixWord, tailWord_4686252, baseEnd_4686252] using wordTrace_append hprefix tailTrace_4686252
  have hstable : (prefixWord ++ tailWord_4686252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686252).length < 2 ^ (prefixWord ++ tailWord_4686252).sum := by decide
  have hdescent : baseEnd_4686252 < baseStart_4686252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686279 : List Nat := [1, 1, 4, 1, 1, 4, 2, 3, 6]
def baseStart_4686279 : Nat := 118140960795 + 4686279 * 2 ^ 59
def prefixEnd_4686279 : Nat := 4983230072969 + 3 ^ 40 * 4686279 * 2
def baseEnd_4686279 : Nat := 267368178674597293951189

theorem tailTrace_4686279 : CollatzResearch.WordTrace tailWord_4686279 prefixEnd_4686279 267368178674597293951189 := by
  unfold tailWord_4686279
  simp only [CollatzResearch.WordTrace]
  refine ⟨170922636989419010578973891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113948424659612673719315927 170922636989419010578973891)
  ·
    refine ⟨256383955484128515868460837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170922636989419010578973891 256383955484128515868460837)
    ·
      refine ⟨48071991653274096725336407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 256383955484128515868460837 48071991653274096725336407)
      ·
        refine ⟨72107987479911145088004611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48071991653274096725336407 72107987479911145088004611)
        ·
          refine ⟨108161981219866717632006917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72107987479911145088004611 108161981219866717632006917)
          ·
            refine ⟨20280371478725009556001297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108161981219866717632006917 20280371478725009556001297)
            ·
              refine ⟨15210278609043757167000973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20280371478725009556001297 15210278609043757167000973)
              ·
                refine ⟨5703854478391408937625365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15210278609043757167000973 5703854478391408937625365)
                ·
                  refine ⟨267368178674597293951189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5703854478391408937625365 267368178674597293951189)
                  ·
                    rfl

theorem cell23_4686279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 6].length) (baseStart_4686279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686279 prefixEnd_4686279 := by exact prefixLift 4686279
  have htrace : WordTrace (prefixWord ++ tailWord_4686279) baseStart_4686279 baseEnd_4686279 := by
    simpa [prefixWord, tailWord_4686279, baseEnd_4686279] using wordTrace_append hprefix tailTrace_4686279
  have hstable : (prefixWord ++ tailWord_4686279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686279).length < 2 ^ (prefixWord ++ tailWord_4686279).sum := by decide
  have hdescent : baseEnd_4686279 < baseStart_4686279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686290 : List Nat := [3, 2, 2, 4, 1, 2, 1, 1, 2, 1, 4]
def baseStart_4686290 : Nat := 118140960795 + 4686290 * 2 ^ 59
def prefixEnd_4686290 : Nat := 4983230072969 + 3 ^ 40 * 4686290 * 2
def baseEnd_4686290 : Nat := 2406319256358575102523151

theorem tailTrace_4686290 : CollatzResearch.WordTrace tailWord_4686290 prefixEnd_4686290 2406319256358575102523151 := by
  unfold tailWord_4686290
  simp only [CollatzResearch.WordTrace]
  refine ⟨42730759548094789864406081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113948692128252772971749549 42730759548094789864406081)
  ·
    refine ⟨32048069661071092398304561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42730759548094789864406081 32048069661071092398304561)
    ·
      refine ⟨24036052245803319298728421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32048069661071092398304561 24036052245803319298728421)
      ·
        refine ⟨4506759796088122368511579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24036052245803319298728421 4506759796088122368511579)
        ·
          refine ⟨6760139694132183552767369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4506759796088122368511579 6760139694132183552767369)
          ·
            refine ⟨5070104770599137664575527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6760139694132183552767369 5070104770599137664575527)
            ·
              refine ⟨7605157155898706496863291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5070104770599137664575527 7605157155898706496863291)
              ·
                refine ⟨11407735733848059745294937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7605157155898706496863291 11407735733848059745294937)
                ·
                  refine ⟨8555801800386044808971203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11407735733848059745294937 8555801800386044808971203)
                  ·
                    refine ⟨12833702700579067213456805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8555801800386044808971203 12833702700579067213456805)
                    ·
                      refine ⟨2406319256358575102523151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12833702700579067213456805 2406319256358575102523151)
                      ·
                        rfl

theorem cell23_4686290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_4686290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686290 prefixEnd_4686290 := by exact prefixLift 4686290
  have htrace : WordTrace (prefixWord ++ tailWord_4686290) baseStart_4686290 baseEnd_4686290 := by
    simpa [prefixWord, tailWord_4686290, baseEnd_4686290] using wordTrace_append hprefix tailTrace_4686290
  have hstable : (prefixWord ++ tailWord_4686290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686290).length < 2 ^ (prefixWord ++ tailWord_4686290).sum := by decide
  have hdescent : baseEnd_4686290 < baseStart_4686290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686293 : List Nat := [1, 3, 2, 3, 1, 4, 1, 1, 2, 2, 3]
def baseStart_4686293 : Nat := 118140960795 + 4686293 * 2 ^ 59
def prefixEnd_4686293 : Nat := 4983230072969 + 3 ^ 40 * 4686293 * 2
def baseEnd_4686293 : Nat := 2406320796800538590785637

theorem tailTrace_4686293 : CollatzResearch.WordTrace tailWord_4686293 prefixEnd_4686293 2406320796800538590785637 := by
  unfold tailWord_4686293
  simp only [CollatzResearch.WordTrace]
  refine ⟨170923147611368290969983533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113948765074245527313322355 170923147611368290969983533)
  ·
    refine ⟨64096180354263109113743825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170923147611368290969983533 64096180354263109113743825)
    ·
      refine ⟨48072135265697331835307869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64096180354263109113743825 48072135265697331835307869)
      ·
        refine ⟨18027050724636499438240451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48072135265697331835307869 18027050724636499438240451)
        ·
          refine ⟨27040576086954749157360677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18027050724636499438240451 27040576086954749157360677)
          ·
            refine ⟨5070108016304015467005127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27040576086954749157360677 5070108016304015467005127)
            ·
              refine ⟨7605162024456023200507691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5070108016304015467005127 7605162024456023200507691)
              ·
                refine ⟨11407743036684034800761537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7605162024456023200507691 11407743036684034800761537)
                ·
                  refine ⟨8555807277513026100571153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11407743036684034800761537 8555807277513026100571153)
                  ·
                    refine ⟨6416855458134769575428365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8555807277513026100571153 6416855458134769575428365)
                    ·
                      refine ⟨2406320796800538590785637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6416855458134769575428365 2406320796800538590785637)
                      ·
                        rfl

theorem cell23_4686293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_4686293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686293 prefixEnd_4686293 := by exact prefixLift 4686293
  have htrace : WordTrace (prefixWord ++ tailWord_4686293) baseStart_4686293 baseEnd_4686293 := by
    simpa [prefixWord, tailWord_4686293, baseEnd_4686293] using wordTrace_append hprefix tailTrace_4686293
  have hstable : (prefixWord ++ tailWord_4686293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686293).length < 2 ^ (prefixWord ++ tailWord_4686293).sum := by decide
  have hdescent : baseEnd_4686293 < baseStart_4686293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686316 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 4, 3, 2]
def baseStart_4686316 : Nat := 118140960795 + 4686316 * 2 ^ 59
def prefixEnd_4686316 : Nat := 4983230072969 + 3 ^ 40 * 4686316 * 2
def baseEnd_4686316 : Nat := 2406332606855592000798031

theorem tailTrace_4686316 : CollatzResearch.WordTrace tailWord_4686316 prefixEnd_4686316 2406332606855592000798031 := by
  unfold tailWord_4686316
  simp only [CollatzResearch.WordTrace]
  refine ⟨85461993245142482949035401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113949324326856643932047201 85461993245142482949035401)
  ·
    refine ⟨64096494933856862211776551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85461993245142482949035401 64096494933856862211776551)
    ·
      refine ⟨96144742400785293317664827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64096494933856862211776551 96144742400785293317664827)
      ·
        refine ⟨144217113601177939976497241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96144742400785293317664827 144217113601177939976497241)
        ·
          refine ⟨108162835200883454982372931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144217113601177939976497241 108162835200883454982372931)
          ·
            refine ⟨162244252801325182473559397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108162835200883454982372931 162244252801325182473559397)
            ·
              refine ⟨30420797400248471713792387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 162244252801325182473559397 30420797400248471713792387)
              ·
                refine ⟨45631196100372707570688581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30420797400248471713792387 45631196100372707570688581)
                ·
                  refine ⟨8555849268819882669504109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45631196100372707570688581 8555849268819882669504109)
                  ·
                    refine ⟨3208443475807456001064041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8555849268819882669504109 3208443475807456001064041)
                    ·
                      refine ⟨2406332606855592000798031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3208443475807456001064041 2406332606855592000798031)
                      ·
                        rfl

theorem cell23_4686316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 3, 2].length) (baseStart_4686316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686316 prefixEnd_4686316 := by exact prefixLift 4686316
  have htrace : WordTrace (prefixWord ++ tailWord_4686316) baseStart_4686316 baseEnd_4686316 := by
    simpa [prefixWord, tailWord_4686316, baseEnd_4686316] using wordTrace_append hprefix tailTrace_4686316
  have hstable : (prefixWord ++ tailWord_4686316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686316).length < 2 ^ (prefixWord ++ tailWord_4686316).sum := by decide
  have hdescent : baseEnd_4686316 < baseStart_4686316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686323 : List Nat := [1, 1, 1, 2, 2, 2, 3, 6, 1, 1, 3]
def baseStart_4686323 : Nat := 118140960795 + 4686323 * 2 ^ 59
def prefixEnd_4686323 : Nat := 4983230072969 + 3 ^ 40 * 4686323 * 2
def baseEnd_4686323 : Nat := 2406336201220173473410499

theorem tailTrace_4686323 : CollatzResearch.WordTrace tailWord_4686323 prefixEnd_4686323 2406336201220173473410499 := by
  unfold tailWord_4686323
  simp only [CollatzResearch.WordTrace]
  refine ⟨170924241801259606093575623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113949494534173070729050415 170924241801259606093575623)
  ·
    refine ⟨256386362701889409140363435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170924241801259606093575623 256386362701889409140363435)
    ·
      refine ⟨384579544052834113710545153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256386362701889409140363435 384579544052834113710545153)
      ·
        refine ⟨288434658039625585282908865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 384579544052834113710545153 288434658039625585282908865)
        ·
          refine ⟨216325993529719188962181649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288434658039625585282908865 216325993529719188962181649)
          ·
            refine ⟨162244495147289391721636237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216325993529719188962181649 162244495147289391721636237)
            ·
              refine ⟨60841685680233521895613589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162244495147289391721636237 60841685680233521895613589)
              ·
                refine ⟨2851954016260946338856887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60841685680233521895613589 2851954016260946338856887)
                ·
                  refine ⟨4277931024391419508285331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2851954016260946338856887 4277931024391419508285331)
                  ·
                    refine ⟨6416896536587129262427997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4277931024391419508285331 6416896536587129262427997)
                    ·
                      refine ⟨2406336201220173473410499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6416896536587129262427997 2406336201220173473410499)
                      ·
                        rfl

theorem cell23_4686323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6, 1, 1, 3].length) (baseStart_4686323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686323 prefixEnd_4686323 := by exact prefixLift 4686323
  have htrace : WordTrace (prefixWord ++ tailWord_4686323) baseStart_4686323 baseEnd_4686323 := by
    simpa [prefixWord, tailWord_4686323, baseEnd_4686323] using wordTrace_append hprefix tailTrace_4686323
  have hstable : (prefixWord ++ tailWord_4686323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686323).length < 2 ^ (prefixWord ++ tailWord_4686323).sum := by decide
  have hdescent : baseEnd_4686323 < baseStart_4686323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686329 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 5, 1, 4]
def baseStart_4686329 : Nat := 118140960795 + 4686329 * 2 ^ 59
def prefixEnd_4686329 : Nat := 4983230072969 + 3 ^ 40 * 4686329 * 2
def baseEnd_4686329 : Nat := 2406339282104100449935471

theorem tailTrace_4686329 : CollatzResearch.WordTrace tailWord_4686329 prefixEnd_4686329 2406339282104100449935471 := by
  unfold tailWord_4686329
  simp only [CollatzResearch.WordTrace]
  refine ⟨170924460639237869118294041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113949640426158579412196027 170924460639237869118294041)
  ·
    refine ⟨128193345479428401838720531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170924460639237869118294041 128193345479428401838720531)
    ·
      refine ⟨192290018219142602758080797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128193345479428401838720531 192290018219142602758080797)
      ·
        refine ⟨72108756832178476034280299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192290018219142602758080797 72108756832178476034280299)
        ·
          refine ⟨108163135248267714051420449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72108756832178476034280299 108163135248267714051420449)
          ·
            refine ⟨81122351436200785538565337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108163135248267714051420449 81122351436200785538565337)
            ·
              refine ⟨60841763577150589153924003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81122351436200785538565337 60841763577150589153924003)
              ·
                refine ⟨91262645365725883730886005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60841763577150589153924003 91262645365725883730886005)
                ·
                  refine ⟨8555873003036801599770563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91262645365725883730886005 8555873003036801599770563)
                  ·
                    refine ⟨12833809504555202399655845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8555873003036801599770563 12833809504555202399655845)
                    ·
                      refine ⟨2406339282104100449935471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12833809504555202399655845 2406339282104100449935471)
                      ·
                        rfl

theorem cell23_4686329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_4686329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686329 prefixEnd_4686329 := by exact prefixLift 4686329
  have htrace : WordTrace (prefixWord ++ tailWord_4686329) baseStart_4686329 baseEnd_4686329 := by
    simpa [prefixWord, tailWord_4686329, baseEnd_4686329] using wordTrace_append hprefix tailTrace_4686329
  have hstable : (prefixWord ++ tailWord_4686329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686329).length < 2 ^ (prefixWord ++ tailWord_4686329).sum := by decide
  have hdescent : baseEnd_4686329 < baseStart_4686329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686343 : List Nat := [1, 1, 4, 3, 3, 1, 2, 2, 1, 5]
def baseStart_4686343 : Nat := 118140960795 + 4686343 * 2 ^ 59
def prefixEnd_4686343 : Nat := 4983230072969 + 3 ^ 40 * 4686343 * 2
def baseEnd_4686343 : Nat := 802115490277754465053469

theorem tailTrace_4686343 : CollatzResearch.WordTrace tailWord_4686343 prefixEnd_4686343 802115490277754465053469 := by
  unfold tailWord_4686343
  simp only [CollatzResearch.WordTrace]
  refine ⟨170924971261187149509303683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113949980840791433006202455 170924971261187149509303683)
  ·
    refine ⟨256387456891780724263955525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170924971261187149509303683 256387456891780724263955525)
    ·
      refine ⟨48072648167208885799491661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 256387456891780724263955525 48072648167208885799491661)
      ·
        refine ⟨18027243062703332174809373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48072648167208885799491661 18027243062703332174809373)
        ·
          refine ⟨6760216148513749565553515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18027243062703332174809373 6760216148513749565553515)
          ·
            refine ⟨10140324222770624348330273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6760216148513749565553515 10140324222770624348330273)
            ·
              refine ⟨7605243167077968261247705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10140324222770624348330273 7605243167077968261247705)
              ·
                refine ⟨5703932375308476195935779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7605243167077968261247705 5703932375308476195935779)
                ·
                  refine ⟨8555898562962714293903669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5703932375308476195935779 8555898562962714293903669)
                  ·
                    refine ⟨802115490277754465053469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8555898562962714293903669 802115490277754465053469)
                    ·
                      rfl

theorem cell23_4686343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_4686343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686343 prefixEnd_4686343 := by exact prefixLift 4686343
  have htrace : WordTrace (prefixWord ++ tailWord_4686343) baseStart_4686343 baseEnd_4686343 := by
    simpa [prefixWord, tailWord_4686343, baseEnd_4686343] using wordTrace_append hprefix tailTrace_4686343
  have hstable : (prefixWord ++ tailWord_4686343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686343).length < 2 ^ (prefixWord ++ tailWord_4686343).sum := by decide
  have hdescent : baseEnd_4686343 < baseStart_4686343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686346 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 2, 6, 2]
def baseStart_4686346 : Nat := 118140960795 + 4686346 * 2 ^ 59
def prefixEnd_4686346 : Nat := 4983230072969 + 3 ^ 40 * 4686346 * 2
def baseEnd_4686346 : Nat := 2406348011275226883422893

theorem tailTrace_4686346 : CollatzResearch.WordTrace tailWord_4686346 prefixEnd_4686346 2406348011275226883422893 := by
  unfold tailWord_4686346
  simp only [CollatzResearch.WordTrace]
  refine ⟨42731270170044070255415723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113950053786784187347775261 42731270170044070255415723)
  ·
    refine ⟨64096905255066105383123585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42731270170044070255415723 64096905255066105383123585)
    ·
      refine ⟨48072678941299579037342689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64096905255066105383123585 48072678941299579037342689)
      ·
        refine ⟨36054509205974684278007017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48072678941299579037342689 36054509205974684278007017)
        ·
          refine ⟨27040881904481013208505263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36054509205974684278007017 27040881904481013208505263)
          ·
            refine ⟨40561322856721519812757895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27040881904481013208505263 40561322856721519812757895)
            ·
              refine ⟨60841984285082279719136843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40561322856721519812757895 60841984285082279719136843)
              ·
                refine ⟨91262976427623419578705265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60841984285082279719136843 91262976427623419578705265)
                ·
                  refine ⟨68447232320717564684028949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91262976427623419578705265 68447232320717564684028949)
                  ·
                    refine ⟨3208464015033635844563857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68447232320717564684028949 3208464015033635844563857)
                    ·
                      refine ⟨2406348011275226883422893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3208464015033635844563857 2406348011275226883422893)
                      ·
                        rfl

theorem cell23_4686346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_4686346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686346 prefixEnd_4686346 := by exact prefixLift 4686346
  have htrace : WordTrace (prefixWord ++ tailWord_4686346) baseStart_4686346 baseEnd_4686346 := by
    simpa [prefixWord, tailWord_4686346, baseEnd_4686346] using wordTrace_append hprefix tailTrace_4686346
  have hstable : (prefixWord ++ tailWord_4686346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686346).length < 2 ^ (prefixWord ++ tailWord_4686346).sum := by decide
  have hdescent : baseEnd_4686346 < baseStart_4686346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686376 : List Nat := [2, 1, 5, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_4686376 : Nat := 118140960795 + 4686376 * 2 ^ 59
def prefixEnd_4686376 : Nat := 4983230072969 + 3 ^ 40 * 4686376 * 2
def baseEnd_4686376 : Nat := 2406363415694861766047755

theorem tailTrace_4686376 : CollatzResearch.WordTrace tailWord_4686376 prefixEnd_4686376 2406363415694861766047755 := by
  unfold tailWord_4686376
  simp only [CollatzResearch.WordTrace]
  refine ⟨85463087435033798072627491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113950783246711730763503321 85463087435033798072627491)
  ·
    refine ⟨128194631152550697108941237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85463087435033798072627491 128194631152550697108941237)
    ·
      refine ⟨12018246670551627853963241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 128194631152550697108941237 12018246670551627853963241)
      ·
        refine ⟨9013685002913720890472431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12018246670551627853963241 9013685002913720890472431)
        ·
          refine ⟨13520527504370581335708647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9013685002913720890472431 13520527504370581335708647)
          ·
            refine ⟨20280791256555872003562971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13520527504370581335708647 20280791256555872003562971)
            ·
              refine ⟨30421186884833808005344457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20280791256555872003562971 30421186884833808005344457)
              ·
                refine ⟨22815890163625356004008343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30421186884833808005344457 22815890163625356004008343)
                ·
                  refine ⟨34223835245438034006012515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22815890163625356004008343 34223835245438034006012515)
                  ·
                    refine ⟨51335752868157051009018773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34223835245438034006012515 51335752868157051009018773)
                    ·
                      refine ⟨2406363415694861766047755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51335752868157051009018773 2406363415694861766047755)
                      ·
                        rfl

theorem cell23_4686376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_4686376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686376 prefixEnd_4686376 := by exact prefixLift 4686376
  have htrace : WordTrace (prefixWord ++ tailWord_4686376) baseStart_4686376 baseEnd_4686376 := by
    simpa [prefixWord, tailWord_4686376, baseEnd_4686376] using wordTrace_append hprefix tailTrace_4686376
  have hstable : (prefixWord ++ tailWord_4686376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686376).length < 2 ^ (prefixWord ++ tailWord_4686376).sum := by decide
  have hdescent : baseEnd_4686376 < baseStart_4686376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686380 : List Nat := [2, 2, 1, 1, 1, 2, 1, 8, 1, 2, 2]
def baseStart_4686380 : Nat := 118140960795 + 4686380 * 2 ^ 59
def prefixEnd_4686380 : Nat := 4983230072969 + 3 ^ 40 * 4686380 * 2
def baseEnd_4686380 : Nat := 2406365469617479750397737

theorem tailTrace_4686380 : CollatzResearch.WordTrace tailWord_4686380 prefixEnd_4686380 2406365469617479750397737 := by
  unfold tailWord_4686380
  simp only [CollatzResearch.WordTrace]
  refine ⟨85463160381026552414200297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113950880508035403218933729 85463160381026552414200297)
  ·
    refine ⟨64097370285769914310650223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85463160381026552414200297 64097370285769914310650223)
    ·
      refine ⟨96146055428654871465975335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64097370285769914310650223 96146055428654871465975335)
      ·
        refine ⟨144219083142982307198963003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96146055428654871465975335 144219083142982307198963003)
        ·
          refine ⟨216328624714473460798444505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144219083142982307198963003 216328624714473460798444505)
          ·
            refine ⟨162246468535855095598833379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216328624714473460798444505 162246468535855095598833379)
            ·
              refine ⟨243369702803782643398250069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162246468535855095598833379 243369702803782643398250069)
              ·
                refine ⟨2851988704731827852323243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 243369702803782643398250069 2851988704731827852323243)
                ·
                  refine ⟨4277983057097741778484865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2851988704731827852323243 4277983057097741778484865)
                  ·
                    refine ⟨3208487292823306333863649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4277983057097741778484865 3208487292823306333863649)
                    ·
                      refine ⟨2406365469617479750397737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3208487292823306333863649 2406365469617479750397737)
                      ·
                        rfl

theorem cell23_4686380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8, 1, 2, 2].length) (baseStart_4686380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686380 prefixEnd_4686380 := by exact prefixLift 4686380
  have htrace : WordTrace (prefixWord ++ tailWord_4686380) baseStart_4686380 baseEnd_4686380 := by
    simpa [prefixWord, tailWord_4686380, baseEnd_4686380] using wordTrace_append hprefix tailTrace_4686380
  have hstable : (prefixWord ++ tailWord_4686380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686380).length < 2 ^ (prefixWord ++ tailWord_4686380).sum := by decide
  have hdescent : baseEnd_4686380 < baseStart_4686380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686389 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_4686389 : Nat := 118140960795 + 4686389 * 2 ^ 59
def prefixEnd_4686389 : Nat := 4983230072969 + 3 ^ 40 * 4686389 * 2
def baseEnd_4686389 : Nat := 2406370090943370215185195

theorem tailTrace_4686389 : CollatzResearch.WordTrace tailWord_4686389 prefixEnd_4686389 2406370090943370215185195 := by
  unfold tailWord_4686389
  simp only [CollatzResearch.WordTrace]
  refine ⟨170926649019020499365478221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113951099346013666243652147 170926649019020499365478221)
  ·
    refine ⟨64097493382132687262054333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170926649019020499365478221 64097493382132687262054333)
    ·
      refine ⟨24036560018299757723270375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64097493382132687262054333 24036560018299757723270375)
      ·
        refine ⟨36054840027449636584905563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24036560018299757723270375 36054840027449636584905563)
        ·
          refine ⟨54082260041174454877358345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36054840027449636584905563 54082260041174454877358345)
          ·
            refine ⟨40561695030880841158018759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54082260041174454877358345 40561695030880841158018759)
            ·
              refine ⟨60842542546321261737028139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40561695030880841158018759 60842542546321261737028139)
              ·
                refine ⟨91263813819481892605542209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60842542546321261737028139 91263813819481892605542209)
                ·
                  refine ⟨68447860364611419454156657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91263813819481892605542209 68447860364611419454156657)
                  ·
                    refine ⟨51335895273458564590617493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68447860364611419454156657 51335895273458564590617493)
                    ·
                      refine ⟨2406370090943370215185195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51335895273458564590617493 2406370090943370215185195)
                      ·
                        rfl

theorem cell23_4686389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_4686389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686389 prefixEnd_4686389 := by exact prefixLift 4686389
  have htrace : WordTrace (prefixWord ++ tailWord_4686389) baseStart_4686389 baseEnd_4686389 := by
    simpa [prefixWord, tailWord_4686389, baseEnd_4686389] using wordTrace_append hprefix tailTrace_4686389
  have hstable : (prefixWord ++ tailWord_4686389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686389).length < 2 ^ (prefixWord ++ tailWord_4686389).sum := by decide
  have hdescent : baseEnd_4686389 < baseStart_4686389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686390 : List Nat := [5, 1, 2, 1, 2, 2, 1, 3, 2, 4]
def baseStart_4686390 : Nat := 118140960795 + 4686390 * 2 ^ 59
def prefixEnd_4686390 : Nat := 4983230072969 + 3 ^ 40 * 4686390 * 2
def baseEnd_4686390 : Nat := 802123534808008237090897

theorem tailTrace_4686390 : CollatzResearch.WordTrace tailWord_4686390 prefixEnd_4686390 802123534808008237090897 := by
  unfold tailWord_4686390
  simp only [CollatzResearch.WordTrace]
  refine ⟨10682917843251054783516539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113951123661344584357509749 10682917843251054783516539)
  ·
    refine ⟨16024376764876582175274809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10682917843251054783516539 16024376764876582175274809)
    ·
      refine ⟨12018282573657436631456107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16024376764876582175274809 12018282573657436631456107)
      ·
        refine ⟨18027423860486154947184161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12018282573657436631456107 18027423860486154947184161)
        ·
          refine ⟨13520567895364616210388121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18027423860486154947184161 13520567895364616210388121)
          ·
            refine ⟨10140425921523462157791091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13520567895364616210388121 10140425921523462157791091)
            ·
              refine ⟨15210638882285193236686637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10140425921523462157791091 15210638882285193236686637)
              ·
                refine ⟨5703989580856947463757489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15210638882285193236686637 5703989580856947463757489)
                ·
                  refine ⟨4277992185642710597818117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5703989580856947463757489 4277992185642710597818117)
                  ·
                    refine ⟨802123534808008237090897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4277992185642710597818117 802123534808008237090897)
                    ·
                      rfl

theorem cell23_4686390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_4686390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686390 prefixEnd_4686390 := by exact prefixLift 4686390
  have htrace : WordTrace (prefixWord ++ tailWord_4686390) baseStart_4686390 baseEnd_4686390 := by
    simpa [prefixWord, tailWord_4686390, baseEnd_4686390] using wordTrace_append hprefix tailTrace_4686390
  have hstable : (prefixWord ++ tailWord_4686390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686390).length < 2 ^ (prefixWord ++ tailWord_4686390).sum := by decide
  have hdescent : baseEnd_4686390 < baseStart_4686390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686413 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_4686413 : Nat := 118140960795 + 4686413 * 2 ^ 59
def prefixEnd_4686413 : Nat := 4983230072969 + 3 ^ 40 * 4686413 * 2
def baseEnd_4686413 : Nat := 2406382414479078121285085

theorem tailTrace_4686413 : CollatzResearch.WordTrace tailWord_4686413 prefixEnd_4686413 2406382414479078121285085 := by
  unfold tailWord_4686413
  simp only [CollatzResearch.WordTrace]
  refine ⟨170927524370933551464351893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113951682913955700976234595 170927524370933551464351893)
  ·
    refine ⟨8012227704887510224891495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 170927524370933551464351893 8012227704887510224891495)
    ·
      refine ⟨12018341557331265337337243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8012227704887510224891495 12018341557331265337337243)
      ·
        refine ⟨18027512335996898006005865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12018341557331265337337243 18027512335996898006005865)
        ·
          refine ⟨13520634251997673504504399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18027512335996898006005865 13520634251997673504504399)
          ·
            refine ⟨20280951377996510256756599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13520634251997673504504399 20280951377996510256756599)
            ·
              refine ⟨30421427066994765385134899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20280951377996510256756599 30421427066994765385134899)
              ·
                refine ⟨45632140600492148077702349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30421427066994765385134899 45632140600492148077702349)
                ·
                  refine ⟨17112052725184555529138381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45632140600492148077702349 17112052725184555529138381)
                  ·
                    refine ⟨6417019771944208323426893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17112052725184555529138381 6417019771944208323426893)
                    ·
                      refine ⟨2406382414479078121285085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6417019771944208323426893 2406382414479078121285085)
                      ·
                        rfl

theorem cell23_4686413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_4686413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686413 prefixEnd_4686413 := by exact prefixLift 4686413
  have htrace : WordTrace (prefixWord ++ tailWord_4686413) baseStart_4686413 baseEnd_4686413 := by
    simpa [prefixWord, tailWord_4686413, baseEnd_4686413] using wordTrace_append hprefix tailTrace_4686413
  have hstable : (prefixWord ++ tailWord_4686413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686413).length < 2 ^ (prefixWord ++ tailWord_4686413).sum := by decide
  have hdescent : baseEnd_4686413 < baseStart_4686413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686446 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 1, 8]
def baseStart_4686446 : Nat := 118140960795 + 4686446 * 2 ^ 59
def prefixEnd_4686446 : Nat := 4983230072969 + 3 ^ 40 * 4686446 * 2
def baseEnd_4686446 : Nat := 802133119780225497390811

theorem tailTrace_4686446 : CollatzResearch.WordTrace tailWord_4686446 prefixEnd_4686446 802133119780225497390811 := by
  unfold tailWord_4686446
  simp only [CollatzResearch.WordTrace]
  refine ⟨21366090997476749762537899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113952485319875998733535461 21366090997476749762537899)
  ·
    refine ⟨32049136496215124643806849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21366090997476749762537899 32049136496215124643806849)
    ·
      refine ⟨24036852372161343482855137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32049136496215124643806849 24036852372161343482855137)
      ·
        refine ⟨18027639279121007612141353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24036852372161343482855137 18027639279121007612141353)
        ·
          refine ⟨13520729459340755709106015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18027639279121007612141353 13520729459340755709106015)
          ·
            refine ⟨20281094189011133563659023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13520729459340755709106015 20281094189011133563659023)
            ·
              refine ⟨30421641283516700345488535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20281094189011133563659023 30421641283516700345488535)
              ·
                refine ⟨45632461925275050518232803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30421641283516700345488535 45632461925275050518232803)
                ·
                  refine ⟨68448692887912575777349205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45632461925275050518232803 68448692887912575777349205)
                  ·
                    refine ⟨802133119780225497390811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68448692887912575777349205 802133119780225497390811)
                    ·
                      rfl

theorem cell23_4686446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_4686446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686446 prefixEnd_4686446 := by exact prefixLift 4686446
  have htrace : WordTrace (prefixWord ++ tailWord_4686446) baseStart_4686446 baseEnd_4686446 := by
    simpa [prefixWord, tailWord_4686446, baseEnd_4686446] using wordTrace_append hprefix tailTrace_4686446
  have hstable : (prefixWord ++ tailWord_4686446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686446).length < 2 ^ (prefixWord ++ tailWord_4686446).sum := by decide
  have hdescent : baseEnd_4686446 < baseStart_4686446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686474 : List Nat := [3, 1, 2, 3, 3, 2, 2, 1, 1, 3, 2]
def baseStart_4686474 : Nat := 118140960795 + 4686474 * 2 ^ 59
def prefixEnd_4686474 : Nat := 4983230072969 + 3 ^ 40 * 4686474 * 2
def baseEnd_4686474 : Nat := 2406413736799002382622305

theorem tailTrace_4686474 : CollatzResearch.WordTrace tailWord_4686474 prefixEnd_4686474 2406413736799002382622305 := by
  unfold tailWord_4686474
  simp only [CollatzResearch.WordTrace]
  refine ⟨42732437305928139720580619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113953166149141705921548317 42732437305928139720580619)
  ·
    refine ⟨64098655958892209580870929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42732437305928139720580619 64098655958892209580870929)
    ·
      refine ⟨48073991969169157185653197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64098655958892209580870929 48073991969169157185653197)
      ·
        refine ⟨18027746988438433944619949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48073991969169157185653197 18027746988438433944619949)
        ·
          refine ⟨6760405120664412729232481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18027746988438433944619949 6760405120664412729232481)
          ·
            refine ⟨5070303840498309546924361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6760405120664412729232481 5070303840498309546924361)
            ·
              refine ⟨3802727880373732160193271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5070303840498309546924361 3802727880373732160193271)
              ·
                refine ⟨5704091820560598240289907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3802727880373732160193271 5704091820560598240289907)
                ·
                  refine ⟨8556137730840897360434861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5704091820560598240289907 8556137730840897360434861)
                  ·
                    refine ⟨3208551649065336510163073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8556137730840897360434861 3208551649065336510163073)
                    ·
                      refine ⟨2406413736799002382622305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3208551649065336510163073 2406413736799002382622305)
                      ·
                        rfl

theorem cell23_4686474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_4686474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686474 prefixEnd_4686474 := by exact prefixLift 4686474
  have htrace : WordTrace (prefixWord ++ tailWord_4686474) baseStart_4686474 baseEnd_4686474 := by
    simpa [prefixWord, tailWord_4686474, baseEnd_4686474] using wordTrace_append hprefix tailTrace_4686474
  have hstable : (prefixWord ++ tailWord_4686474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686474).length < 2 ^ (prefixWord ++ tailWord_4686474).sum := by decide
  have hdescent : baseEnd_4686474 < baseStart_4686474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686493 : List Nat := [1, 4, 2, 1, 1, 1, 4, 4, 5]
def baseStart_4686493 : Nat := 118140960795 + 4686493 * 2 ^ 59
def prefixEnd_4686493 : Nat := 4983230072969 + 3 ^ 40 * 4686493 * 2
def baseEnd_4686493 : Nat := 267380388103493089809413

theorem tailTrace_4686493 : CollatzResearch.WordTrace tailWord_4686493 prefixEnd_4686493 267380388103493089809413 := by
  unfold tailWord_4686493
  simp only [CollatzResearch.WordTrace]
  refine ⟨170930442210643725127264133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113953628140429150084842755 170930442210643725127264133)
  ·
    refine ⟨32049457914495698461362025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170930442210643725127264133 32049457914495698461362025)
    ·
      refine ⟨24037093435871773846021519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32049457914495698461362025 24037093435871773846021519)
      ·
        refine ⟨36055640153807660769032279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24037093435871773846021519 36055640153807660769032279)
        ·
          refine ⟨54083460230711491153548419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36055640153807660769032279 54083460230711491153548419)
          ·
            refine ⟨81125190346067236730322629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54083460230711491153548419 81125190346067236730322629)
            ·
              refine ⟨15210973189887606886935493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81125190346067236730322629 15210973189887606886935493)
              ·
                refine ⟨2852057473103926291300405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15210973189887606886935493 2852057473103926291300405)
                ·
                  refine ⟨267380388103493089809413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2852057473103926291300405 267380388103493089809413)
                  ·
                    rfl

theorem cell23_4686493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4, 5].length) (baseStart_4686493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686493 prefixEnd_4686493 := by exact prefixLift 4686493
  have htrace : WordTrace (prefixWord ++ tailWord_4686493) baseStart_4686493 baseEnd_4686493 := by
    simpa [prefixWord, tailWord_4686493, baseEnd_4686493] using wordTrace_append hprefix tailTrace_4686493
  have hstable : (prefixWord ++ tailWord_4686493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686493).length < 2 ^ (prefixWord ++ tailWord_4686493).sum := by decide
  have hdescent : baseEnd_4686493 < baseStart_4686493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686603 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 3, 5, 2]
def baseStart_4686603 : Nat := 118140960795 + 4686603 * 2 ^ 59
def prefixEnd_4686603 : Nat := 4983230072969 + 3 ^ 40 * 4686603 * 2
def baseEnd_4686603 : Nat := 2406479975803432377909211

theorem tailTrace_4686603 : CollatzResearch.WordTrace tailWord_4686603 prefixEnd_4686603 2406479975803432377909211 := by
  unfold tailWord_4686603
  simp only [CollatzResearch.WordTrace]
  refine ⟨170934454240245213913768463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113956302826830142609178975 170934454240245213913768463)
  ·
    refine ⟨256401681360367820870652695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170934454240245213913768463 256401681360367820870652695)
    ·
      refine ⟨384602522040551731305979043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256401681360367820870652695 384602522040551731305979043)
      ·
        refine ⟨576903783060827596958968565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384602522040551731305979043 576903783060827596958968565)
        ·
          refine ⟨54084729661952587214903303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 576903783060827596958968565 54084729661952587214903303)
          ·
            refine ⟨81127094492928880822354955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54084729661952587214903303 81127094492928880822354955)
            ·
              refine ⟨121690641739393321233532433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81127094492928880822354955 121690641739393321233532433)
              ·
                refine ⟨91267981304544990925149325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121690641739393321233532433 91267981304544990925149325)
                ·
                  refine ⟨34225492989204371596930997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91267981304544990925149325 34225492989204371596930997)
                  ·
                    refine ⟨3208639967737909837212281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34225492989204371596930997 3208639967737909837212281)
                    ·
                      refine ⟨2406479975803432377909211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3208639967737909837212281 2406479975803432377909211)
                      ·
                        rfl

theorem cell23_4686603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 5, 2].length) (baseStart_4686603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686603 prefixEnd_4686603 := by exact prefixLift 4686603
  have htrace : WordTrace (prefixWord ++ tailWord_4686603) baseStart_4686603 baseEnd_4686603 := by
    simpa [prefixWord, tailWord_4686603, baseEnd_4686603] using wordTrace_append hprefix tailTrace_4686603
  have hstable : (prefixWord ++ tailWord_4686603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686603).length < 2 ^ (prefixWord ++ tailWord_4686603).sum := by decide
  have hdescent : baseEnd_4686603 < baseStart_4686603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686633 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 2, 6, 2]
def baseStart_4686633 : Nat := 118140960795 + 4686633 * 2 ^ 59
def prefixEnd_4686633 : Nat := 4983230072969 + 3 ^ 40 * 4686633 * 2
def baseEnd_4686633 : Nat := 2406495380223067260534073

theorem tailTrace_4686633 : CollatzResearch.WordTrace tailWord_4686633 prefixEnd_4686633 2406495380223067260534073 := by
  unfold tailWord_4686633
  simp only [CollatzResearch.WordTrace]
  refine ⟨170935548430136529037360553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113957032286757686024907035 170935548430136529037360553)
  ·
    refine ⟨128201661322602396778020415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170935548430136529037360553 128201661322602396778020415)
    ·
      refine ⟨192302491983903595167030623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128201661322602396778020415 192302491983903595167030623)
      ·
        refine ⟨288453737975855392750545935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192302491983903595167030623 288453737975855392750545935)
        ·
          refine ⟨432680606963783089125818903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288453737975855392750545935 432680606963783089125818903)
          ·
            refine ⟨649020910445674633688728355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432680606963783089125818903 649020910445674633688728355)
            ·
              refine ⟨973531365668511950533092533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 649020910445674633688728355 973531365668511950533092533)
              ·
                refine ⟨91268565531422995362477425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 973531365668511950533092533 91268565531422995362477425)
                ·
                  refine ⟨68451424148567246521858069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91268565531422995362477425 68451424148567246521858069)
                  ·
                    refine ⟨3208660506964089680712097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68451424148567246521858069 3208660506964089680712097)
                    ·
                      refine ⟨2406495380223067260534073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3208660506964089680712097 2406495380223067260534073)
                      ·
                        rfl

theorem cell23_4686633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 6, 2].length) (baseStart_4686633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686633 prefixEnd_4686633 := by exact prefixLift 4686633
  have htrace : WordTrace (prefixWord ++ tailWord_4686633) baseStart_4686633 baseEnd_4686633 := by
    simpa [prefixWord, tailWord_4686633, baseEnd_4686633] using wordTrace_append hprefix tailTrace_4686633
  have hstable : (prefixWord ++ tailWord_4686633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686633).length < 2 ^ (prefixWord ++ tailWord_4686633).sum := by decide
  have hdescent : baseEnd_4686633 < baseStart_4686633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686643 : List Nat := [1, 1, 1, 2, 6, 1, 2, 2, 1, 6]
def baseStart_4686643 : Nat := 118140960795 + 4686643 * 2 ^ 59
def prefixEnd_4686643 : Nat := 4983230072969 + 3 ^ 40 * 4686643 * 2
def baseEnd_4686643 : Nat := 802166838343204073803009

theorem tailTrace_4686643 : CollatzResearch.WordTrace tailWord_4686643 prefixEnd_4686643 802166838343204073803009 := by
  unfold tailWord_4686643
  simp only [CollatzResearch.WordTrace]
  refine ⟨170935913160100300745224583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113957275440066867163483055 170935913160100300745224583)
  ·
    refine ⟨256403869740150451117836875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170935913160100300745224583 256403869740150451117836875)
    ·
      refine ⟨384605804610225676676755313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256403869740150451117836875 384605804610225676676755313)
      ·
        refine ⟨288454353457669257507566485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 384605804610225676676755313 288454353457669257507566485)
        ·
          refine ⟨13521297818328246445667179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 288454353457669257507566485 13521297818328246445667179)
          ·
            refine ⟨20281946727492369668500769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13521297818328246445667179 20281946727492369668500769)
            ·
              refine ⟨15211460045619277251375577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20281946727492369668500769 15211460045619277251375577)
              ·
                refine ⟨11408595034214457938531683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15211460045619277251375577 11408595034214457938531683)
                ·
                  refine ⟨17112892551321686907797525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11408595034214457938531683 17112892551321686907797525)
                  ·
                    refine ⟨802166838343204073803009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17112892551321686907797525 802166838343204073803009)
                    ·
                      rfl

theorem cell23_4686643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 6].length) (baseStart_4686643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686643 prefixEnd_4686643 := by exact prefixLift 4686643
  have htrace : WordTrace (prefixWord ++ tailWord_4686643) baseStart_4686643 baseEnd_4686643 := by
    simpa [prefixWord, tailWord_4686643, baseEnd_4686643] using wordTrace_append hprefix tailTrace_4686643
  have hstable : (prefixWord ++ tailWord_4686643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686643).length < 2 ^ (prefixWord ++ tailWord_4686643).sum := by decide
  have hdescent : baseEnd_4686643 < baseStart_4686643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686677 : List Nat := [1, 3, 2, 2, 2, 1, 5, 1, 2, 4]
def baseStart_4686677 : Nat := 118140960795 + 4686677 * 2 ^ 59
def prefixEnd_4686677 : Nat := 4983230072969 + 3 ^ 40 * 4686677 * 2
def baseEnd_4686677 : Nat := 802172657790621696127957

theorem tailTrace_4686677 : CollatzResearch.WordTrace tailWord_4686677 prefixEnd_4686677 802172657790621696127957 := by
  unfold tailWord_4686677
  simp only [CollatzResearch.WordTrace]
  refine ⟨170937153241977124551962285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113958102161318083034641523 170937153241977124551962285)
  ·
    refine ⟨64101432465741421706985857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170937153241977124551962285 64101432465741421706985857)
    ·
      refine ⟨48076074349306066280239393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64101432465741421706985857 48076074349306066280239393)
      ·
        refine ⟨36057055761979549710179545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48076074349306066280239393 36057055761979549710179545)
        ·
          refine ⟨27042791821484662282634659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36057055761979549710179545 27042791821484662282634659)
          ·
            refine ⟨40564187732226993423951989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27042791821484662282634659 40564187732226993423951989)
            ·
              refine ⟨3802892599896280633495499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40564187732226993423951989 3802892599896280633495499)
              ·
                refine ⟨5704338899844420950243249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3802892599896280633495499 5704338899844420950243249)
                ·
                  refine ⟨4278254174883315712682437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5704338899844420950243249 4278254174883315712682437)
                  ·
                    refine ⟨802172657790621696127957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4278254174883315712682437 802172657790621696127957)
                    ·
                      rfl

theorem cell23_4686677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_4686677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686677 prefixEnd_4686677 := by exact prefixLift 4686677
  have htrace : WordTrace (prefixWord ++ tailWord_4686677) baseStart_4686677 baseEnd_4686677 := by
    simpa [prefixWord, tailWord_4686677, baseEnd_4686677] using wordTrace_append hprefix tailTrace_4686677
  have hstable : (prefixWord ++ tailWord_4686677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686677).length < 2 ^ (prefixWord ++ tailWord_4686677).sum := by decide
  have hdescent : baseEnd_4686677 < baseStart_4686677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686684 : List Nat := [2, 2, 4, 2, 1, 1, 2, 2, 3, 2, 2]
def baseStart_4686684 : Nat := 118140960795 + 4686684 * 2 ^ 59
def prefixEnd_4686684 : Nat := 4983230072969 + 3 ^ 40 * 4686684 * 2
def baseEnd_4686684 : Nat := 2406521567736446560996339

theorem tailTrace_4686684 : CollatzResearch.WordTrace tailWord_4686684 prefixEnd_4686684 2406521567736446560996339 := by
  unfold tailWord_4686684
  simp only [CollatzResearch.WordTrace]
  refine ⟨85468704276475882373733553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113958272368634509831644737 85468704276475882373733553)
  ·
    refine ⟨64101528207356911780300165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85468704276475882373733553 64101528207356911780300165)
    ·
      refine ⟨12019036538879420958806281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64101528207356911780300165 12019036538879420958806281)
      ·
        refine ⟨9014277404159565719104711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12019036538879420958806281 9014277404159565719104711)
        ·
          refine ⟨13521416106239348578657067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9014277404159565719104711 13521416106239348578657067)
          ·
            refine ⟨20282124159359022867985601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13521416106239348578657067 20282124159359022867985601)
            ·
              refine ⟨15211593119519267150989201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20282124159359022867985601 15211593119519267150989201)
              ·
                refine ⟨11408694839639450363241901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15211593119519267150989201 11408694839639450363241901)
                ·
                  refine ⟨4278260564864793886215713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11408694839639450363241901 4278260564864793886215713)
                  ·
                    refine ⟨3208695423648595414661785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4278260564864793886215713 3208695423648595414661785)
                    ·
                      refine ⟨2406521567736446560996339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3208695423648595414661785 2406521567736446560996339)
                      ·
                        rfl

theorem cell23_4686684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_4686684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686684 prefixEnd_4686684 := by exact prefixLift 4686684
  have htrace : WordTrace (prefixWord ++ tailWord_4686684) baseStart_4686684 baseEnd_4686684 := by
    simpa [prefixWord, tailWord_4686684, baseEnd_4686684] using wordTrace_append hprefix tailTrace_4686684
  have hstable : (prefixWord ++ tailWord_4686684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686684).length < 2 ^ (prefixWord ++ tailWord_4686684).sum := by decide
  have hdescent : baseEnd_4686684 < baseStart_4686684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686690 : List Nat := [3, 3, 2, 1, 3, 1, 1, 9]
def baseStart_4686690 : Nat := 118140960795 + 4686690 * 2 ^ 59
def prefixEnd_4686690 : Nat := 4983230072969 + 3 ^ 40 * 4686690 * 2
def baseEnd_4686690 : Nat := 89130542541495316204493

theorem tailTrace_4686690 : CollatzResearch.WordTrace tailWord_4686690 prefixEnd_4686690 89130542541495316204493 := by
  unfold tailWord_4686690
  simp only [CollatzResearch.WordTrace]
  refine ⟨42734406847732506943046381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113958418260620018514790349 42734406847732506943046381)
  ·
    refine ⟨16025402567899690103642393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42734406847732506943046381 16025402567899690103642393)
    ·
      refine ⟨12019051925924767577731795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16025402567899690103642393 12019051925924767577731795)
      ·
        refine ⟨18028577888887151366597693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12019051925924767577731795 18028577888887151366597693)
        ·
          refine ⟨6760716708332681762474135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18028577888887151366597693 6760716708332681762474135)
          ·
            refine ⟨10141075062499022643711203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6760716708332681762474135 10141075062499022643711203)
            ·
              refine ⟨15211612593748533965566805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10141075062499022643711203 15211612593748533965566805)
              ·
                refine ⟨89130542541495316204493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15211612593748533965566805 89130542541495316204493)
                ·
                  rfl

theorem cell23_4686690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 9].length) (baseStart_4686690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686690 prefixEnd_4686690 := by exact prefixLift 4686690
  have htrace : WordTrace (prefixWord ++ tailWord_4686690) baseStart_4686690 baseEnd_4686690 := by
    simpa [prefixWord, tailWord_4686690, baseEnd_4686690] using wordTrace_append hprefix tailTrace_4686690
  have hstable : (prefixWord ++ tailWord_4686690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686690).length < 2 ^ (prefixWord ++ tailWord_4686690).sum := by decide
  have hdescent : baseEnd_4686690 < baseStart_4686690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686700 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 3]
def baseStart_4686700 : Nat := 118140960795 + 4686700 * 2 ^ 59
def prefixEnd_4686700 : Nat := 4983230072969 + 3 ^ 40 * 4686700 * 2
def baseEnd_4686700 : Nat := 2406529783426918498396265

theorem tailTrace_4686700 : CollatzResearch.WordTrace tailWord_4686700 prefixEnd_4686700 2406529783426918498396265 := by
  unfold tailWord_4686700
  simp only [CollatzResearch.WordTrace]
  refine ⟨85468996060446899740024777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113958661413929199653366369 85468996060446899740024777)
  ·
    refine ⟨64101747045335174805018583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85468996060446899740024777 64101747045335174805018583)
    ·
      refine ⟨96152620568002762207527875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64101747045335174805018583 96152620568002762207527875)
      ·
        refine ⟨144228930852004143311291813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96152620568002762207527875 144228930852004143311291813)
        ·
          refine ⟨27042924534750776870867215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144228930852004143311291813 27042924534750776870867215)
          ·
            refine ⟨40564386802126165306300823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27042924534750776870867215 40564386802126165306300823)
            ·
              refine ⟨60846580203189247959451235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40564386802126165306300823 60846580203189247959451235)
              ·
                refine ⟨91269870304783871939176853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60846580203189247959451235 91269870304783871939176853)
                ·
                  refine ⟨4278275170536743997148915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 91269870304783871939176853 4278275170536743997148915)
                  ·
                    refine ⟨6417412755805115995723373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4278275170536743997148915 6417412755805115995723373)
                    ·
                      refine ⟨2406529783426918498396265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6417412755805115995723373 2406529783426918498396265)
                      ·
                        rfl

theorem cell23_4686700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 3].length) (baseStart_4686700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686700 prefixEnd_4686700 := by exact prefixLift 4686700
  have htrace : WordTrace (prefixWord ++ tailWord_4686700) baseStart_4686700 baseEnd_4686700 := by
    simpa [prefixWord, tailWord_4686700, baseEnd_4686700] using wordTrace_append hprefix tailTrace_4686700
  have hstable : (prefixWord ++ tailWord_4686700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686700).length < 2 ^ (prefixWord ++ tailWord_4686700).sum := by decide
  have hdescent : baseEnd_4686700 < baseStart_4686700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686718 : List Nat := [4, 2, 3, 1, 2, 2, 1, 1, 3, 2, 2]
def baseStart_4686718 : Nat := 118140960795 + 4686718 * 2 ^ 59
def prefixEnd_4686718 : Nat := 4983230072969 + 3 ^ 40 * 4686718 * 2
def baseEnd_4686718 : Nat := 2406539026078699427971183

theorem tailTrace_4686718 : CollatzResearch.WordTrace tailWord_4686718 prefixEnd_4686718 2406539026078699427971183 := by
  unfold tailWord_4686718
  simp only [CollatzResearch.WordTrace]
  refine ⟨21367331079353573569275601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113959099089885725702803205 21367331079353573569275601)
  ·
    refine ⟨16025498309515180176956701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21367331079353573569275601 16025498309515180176956701)
    ·
      refine ⟨6009561866068192566358763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16025498309515180176956701 6009561866068192566358763)
      ·
        refine ⟨9014342799102288849538145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6009561866068192566358763 9014342799102288849538145)
        ·
          refine ⟨6760757099326716637153609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9014342799102288849538145 6760757099326716637153609)
          ·
            refine ⟨5070567824495037477865207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6760757099326716637153609 5070567824495037477865207)
            ·
              refine ⟨7605851736742556216797811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5070567824495037477865207 7605851736742556216797811)
              ·
                refine ⟨11408777605113834325196717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7605851736742556216797811 11408777605113834325196717)
                ·
                  refine ⟨4278291601917687871948769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11408777605113834325196717 4278291601917687871948769)
                  ·
                    refine ⟨3208718701438265903961577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4278291601917687871948769 3208718701438265903961577)
                    ·
                      refine ⟨2406539026078699427971183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3208718701438265903961577 2406539026078699427971183)
                      ·
                        rfl

theorem cell23_4686718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_4686718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686718 prefixEnd_4686718 := by exact prefixLift 4686718
  have htrace : WordTrace (prefixWord ++ tailWord_4686718) baseStart_4686718 baseEnd_4686718 := by
    simpa [prefixWord, tailWord_4686718, baseEnd_4686718] using wordTrace_append hprefix tailTrace_4686718
  have hstable : (prefixWord ++ tailWord_4686718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686718).length < 2 ^ (prefixWord ++ tailWord_4686718).sum := by decide
  have hdescent : baseEnd_4686718 < baseStart_4686718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686723 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 4]
def baseStart_4686723 : Nat := 118140960795 + 4686723 * 2 ^ 59
def prefixEnd_4686723 : Nat := 4983230072969 + 3 ^ 40 * 4686723 * 2
def baseEnd_4686723 : Nat := 2406541593481971908408659

theorem tailTrace_4686723 : CollatzResearch.WordTrace tailWord_4686723 prefixEnd_4686723 2406541593481971908408659 := by
  unfold tailWord_4686723
  simp only [CollatzResearch.WordTrace]
  refine ⟨170938830999810474408136823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113959220666540316272091215 170938830999810474408136823)
  ·
    refine ⟨256408246499715711612205235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170938830999810474408136823 256408246499715711612205235)
    ·
      refine ⟨384612369749573567418307853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256408246499715711612205235 384612369749573567418307853)
      ·
        refine ⟨144229638656090087781865445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 384612369749573567418307853 144229638656090087781865445)
        ·
          refine ⟨27043057248016891459099771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144229638656090087781865445 27043057248016891459099771)
          ·
            refine ⟨40564585872025337188649657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27043057248016891459099771 40564585872025337188649657)
            ·
              refine ⟨30423439404019002891487243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40564585872025337188649657 30423439404019002891487243)
              ·
                refine ⟨45635159106028504337230865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30423439404019002891487243 45635159106028504337230865)
                ·
                  refine ⟨34226369329521378252923149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45635159106028504337230865 34226369329521378252923149)
                  ·
                    refine ⟨12834888498570516844846181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34226369329521378252923149 12834888498570516844846181)
                    ·
                      refine ⟨2406541593481971908408659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12834888498570516844846181 2406541593481971908408659)
                      ·
                        rfl

theorem cell23_4686723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_4686723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686723 prefixEnd_4686723 := by exact prefixLift 4686723
  have htrace : WordTrace (prefixWord ++ tailWord_4686723) baseStart_4686723 baseEnd_4686723 := by
    simpa [prefixWord, tailWord_4686723, baseEnd_4686723] using wordTrace_append hprefix tailTrace_4686723
  have hstable : (prefixWord ++ tailWord_4686723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686723).length < 2 ^ (prefixWord ++ tailWord_4686723).sum := by decide
  have hdescent : baseEnd_4686723 < baseStart_4686723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686743 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 5]
def baseStart_4686743 : Nat := 118140960795 + 4686743 * 2 ^ 59
def prefixEnd_4686743 : Nat := 4983230072969 + 3 ^ 40 * 4686743 * 2
def baseEnd_4686743 : Nat := 2406551863095061830158567

theorem tailTrace_4686743 : CollatzResearch.WordTrace tailWord_4686743 prefixEnd_4686743 2406551863095061830158567 := by
  unfold tailWord_4686743
  simp only [CollatzResearch.WordTrace]
  refine ⟨170939560459738017823864883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113959706973158678549243255 170939560459738017823864883)
  ·
    refine ⟨256409340689607026735797325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170939560459738017823864883 256409340689607026735797325)
    ·
      refine ⟨96153502758602635025923997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256409340689607026735797325 96153502758602635025923997)
      ·
        refine ⟨36057563534475988134721499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96153502758602635025923997 36057563534475988134721499)
        ·
          refine ⟨54086345301713982202082249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36057563534475988134721499 54086345301713982202082249)
          ·
            refine ⟨40564758976285486651561687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54086345301713982202082249 40564758976285486651561687)
            ·
              refine ⟨60847138464428229977342531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40564758976285486651561687 60847138464428229977342531)
              ·
                refine ⟨91270707696642344966013797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60847138464428229977342531 91270707696642344966013797)
                ·
                  refine ⟨17113257693120439681127587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91270707696642344966013797 17113257693120439681127587)
                  ·
                    refine ⟨25669886539680659521691381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17113257693120439681127587 25669886539680659521691381)
                    ·
                      refine ⟨2406551863095061830158567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25669886539680659521691381 2406551863095061830158567)
                      ·
                        rfl

theorem cell23_4686743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_4686743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686743 prefixEnd_4686743 := by exact prefixLift 4686743
  have htrace : WordTrace (prefixWord ++ tailWord_4686743) baseStart_4686743 baseEnd_4686743 := by
    simpa [prefixWord, tailWord_4686743, baseEnd_4686743] using wordTrace_append hprefix tailTrace_4686743
  have hstable : (prefixWord ++ tailWord_4686743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686743).length < 2 ^ (prefixWord ++ tailWord_4686743).sum := by decide
  have hdescent : baseEnd_4686743 < baseStart_4686743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686800 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 4, 5, 2]
def baseStart_4686800 : Nat := 118140960795 + 4686800 * 2 ^ 59
def prefixEnd_4686800 : Nat := 4983230072969 + 3 ^ 40 * 4686800 * 2
def baseEnd_4686800 : Nat := 2406581131492368107145805

theorem tailTrace_4686800 : CollatzResearch.WordTrace tailWord_4686800 prefixEnd_4686800 2406581131492368107145805 := by
  unfold tailWord_4686800
  simp only [CollatzResearch.WordTrace]
  refine ⟨85470819710265758279344927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113961092947021011039126569 85470819710265758279344927)
  ·
    refine ⟨128206229565398637419017391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85470819710265758279344927 128206229565398637419017391)
    ·
      refine ⟨192309344348097956128526087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128206229565398637419017391 192309344348097956128526087)
      ·
        refine ⟨288464016522146934192789131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192309344348097956128526087 288464016522146934192789131)
        ·
          refine ⟨432696024783220401289183697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288464016522146934192789131 432696024783220401289183697)
          ·
            refine ⟨324522018587415300966887773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 432696024783220401289183697 324522018587415300966887773)
            ·
              refine ⟨121695756970280737862582915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 324522018587415300966887773 121695756970280737862582915)
              ·
                refine ⟨182543635455421106793874373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121695756970280737862582915 182543635455421106793874373)
                ·
                  refine ⟨34226931647891457523851445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 182543635455421106793874373 34226931647891457523851445)
                  ·
                    refine ⟨3208774841989824142861073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34226931647891457523851445 3208774841989824142861073)
                    ·
                      refine ⟨2406581131492368107145805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3208774841989824142861073 2406581131492368107145805)
                      ·
                        rfl

theorem cell23_4686800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 4, 5, 2].length) (baseStart_4686800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686800 prefixEnd_4686800 := by exact prefixLift 4686800
  have htrace : WordTrace (prefixWord ++ tailWord_4686800) baseStart_4686800 baseEnd_4686800 := by
    simpa [prefixWord, tailWord_4686800, baseEnd_4686800] using wordTrace_append hprefix tailTrace_4686800
  have hstable : (prefixWord ++ tailWord_4686800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686800).length < 2 ^ (prefixWord ++ tailWord_4686800).sum := by decide
  have hdescent : baseEnd_4686800 < baseStart_4686800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686810 : List Nat := [3, 1, 1, 2, 4, 2, 1, 1, 1, 7]
def baseStart_4686810 : Nat := 118140960795 + 4686810 * 2 ^ 59
def prefixEnd_4686810 : Nat := 4983230072969 + 3 ^ 40 * 4686810 * 2
def baseEnd_4686810 : Nat := 802195422099637689340253

theorem tailTrace_4686810 : CollatzResearch.WordTrace tailWord_4686810 prefixEnd_4686810 802195422099637689340253 := by
  unfold tailWord_4686810
  simp only [CollatzResearch.WordTrace]
  refine ⟨42735501037623822066638471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113961336100330192177702589 42735501037623822066638471)
  ·
    refine ⟨64103251556435733099957707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42735501037623822066638471 64103251556435733099957707)
    ·
      refine ⟨96154877334653599649936561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64103251556435733099957707 96154877334653599649936561)
      ·
        refine ⟨72116158000990199737452421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96154877334653599649936561 72116158000990199737452421)
        ·
          refine ⟨13521779625185662450772329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72116158000990199737452421 13521779625185662450772329)
          ·
            refine ⟨10141334718889246838079247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13521779625185662450772329 10141334718889246838079247)
            ·
              refine ⟨15212002078333870257118871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10141334718889246838079247 15212002078333870257118871)
              ·
                refine ⟨22818003117500805385678307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15212002078333870257118871 22818003117500805385678307)
                ·
                  refine ⟨34227004676251208078517461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22818003117500805385678307 34227004676251208078517461)
                  ·
                    refine ⟨802195422099637689340253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34227004676251208078517461 802195422099637689340253)
                    ·
                      rfl

theorem cell23_4686810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 1, 7].length) (baseStart_4686810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686810 prefixEnd_4686810 := by exact prefixLift 4686810
  have htrace : WordTrace (prefixWord ++ tailWord_4686810) baseStart_4686810 baseEnd_4686810 := by
    simpa [prefixWord, tailWord_4686810, baseEnd_4686810] using wordTrace_append hprefix tailTrace_4686810
  have hstable : (prefixWord ++ tailWord_4686810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686810).length < 2 ^ (prefixWord ++ tailWord_4686810).sum := by decide
  have hdescent : baseEnd_4686810 < baseStart_4686810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686843 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 6]
def baseStart_4686843 : Nat := 118140960795 + 4686843 * 2 ^ 59
def prefixEnd_4686843 : Nat := 4983230072969 + 3 ^ 40 * 4686843 * 2
def baseEnd_4686843 : Nat := 2406603211160511438908107

theorem tailTrace_4686843 : CollatzResearch.WordTrace tailWord_4686843 prefixEnd_4686843 2406603211160511438908107 := by
  unfold tailWord_4686843
  simp only [CollatzResearch.WordTrace]
  refine ⟨170943207759375734902505183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113962138506250489935003455 170943207759375734902505183)
  ·
    refine ⟨256414811639063602353757775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170943207759375734902505183 256414811639063602353757775)
    ·
      refine ⟨384622217458595403530636663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256414811639063602353757775 384622217458595403530636663)
      ·
        refine ⟨576933326187893105295954995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384622217458595403530636663 576933326187893105295954995)
        ·
          refine ⟨865399989281839657943932493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 576933326187893105295954995 865399989281839657943932493)
          ·
            refine ⟨324524995980689871728974685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 865399989281839657943932493 324524995980689871728974685)
            ·
              refine ⟨121696873492758701898365507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 324524995980689871728974685 121696873492758701898365507)
              ·
                refine ⟨182545310239138052847548261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121696873492758701898365507 182545310239138052847548261)
                ·
                  refine ⟨34227245669838384908915299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 182545310239138052847548261 34227245669838384908915299)
                  ·
                    refine ⟨51340868504757577363372949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34227245669838384908915299 51340868504757577363372949)
                    ·
                      refine ⟨2406603211160511438908107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51340868504757577363372949 2406603211160511438908107)
                      ·
                        rfl

theorem cell23_4686843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 6].length) (baseStart_4686843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686843 prefixEnd_4686843 := by exact prefixLift 4686843
  have htrace : WordTrace (prefixWord ++ tailWord_4686843) baseStart_4686843 baseEnd_4686843 := by
    simpa [prefixWord, tailWord_4686843, baseEnd_4686843] using wordTrace_append hprefix tailTrace_4686843
  have hstable : (prefixWord ++ tailWord_4686843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686843).length < 2 ^ (prefixWord ++ tailWord_4686843).sum := by decide
  have hdescent : baseEnd_4686843 < baseStart_4686843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686884 : List Nat := [2, 3, 1, 4, 1, 2, 1, 2, 2, 2, 3]
def baseStart_4686884 : Nat := 118140960795 + 4686884 * 2 ^ 59
def prefixEnd_4686884 : Nat := 4983230072969 + 3 ^ 40 * 4686884 * 2
def baseEnd_4686884 : Nat := 2406624263867345778495419

theorem tailTrace_4686884 : CollatzResearch.WordTrace tailWord_4686884 prefixEnd_4686884 2406624263867345778495419 := by
  unfold tailWord_4686884
  simp only [CollatzResearch.WordTrace]
  refine ⟨85472351576113599452373853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113963135434818132603165137 85472351576113599452373853)
  ·
    refine ⟨32052131841042599794640195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85472351576113599452373853 32052131841042599794640195)
    ·
      refine ⟨48078197761563899691960293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32052131841042599794640195 48078197761563899691960293)
      ·
        refine ⟨9014662080293231192242555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48078197761563899691960293 9014662080293231192242555)
        ·
          refine ⟨13521993120439846788363833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9014662080293231192242555 13521993120439846788363833)
          ·
            refine ⟨10141494840329885091272875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13521993120439846788363833 10141494840329885091272875)
            ·
              refine ⟨15212242260494827636909313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10141494840329885091272875 15212242260494827636909313)
              ·
                refine ⟨11409181695371120727681985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15212242260494827636909313 11409181695371120727681985)
                ·
                  refine ⟨8556886271528340545761489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11409181695371120727681985 8556886271528340545761489)
                  ·
                    refine ⟨6417664703646255409321117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8556886271528340545761489 6417664703646255409321117)
                    ·
                      refine ⟨2406624263867345778495419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6417664703646255409321117 2406624263867345778495419)
                      ·
                        rfl

theorem cell23_4686884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_4686884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686884 prefixEnd_4686884 := by exact prefixLift 4686884
  have htrace : WordTrace (prefixWord ++ tailWord_4686884) baseStart_4686884 baseEnd_4686884 := by
    simpa [prefixWord, tailWord_4686884, baseEnd_4686884] using wordTrace_append hprefix tailTrace_4686884
  have hstable : (prefixWord ++ tailWord_4686884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686884).length < 2 ^ (prefixWord ++ tailWord_4686884).sum := by decide
  have hdescent : baseEnd_4686884 < baseStart_4686884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686887 : List Nat := [1, 1, 7, 1, 1, 1, 2, 1, 8]
def baseStart_4686887 : Nat := 118140960795 + 4686887 * 2 ^ 59
def prefixEnd_4686887 : Nat := 4983230072969 + 3 ^ 40 * 4686887 * 2
def baseEnd_4686887 : Nat := 267402867145478807417545

theorem tailTrace_4686887 : CollatzResearch.WordTrace tailWord_4686887 prefixEnd_4686887 267402867145478807417545 := by
  unfold tailWord_4686887
  simp only [CollatzResearch.WordTrace]
  refine ⟨170944812571216330417106915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113963208380810886944737943 170944812571216330417106915)
  ·
    refine ⟨256417218856824495625660373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170944812571216330417106915 256417218856824495625660373)
    ·
      refine ⟨6009778566956824116226415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 256417218856824495625660373 6009778566956824116226415)
      ·
        refine ⟨9014667850435236174339623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6009778566956824116226415 9014667850435236174339623)
        ·
          refine ⟨13522001775652854261509435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9014667850435236174339623 13522001775652854261509435)
          ·
            refine ⟨20283002663479281392264153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13522001775652854261509435 20283002663479281392264153)
            ·
              refine ⟨15212251997609461044198115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20283002663479281392264153 15212251997609461044198115)
              ·
                refine ⟨22818377996414191566297173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15212251997609461044198115 22818377996414191566297173)
                ·
                  refine ⟨267402867145478807417545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22818377996414191566297173 267402867145478807417545)
                  ·
                    rfl

theorem cell23_4686887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 8].length) (baseStart_4686887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686887 prefixEnd_4686887 := by exact prefixLift 4686887
  have htrace : WordTrace (prefixWord ++ tailWord_4686887) baseStart_4686887 baseEnd_4686887 := by
    simpa [prefixWord, tailWord_4686887, baseEnd_4686887] using wordTrace_append hprefix tailTrace_4686887
  have hstable : (prefixWord ++ tailWord_4686887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686887).length < 2 ^ (prefixWord ++ tailWord_4686887).sum := by decide
  have hdescent : baseEnd_4686887 < baseStart_4686887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686904 : List Nat := [2, 1, 2, 1, 5, 3, 2, 1, 6]
def baseStart_4686904 : Nat := 118140960795 + 4686904 * 2 ^ 59
def prefixEnd_4686904 : Nat := 4983230072969 + 3 ^ 40 * 4686904 * 2
def baseEnd_4686904 : Nat := 267403837053381744471703

theorem tailTrace_4686904 : CollatzResearch.WordTrace tailWord_4686904 prefixEnd_4686904 267403837053381744471703 := by
  unfold tailWord_4686904
  simp only [CollatzResearch.WordTrace]
  refine ⟨85472716306077371160237883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113963621741436494880317177 85472716306077371160237883)
  ·
    refine ⟨128209074459116056740356825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85472716306077371160237883 128209074459116056740356825)
    ·
      refine ⟨96156805844337042555267619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128209074459116056740356825 96156805844337042555267619)
      ·
        refine ⟨144235208766505563832901429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96156805844337042555267619 144235208766505563832901429)
        ·
          refine ⟨13522050821859896609334509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 144235208766505563832901429 13522050821859896609334509)
          ·
            refine ⟨5070769058197461228500441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13522050821859896609334509 5070769058197461228500441)
            ·
              refine ⟨3803076793648095921375331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5070769058197461228500441 3803076793648095921375331)
              ·
                refine ⟨5704615190472143882062997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3803076793648095921375331 5704615190472143882062997)
                ·
                  refine ⟨267403837053381744471703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5704615190472143882062997 267403837053381744471703)
                  ·
                    rfl

theorem cell23_4686904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 6].length) (baseStart_4686904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686904 prefixEnd_4686904 := by exact prefixLift 4686904
  have htrace : WordTrace (prefixWord ++ tailWord_4686904) baseStart_4686904 baseEnd_4686904 := by
    simpa [prefixWord, tailWord_4686904, baseEnd_4686904] using wordTrace_append hprefix tailTrace_4686904
  have hstable : (prefixWord ++ tailWord_4686904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686904).length < 2 ^ (prefixWord ++ tailWord_4686904).sum := by decide
  have hdescent : baseEnd_4686904 < baseStart_4686904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686917 : List Nat := [1, 3, 1, 1, 1, 3, 5, 2, 1, 5]
def baseStart_4686917 : Nat := 118140960795 + 4686917 * 2 ^ 59
def prefixEnd_4686917 : Nat := 4983230072969 + 3 ^ 40 * 4686917 * 2
def baseEnd_4686917 : Nat := 802213736242981383127589

theorem tailTrace_4686917 : CollatzResearch.WordTrace tailWord_4686917 prefixEnd_4686917 802213736242981383127589 := by
  unfold tailWord_4686917
  simp only [CollatzResearch.WordTrace]
  refine ⟨170945906761107645540699005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113963937840738430360466003 170945906761107645540699005)
  ·
    refine ⟨64104715035415367077762127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170945906761107645540699005 64104715035415367077762127)
    ·
      refine ⟨96157072553123050616643191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64104715035415367077762127 96157072553123050616643191)
      ·
        refine ⟨144235608829684575924964787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96157072553123050616643191 144235608829684575924964787)
        ·
          refine ⟨216353413244526863887447181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144235608829684575924964787 216353413244526863887447181)
          ·
            refine ⟨81132529966697573957792693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 216353413244526863887447181 81132529966697573957792693)
            ·
              refine ⟨7606174684377897558543065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81132529966697573957792693 7606174684377897558543065)
              ·
                refine ⟨5704631013283423168907299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7606174684377897558543065 5704631013283423168907299)
                ·
                  refine ⟨8556946519925134753360949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5704631013283423168907299 8556946519925134753360949)
                  ·
                    refine ⟨802213736242981383127589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8556946519925134753360949 802213736242981383127589)
                    ·
                      rfl

theorem cell23_4686917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 5].length) (baseStart_4686917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686917 prefixEnd_4686917 := by exact prefixLift 4686917
  have htrace : WordTrace (prefixWord ++ tailWord_4686917) baseStart_4686917 baseEnd_4686917 := by
    simpa [prefixWord, tailWord_4686917, baseEnd_4686917] using wordTrace_append hprefix tailTrace_4686917
  have hstable : (prefixWord ++ tailWord_4686917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686917).length < 2 ^ (prefixWord ++ tailWord_4686917).sum := by decide
  have hdescent : baseEnd_4686917 < baseStart_4686917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686942 : List Nat := [4, 4, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_4686942 : Nat := 118140960795 + 4686942 * 2 ^ 59
def prefixEnd_4686942 : Nat := 4983230072969 + 3 ^ 40 * 4686942 * 2
def baseEnd_4686942 : Nat := 802218015248435517190051

theorem tailTrace_4686942 : CollatzResearch.WordTrace tailWord_4686942 prefixEnd_4686942 802218015248435517190051 := by
  unfold tailWord_4686942
  simp only [CollatzResearch.WordTrace]
  refine ⟨21368352323252134351294885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113964545724011383206906053 21368352323252134351294885)
  ·
    refine ⟨4006566060609775190867791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21368352323252134351294885 4006566060609775190867791)
    ·
      refine ⟨6009849090914662786301687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4006566060609775190867791 6009849090914662786301687)
      ·
        refine ⟨9014773636371994179452531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6009849090914662786301687 9014773636371994179452531)
        ·
          refine ⟨13522160454557991269178797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9014773636371994179452531 13522160454557991269178797)
          ·
            refine ⟨5070810170459246725942049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13522160454557991269178797 5070810170459246725942049)
            ·
              refine ⟨3803107627844435044456537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5070810170459246725942049 3803107627844435044456537)
              ·
                refine ⟨2852330720883326283342403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3803107627844435044456537 2852330720883326283342403)
                ·
                  refine ⟨4278496081324989425013605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2852330720883326283342403 4278496081324989425013605)
                  ·
                    refine ⟨802218015248435517190051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4278496081324989425013605 802218015248435517190051)
                    ·
                      rfl

theorem cell23_4686942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_4686942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686942 prefixEnd_4686942 := by exact prefixLift 4686942
  have htrace : WordTrace (prefixWord ++ tailWord_4686942) baseStart_4686942 baseEnd_4686942 := by
    simpa [prefixWord, tailWord_4686942, baseEnd_4686942] using wordTrace_append hprefix tailTrace_4686942
  have hstable : (prefixWord ++ tailWord_4686942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686942).length < 2 ^ (prefixWord ++ tailWord_4686942).sum := by decide
  have hdescent : baseEnd_4686942 < baseStart_4686942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4686967 : List Nat := [1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 4]
def baseStart_4686967 : Nat := 118140960795 + 4686967 * 2 ^ 59
def prefixEnd_4686967 : Nat := 4983230072969 + 3 ^ 40 * 4686967 * 2
def baseEnd_4686967 : Nat := 2406666882761668953757537

theorem tailTrace_4686967 : CollatzResearch.WordTrace tailWord_4686967 prefixEnd_4686967 2406666882761668953757537 := by
  unfold tailWord_4686967
  simp only [CollatzResearch.WordTrace]
  refine ⟨170947730410926504080019155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113965153607284336053346103 170947730410926504080019155)
  ·
    refine ⟨256421595616389756120028733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170947730410926504080019155 256421595616389756120028733)
    ·
      refine ⟨96158098356146158545010775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256421595616389756120028733 96158098356146158545010775)
      ·
        refine ⟨144237147534219237817516163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96158098356146158545010775 144237147534219237817516163)
        ·
          refine ⟨216355721301328856726274245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144237147534219237817516163 216355721301328856726274245)
          ·
            refine ⟨40566697743999160636176421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 216355721301328856726274245 40566697743999160636176421)
            ·
              refine ⟨7606255826999842619283079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40566697743999160636176421 7606255826999842619283079)
              ·
                refine ⟨11409383740499763928924619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7606255826999842619283079 11409383740499763928924619)
                ·
                  refine ⟨17114075610749645893386929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11409383740499763928924619 17114075610749645893386929)
                  ·
                    refine ⟨12835556708062234420040197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17114075610749645893386929 12835556708062234420040197)
                    ·
                      refine ⟨2406666882761668953757537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12835556708062234420040197 2406666882761668953757537)
                      ·
                        rfl

theorem cell23_4686967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 4].length) (baseStart_4686967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4686967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4686967 prefixEnd_4686967 := by exact prefixLift 4686967
  have htrace : WordTrace (prefixWord ++ tailWord_4686967) baseStart_4686967 baseEnd_4686967 := by
    simpa [prefixWord, tailWord_4686967, baseEnd_4686967] using wordTrace_append hprefix tailTrace_4686967
  have hstable : (prefixWord ++ tailWord_4686967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4686967).length < 2 ^ (prefixWord ++ tailWord_4686967).sum := by decide
  have hdescent : baseEnd_4686967 < baseStart_4686967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4686967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687020 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 1, 8]
def baseStart_4687020 : Nat := 118140960795 + 4687020 * 2 ^ 59
def prefixEnd_4687020 : Nat := 4983230072969 + 3 ^ 40 * 4687020 * 2
def baseEnd_4687020 : Nat := 802231365745452415464931

theorem tailTrace_4687020 : CollatzResearch.WordTrace tailWord_4687020 prefixEnd_4687020 802231365745452415464931 := by
  unfold tailWord_4687020
  simp only [CollatzResearch.WordTrace]
  refine ⟨85474831739867247065849257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113966442319822996087799009 85474831739867247065849257)
  ·
    refine ⟨64106123804900435299386943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85474831739867247065849257 64106123804900435299386943)
    ·
      refine ⟨96159185707350652949080415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64106123804900435299386943 96159185707350652949080415)
      ·
        refine ⟨144238778561025979423620623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96159185707350652949080415 144238778561025979423620623)
        ·
          refine ⟨216358167841538969135430935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144238778561025979423620623 216358167841538969135430935)
          ·
            refine ⟨324537251762308453703146403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216358167841538969135430935 324537251762308453703146403)
            ·
              refine ⟨486805877643462680554719605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324537251762308453703146403 486805877643462680554719605)
              ·
                refine ⟨45638051029074626302004963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 486805877643462680554719605 45638051029074626302004963)
                ·
                  refine ⟨68457076543611939453007445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45638051029074626302004963 68457076543611939453007445)
                  ·
                    refine ⟨802231365745452415464931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68457076543611939453007445 802231365745452415464931)
                    ·
                      rfl

theorem cell23_4687020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 8].length) (baseStart_4687020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687020 prefixEnd_4687020 := by exact prefixLift 4687020
  have htrace : WordTrace (prefixWord ++ tailWord_4687020) baseStart_4687020 baseEnd_4687020 := by
    simpa [prefixWord, tailWord_4687020, baseEnd_4687020] using wordTrace_append hprefix tailTrace_4687020
  have hstable : (prefixWord ++ tailWord_4687020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687020).length < 2 ^ (prefixWord ++ tailWord_4687020).sum := by decide
  have hdescent : baseEnd_4687020 < baseStart_4687020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687031 : List Nat := [1, 1, 3, 1, 4, 1, 4, 2, 1, 3, 2]
def baseStart_4687031 : Nat := 118140960795 + 4687031 * 2 ^ 59
def prefixEnd_4687031 : Nat := 4983230072969 + 3 ^ 40 * 4687031 * 2
def baseEnd_4687031 : Nat := 2406699745523556703357243

theorem tailTrace_4687031 : CollatzResearch.WordTrace tailWord_4687031 prefixEnd_4687031 2406699745523556703357243 := by
  unfold tailWord_4687031
  simp only [CollatzResearch.WordTrace]
  refine ⟨170950064682694643010348947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113966709788463095340232631 170950064682694643010348947)
  ·
    refine ⟨256425097024041964515523421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170950064682694643010348947 256425097024041964515523421)
    ·
      refine ⟨96159411384015736693321283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256425097024041964515523421 96159411384015736693321283)
      ·
        refine ⟨144239117076023605039981925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96159411384015736693321283 144239117076023605039981925)
        ·
          refine ⟨27044834451754425944996611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144239117076023605039981925 27044834451754425944996611)
          ·
            refine ⟨40567251677631638917494917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27044834451754425944996611 40567251677631638917494917)
            ·
              refine ⟨7606359689555932297030297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40567251677631638917494917 7606359689555932297030297)
              ·
                refine ⟨5704769767166949222772723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7606359689555932297030297 5704769767166949222772723)
                ·
                  refine ⟨8557154650750423834159085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5704769767166949222772723 8557154650750423834159085)
                  ·
                    refine ⟨3208932994031408937809657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8557154650750423834159085 3208932994031408937809657)
                    ·
                      refine ⟨2406699745523556703357243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3208932994031408937809657 2406699745523556703357243)
                      ·
                        rfl

theorem cell23_4687031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 3, 2].length) (baseStart_4687031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687031 prefixEnd_4687031 := by exact prefixLift 4687031
  have htrace : WordTrace (prefixWord ++ tailWord_4687031) baseStart_4687031 baseEnd_4687031 := by
    simpa [prefixWord, tailWord_4687031, baseEnd_4687031] using wordTrace_append hprefix tailTrace_4687031
  have hstable : (prefixWord ++ tailWord_4687031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687031).length < 2 ^ (prefixWord ++ tailWord_4687031).sum := by decide
  have hdescent : baseEnd_4687031 < baseStart_4687031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687094 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3]
def baseStart_4687094 : Nat := 118140960795 + 4687094 * 2 ^ 59
def prefixEnd_4687094 : Nat := 4983230072969 + 3 ^ 40 * 4687094 * 2
def baseEnd_4687094 : Nat := 2406732094804789956869453

theorem tailTrace_4687094 : CollatzResearch.WordTrace tailWord_4687094 prefixEnd_4687094 2406732094804789956869453 := by
  unfold tailWord_4687094
  simp only [CollatzResearch.WordTrace]
  refine ⟨10684522655091650298118271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113968241654310936513261557 10684522655091650298118271)
  ·
    refine ⟨16026783982637475447177407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10684522655091650298118271 16026783982637475447177407)
    ·
      refine ⟨24040175973956213170766111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16026783982637475447177407 24040175973956213170766111)
      ·
        refine ⟨36060263960934319756149167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24040175973956213170766111 36060263960934319756149167)
        ·
          refine ⟨54090395941401479634223751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36060263960934319756149167 54090395941401479634223751)
          ·
            refine ⟨81135593912102219451335627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54090395941401479634223751 81135593912102219451335627)
            ·
              refine ⟨121703390868153329177003441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81135593912102219451335627 121703390868153329177003441)
              ·
                refine ⟨91277543151114996882752581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121703390868153329177003441 91277543151114996882752581)
                ·
                  refine ⟨17114539340834061915516109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91277543151114996882752581 17114539340834061915516109)
                  ·
                    refine ⟨6417952252812773218318541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17114539340834061915516109 6417952252812773218318541)
                    ·
                      refine ⟨2406732094804789956869453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6417952252812773218318541 2406732094804789956869453)
                      ·
                        rfl

theorem cell23_4687094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_4687094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687094 prefixEnd_4687094 := by exact prefixLift 4687094
  have htrace : WordTrace (prefixWord ++ tailWord_4687094) baseStart_4687094 baseEnd_4687094 := by
    simpa [prefixWord, tailWord_4687094, baseEnd_4687094] using wordTrace_append hprefix tailTrace_4687094
  have hstable : (prefixWord ++ tailWord_4687094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687094).length < 2 ^ (prefixWord ++ tailWord_4687094).sum := by decide
  have hdescent : baseEnd_4687094 < baseStart_4687094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687107 : List Nat := [1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 5]
def baseStart_4687107 : Nat := 118140960795 + 4687107 * 2 ^ 59
def prefixEnd_4687107 : Nat := 4983230072969 + 3 ^ 40 * 4687107 * 2
def baseEnd_4687107 : Nat := 2406738770053298406006893

theorem tailTrace_4687107 : CollatzResearch.WordTrace tailWord_4687107 prefixEnd_4687107 2406738770053298406006893 := by
  unfold tailWord_4687107
  simp only [CollatzResearch.WordTrace]
  refine ⟨170952836630419307990115575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113968557753612871993410383 170952836630419307990115575)
  ·
    refine ⟨256429254945628961985173363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170952836630419307990115575 256429254945628961985173363)
    ·
      refine ⟨384643882418443442977760045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256429254945628961985173363 384643882418443442977760045)
      ·
        refine ⟨144241455906916291116660017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 384643882418443442977760045 144241455906916291116660017)
        ·
          refine ⟨108181091930187218337495013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144241455906916291116660017 108181091930187218337495013)
          ·
            refine ⟨20283954736910103438280315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108181091930187218337495013 20283954736910103438280315)
            ·
              refine ⟨30425932105365155157420473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20283954736910103438280315 30425932105365155157420473)
              ·
                refine ⟨22819449079023866368065355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30425932105365155157420473 22819449079023866368065355)
                ·
                  refine ⟨34229173618535799552098033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22819449079023866368065355 34229173618535799552098033)
                  ·
                    refine ⟨25671880213901849664073525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34229173618535799552098033 25671880213901849664073525)
                    ·
                      refine ⟨2406738770053298406006893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25671880213901849664073525 2406738770053298406006893)
                      ·
                        rfl

theorem cell23_4687107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_4687107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687107 prefixEnd_4687107 := by exact prefixLift 4687107
  have htrace : WordTrace (prefixWord ++ tailWord_4687107) baseStart_4687107 baseEnd_4687107 := by
    simpa [prefixWord, tailWord_4687107, baseEnd_4687107] using wordTrace_append hprefix tailTrace_4687107
  have hstable : (prefixWord ++ tailWord_4687107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687107).length < 2 ^ (prefixWord ++ tailWord_4687107).sum := by decide
  have hdescent : baseEnd_4687107 < baseStart_4687107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687118 : List Nat := [4, 1, 1, 2, 1, 5, 2, 2, 5]
def baseStart_4687118 : Nat := 118140960795 + 4687118 * 2 ^ 59
def prefixEnd_4687118 : Nat := 4983230072969 + 3 ^ 40 * 4687118 * 2
def baseEnd_4687118 : Nat := 267416046482277540329927

theorem tailTrace_4687118 : CollatzResearch.WordTrace tailWord_4687118 prefixEnd_4687118 267416046482277540329927 := by
  unfold tailWord_4687118
  simp only [CollatzResearch.WordTrace]
  refine ⟨21369154729172432108595751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113968825222252971245844005 21369154729172432108595751)
  ·
    refine ⟨32053732093758648162893627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21369154729172432108595751 32053732093758648162893627)
    ·
      refine ⟨48080598140637972244340441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32053732093758648162893627 48080598140637972244340441)
      ·
        refine ⟨36060448605478479183255331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48080598140637972244340441 36060448605478479183255331)
        ·
          refine ⟨54090672908217718774882997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36060448605478479183255331 54090672908217718774882997)
          ·
            refine ⟨5071000585145411135145281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54090672908217718774882997 5071000585145411135145281)
            ·
              refine ⟨3803250438859058351358961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5071000585145411135145281 3803250438859058351358961)
              ·
                refine ⟨2852437829144293763519221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3803250438859058351358961 2852437829144293763519221)
                ·
                  refine ⟨267416046482277540329927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2852437829144293763519221 267416046482277540329927)
                  ·
                    rfl

theorem cell23_4687118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2, 5].length) (baseStart_4687118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687118 prefixEnd_4687118 := by exact prefixLift 4687118
  have htrace : WordTrace (prefixWord ++ tailWord_4687118) baseStart_4687118 baseEnd_4687118 := by
    simpa [prefixWord, tailWord_4687118, baseEnd_4687118] using wordTrace_append hprefix tailTrace_4687118
  have hstable : (prefixWord ++ tailWord_4687118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687118).length < 2 ^ (prefixWord ++ tailWord_4687118).sum := by decide
  have hdescent : baseEnd_4687118 < baseStart_4687118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687177 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 1, 2, 6]
def baseStart_4687177 : Nat := 118140960795 + 4687177 * 2 ^ 59
def prefixEnd_4687177 : Nat := 4983230072969 + 3 ^ 40 * 4687177 * 2
def baseEnd_4687177 : Nat := 2406774713699113132131571

theorem tailTrace_4687177 : CollatzResearch.WordTrace tailWord_4687177 prefixEnd_4687177 2406774713699113132131571 := by
  unfold tailWord_4687177
  simp only [CollatzResearch.WordTrace]
  refine ⟨170955389740165709945163785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113970259826777139963442523 170955389740165709945163785)
  ·
    refine ⟨128216542305124282458872839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170955389740165709945163785 128216542305124282458872839)
    ·
      refine ⟨192324813457686423688309259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128216542305124282458872839 192324813457686423688309259)
      ·
        refine ⟨288487220186529635532463889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192324813457686423688309259 288487220186529635532463889)
        ·
          refine ⟨216365415139897226649347917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288487220186529635532463889 216365415139897226649347917)
          ·
            refine ⟨81137030677461459993505469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 216365415139897226649347917 81137030677461459993505469)
            ·
              refine ⟨30426386504048047497564551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81137030677461459993505469 30426386504048047497564551)
              ·
                refine ⟨45639579756072071246346827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30426386504048047497564551 45639579756072071246346827)
                ·
                  refine ⟨68459369634108106869520241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45639579756072071246346827 68459369634108106869520241)
                  ·
                    refine ⟨51344527225581080152140181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68459369634108106869520241 51344527225581080152140181)
                    ·
                      refine ⟨2406774713699113132131571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51344527225581080152140181 2406774713699113132131571)
                      ·
                        rfl

theorem cell23_4687177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 2, 6].length) (baseStart_4687177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687177 prefixEnd_4687177 := by exact prefixLift 4687177
  have htrace : WordTrace (prefixWord ++ tailWord_4687177) baseStart_4687177 baseEnd_4687177 := by
    simpa [prefixWord, tailWord_4687177, baseEnd_4687177] using wordTrace_append hprefix tailTrace_4687177
  have hstable : (prefixWord ++ tailWord_4687177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687177).length < 2 ^ (prefixWord ++ tailWord_4687177).sum := by decide
  have hdescent : baseEnd_4687177 < baseStart_4687177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687191 : List Nat := [1, 1, 3, 2, 3, 3, 3, 1, 6]
def baseStart_4687191 : Nat := 118140960795 + 4687191 * 2 ^ 59
def prefixEnd_4687191 : Nat := 4983230072969 + 3 ^ 40 * 4687191 * 2
def baseEnd_4687191 : Nat := 267420211380919564150723

theorem tailTrace_4687191 : CollatzResearch.WordTrace tailWord_4687191 prefixEnd_4687191 267420211380919564150723 := by
  unfold tailWord_4687191
  simp only [CollatzResearch.WordTrace]
  refine ⟨170955900362114990336173427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113970600241409993557448951 170955900362114990336173427)
  ·
    refine ⟨256433850543172485504260141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170955900362114990336173427 256433850543172485504260141)
    ·
      refine ⟨96162693953689682064097553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256433850543172485504260141 96162693953689682064097553)
      ·
        refine ⟨72122020465267261548073165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96162693953689682064097553 72122020465267261548073165)
        ·
          refine ⟨27045757674475223080527437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72122020465267261548073165 27045757674475223080527437)
          ·
            refine ⟨10142159127928208655197789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27045757674475223080527437 10142159127928208655197789)
            ·
              refine ⟨3803309672973078245699171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10142159127928208655197789 3803309672973078245699171)
              ·
                refine ⟨5704964509459617368548757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3803309672973078245699171 5704964509459617368548757)
                ·
                  refine ⟨267420211380919564150723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5704964509459617368548757 267420211380919564150723)
                  ·
                    rfl

theorem cell23_4687191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 6].length) (baseStart_4687191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687191 prefixEnd_4687191 := by exact prefixLift 4687191
  have htrace : WordTrace (prefixWord ++ tailWord_4687191) baseStart_4687191 baseEnd_4687191 := by
    simpa [prefixWord, tailWord_4687191, baseEnd_4687191] using wordTrace_append hprefix tailTrace_4687191
  have hstable : (prefixWord ++ tailWord_4687191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687191).length < 2 ^ (prefixWord ++ tailWord_4687191).sum := by decide
  have hdescent : baseEnd_4687191 < baseStart_4687191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687244 : List Nat := [2, 2, 1, 2, 1, 3, 1, 4, 1, 1, 5]
def baseStart_4687244 : Nat := 118140960795 + 4687244 * 2 ^ 59
def prefixEnd_4687244 : Nat := 4983230072969 + 3 ^ 40 * 4687244 * 2
def baseEnd_4687244 : Nat := 2406809116902964369993763

theorem tailTrace_4687244 : CollatzResearch.WordTrace tailWord_4687244 prefixEnd_4687244 2406809116902964369993763 := by
  unfold tailWord_4687244
  simp only [CollatzResearch.WordTrace]
  refine ⟨85478916715461490193926393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113971888953948653591901857 85478916715461490193926393)
  ·
    refine ⟨64109187536596117645444795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85478916715461490193926393 64109187536596117645444795)
    ·
      refine ⟨96163781304894176468167193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64109187536596117645444795 96163781304894176468167193)
      ·
        refine ⟨72122835978670632351125395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96163781304894176468167193 72122835978670632351125395)
        ·
          refine ⟨108184253968005948526688093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72122835978670632351125395 108184253968005948526688093)
          ·
            refine ⟨40569095238002230697508035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108184253968005948526688093 40569095238002230697508035)
            ·
              refine ⟨60853642857003346046262053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40569095238002230697508035 60853642857003346046262053)
              ·
                refine ⟨11410058035688127383674135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60853642857003346046262053 11410058035688127383674135)
                ·
                  refine ⟨17115087053532191075511203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11410058035688127383674135 17115087053532191075511203)
                  ·
                    refine ⟨25672630580298286613266805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17115087053532191075511203 25672630580298286613266805)
                    ·
                      refine ⟨2406809116902964369993763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25672630580298286613266805 2406809116902964369993763)
                      ·
                        rfl

theorem cell23_4687244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_4687244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687244 prefixEnd_4687244 := by exact prefixLift 4687244
  have htrace : WordTrace (prefixWord ++ tailWord_4687244) baseStart_4687244 baseEnd_4687244 := by
    simpa [prefixWord, tailWord_4687244, baseEnd_4687244] using wordTrace_append hprefix tailTrace_4687244
  have hstable : (prefixWord ++ tailWord_4687244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687244).length < 2 ^ (prefixWord ++ tailWord_4687244).sum := by decide
  have hdescent : baseEnd_4687244 < baseStart_4687244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687258 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2]
def baseStart_4687258 : Nat := 118140960795 + 4687258 * 2 ^ 59
def prefixEnd_4687258 : Nat := 4983230072969 + 3 ^ 40 * 4687258 * 2
def baseEnd_4687258 : Nat := 2406816305632127315218699

theorem tailTrace_4687258 : CollatzResearch.WordTrace tailWord_4687258 prefixEnd_4687258 2406816305632127315218699 := by
  unfold tailWord_4687258
  simp only [CollatzResearch.WordTrace]
  refine ⟨42739586013218065194715607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113972229368581507185908285 42739586013218065194715607)
  ·
    refine ⟨64109379019827097792073411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42739586013218065194715607 64109379019827097792073411)
    ·
      refine ⟨96164068529740646688110117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64109379019827097792073411 96164068529740646688110117)
      ·
        refine ⟨18030762849326371254020647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96164068529740646688110117 18030762849326371254020647)
        ·
          refine ⟨27046144273989556881030971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18030762849326371254020647 27046144273989556881030971)
          ·
            refine ⟨40569216410984335321546457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27046144273989556881030971 40569216410984335321546457)
            ·
              refine ⟨30426912308238251491159843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40569216410984335321546457 30426912308238251491159843)
              ·
                refine ⟨45640368462357377236739765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30426912308238251491159843 45640368462357377236739765)
                ·
                  refine ⟨4278784543346004115944353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45640368462357377236739765 4278784543346004115944353)
                  ·
                    refine ⟨3209088407509503086958265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4278784543346004115944353 3209088407509503086958265)
                    ·
                      refine ⟨2406816305632127315218699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3209088407509503086958265 2406816305632127315218699)
                      ·
                        rfl

theorem cell23_4687258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_4687258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687258 prefixEnd_4687258 := by exact prefixLift 4687258
  have htrace : WordTrace (prefixWord ++ tailWord_4687258) baseStart_4687258 baseEnd_4687258 := by
    simpa [prefixWord, tailWord_4687258, baseEnd_4687258] using wordTrace_append hprefix tailTrace_4687258
  have hstable : (prefixWord ++ tailWord_4687258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687258).length < 2 ^ (prefixWord ++ tailWord_4687258).sum := by decide
  have hdescent : baseEnd_4687258 < baseStart_4687258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687262 : List Nat := [4, 3, 1, 2, 2, 1, 2, 1, 2, 3, 2]
def baseStart_4687262 : Nat := 118140960795 + 4687262 * 2 ^ 59
def prefixEnd_4687262 : Nat := 4983230072969 + 3 ^ 40 * 4687262 * 2
def baseEnd_4687262 : Nat := 2406818359554745299568681

theorem tailTrace_4687262 : CollatzResearch.WordTrace tailWord_4687262 prefixEnd_4687262 2406818359554745299568681 := by
  unfold tailWord_4687262
  simp only [CollatzResearch.WordTrace]
  refine ⟨21369811243107221182751005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113972326629905179641338693 21369811243107221182751005)
  ·
    refine ⟨8013679216165207943531627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21369811243107221182751005 8013679216165207943531627)
    ·
      refine ⟨12020518824247811915297441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8013679216165207943531627 12020518824247811915297441)
      ·
        refine ⟨9015389118185858936473081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12020518824247811915297441 9015389118185858936473081)
        ·
          refine ⟨6761541838639394202354811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9015389118185858936473081 6761541838639394202354811)
          ·
            refine ⟨10142312757959091303532217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6761541838639394202354811 10142312757959091303532217)
            ·
              refine ⟨7606734568469318477649163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10142312757959091303532217 7606734568469318477649163)
              ·
                refine ⟨11410101852703977716473745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7606734568469318477649163 11410101852703977716473745)
                ·
                  refine ⟨8557576389527983287355309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11410101852703977716473745 8557576389527983287355309)
                  ·
                    refine ⟨3209091146072993732758241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8557576389527983287355309 3209091146072993732758241)
                    ·
                      refine ⟨2406818359554745299568681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3209091146072993732758241 2406818359554745299568681)
                      ·
                        rfl

theorem cell23_4687262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_4687262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687262 prefixEnd_4687262 := by exact prefixLift 4687262
  have htrace : WordTrace (prefixWord ++ tailWord_4687262) baseStart_4687262 baseEnd_4687262 := by
    simpa [prefixWord, tailWord_4687262, baseEnd_4687262] using wordTrace_append hprefix tailTrace_4687262
  have hstable : (prefixWord ++ tailWord_4687262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687262).length < 2 ^ (prefixWord ++ tailWord_4687262).sum := by decide
  have hdescent : baseEnd_4687262 < baseStart_4687262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687271 : List Nat := [1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_4687271 : Nat := 118140960795 + 4687271 * 2 ^ 59
def prefixEnd_4687271 : Nat := 4983230072969 + 3 ^ 40 * 4687271 * 2
def baseEnd_4687271 : Nat := 2406822980880635764356139

theorem tailTrace_4687271 : CollatzResearch.WordTrace tailWord_4687271 prefixEnd_4687271 2406822980880635764356139 := by
  unfold tailWord_4687271
  simp only [CollatzResearch.WordTrace]
  refine ⟨170958818201825163999085667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113972545467883442666057111 170958818201825163999085667)
  ·
    refine ⟨256438227302737745998628501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170958818201825163999085667 256438227302737745998628501)
    ·
      refine ⟨12020541904815831843685711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 256438227302737745998628501 12020541904815831843685711)
      ·
        refine ⟨18030812857223747765528567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12020541904815831843685711 18030812857223747765528567)
        ·
          refine ⟨27046219285835621648292851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18030812857223747765528567 27046219285835621648292851)
          ·
            refine ⟨40569328928753432472439277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27046219285835621648292851 40569328928753432472439277)
            ·
              refine ⟨15213498348282537177164729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40569328928753432472439277 15213498348282537177164729)
              ·
                refine ⟨11410123761211902882873547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15213498348282537177164729 11410123761211902882873547)
                ·
                  refine ⟨17115185641817854324310321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11410123761211902882873547 17115185641817854324310321)
                  ·
                    refine ⟨12836389231363390743232741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17115185641817854324310321 12836389231363390743232741)
                    ·
                      refine ⟨2406822980880635764356139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12836389231363390743232741 2406822980880635764356139)
                      ·
                        rfl

theorem cell23_4687271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_4687271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687271 prefixEnd_4687271 := by exact prefixLift 4687271
  have htrace : WordTrace (prefixWord ++ tailWord_4687271) baseStart_4687271 baseEnd_4687271 := by
    simpa [prefixWord, tailWord_4687271, baseEnd_4687271] using wordTrace_append hprefix tailTrace_4687271
  have hstable : (prefixWord ++ tailWord_4687271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687271).length < 2 ^ (prefixWord ++ tailWord_4687271).sum := by decide
  have hdescent : baseEnd_4687271 < baseStart_4687271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687308 : List Nat := [2, 2, 1, 4, 2, 2, 2, 1, 1, 3, 3]
def baseStart_4687308 : Nat := 118140960795 + 4687308 * 2 ^ 59
def prefixEnd_4687308 : Nat := 4983230072969 + 3 ^ 40 * 4687308 * 2
def baseEnd_4687308 : Nat := 2406841979664852119593469

theorem tailTrace_4687308 : CollatzResearch.WordTrace tailWord_4687308 prefixEnd_4687308 2406841979664852119593469 := by
  unfold tailWord_4687308
  simp only [CollatzResearch.WordTrace]
  refine ⟨85480083851345559659091289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113973445135127412878788385 85480083851345559659091289)
  ·
    refine ⟨64110062888509169744318467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85480083851345559659091289 64110062888509169744318467)
    ·
      refine ⟨96165094332763754616477701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64110062888509169744318467 96165094332763754616477701)
      ·
        refine ⟨18030955187393203990589569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96165094332763754616477701 18030955187393203990589569)
        ·
          refine ⟨13523216390544902992942177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18030955187393203990589569 13523216390544902992942177)
          ·
            refine ⟨10142412292908677244706633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13523216390544902992942177 10142412292908677244706633)
            ·
              refine ⟨7606809219681507933529975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10142412292908677244706633 7606809219681507933529975)
              ·
                refine ⟨11410213829522261900294963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7606809219681507933529975 11410213829522261900294963)
                ·
                  refine ⟨17115320744283392850442445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11410213829522261900294963 17115320744283392850442445)
                  ·
                    refine ⟨6418245279106272318915917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17115320744283392850442445 6418245279106272318915917)
                    ·
                      refine ⟨2406841979664852119593469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6418245279106272318915917 2406841979664852119593469)
                      ·
                        rfl

theorem cell23_4687308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_4687308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687308 prefixEnd_4687308 := by exact prefixLift 4687308
  have htrace : WordTrace (prefixWord ++ tailWord_4687308) baseStart_4687308 baseEnd_4687308 := by
    simpa [prefixWord, tailWord_4687308, baseEnd_4687308] using wordTrace_append hprefix tailTrace_4687308
  have hstable : (prefixWord ++ tailWord_4687308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687308).length < 2 ^ (prefixWord ++ tailWord_4687308).sum := by decide
  have hdescent : baseEnd_4687308 < baseStart_4687308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687335 : List Nat := [1, 1, 5, 2, 1, 3, 1, 3, 1, 3, 2]
def baseStart_4687335 : Nat := 118140960795 + 4687335 * 2 ^ 59
def prefixEnd_4687335 : Nat := 4983230072969 + 3 ^ 40 * 4687335 * 2
def baseEnd_4687335 : Nat := 2406855843642523513955845

theorem tailTrace_4687335 : CollatzResearch.WordTrace tailWord_4687335 prefixEnd_4687335 2406855843642523513955845 := by
  unfold tailWord_4687335
  simp only [CollatzResearch.WordTrace]
  refine ⟨170961152473593302929415459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113974101649062201952943639 170961152473593302929415459)
  ·
    refine ⟨256441728710389954394123189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170961152473593302929415459 256441728710389954394123189)
    ·
      refine ⟨24041412066599058224449049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 256441728710389954394123189 24041412066599058224449049)
      ·
        refine ⟨18031059049949293668336787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24041412066599058224449049 18031059049949293668336787)
        ·
          refine ⟨27046588574923940502505181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18031059049949293668336787 27046588574923940502505181)
          ·
            refine ⟨10142470715596477688439443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27046588574923940502505181 10142470715596477688439443)
            ·
              refine ⟨15213706073394716532659165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10142470715596477688439443 15213706073394716532659165)
              ·
                refine ⟨5705139777523018699747187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15213706073394716532659165 5705139777523018699747187)
                ·
                  refine ⟨8557709666284528049620781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5705139777523018699747187 8557709666284528049620781)
                  ·
                    refine ⟨3209141124856698018607793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8557709666284528049620781 3209141124856698018607793)
                    ·
                      refine ⟨2406855843642523513955845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3209141124856698018607793 2406855843642523513955845)
                      ·
                        rfl

theorem cell23_4687335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_4687335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687335 prefixEnd_4687335 := by exact prefixLift 4687335
  have htrace : WordTrace (prefixWord ++ tailWord_4687335) baseStart_4687335 baseEnd_4687335 := by
    simpa [prefixWord, tailWord_4687335, baseEnd_4687335] using wordTrace_append hprefix tailTrace_4687335
  have hstable : (prefixWord ++ tailWord_4687335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687335).length < 2 ^ (prefixWord ++ tailWord_4687335).sum := by decide
  have hdescent : baseEnd_4687335 < baseStart_4687335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687404 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 8]
def baseStart_4687404 : Nat := 118140960795 + 4687404 * 2 ^ 59
def prefixEnd_4687404 : Nat := 4983230072969 + 3 ^ 40 * 4687404 * 2
def baseEnd_4687404 : Nat := 2406891273807683743993027

theorem tailTrace_4687404 : CollatzResearch.WordTrace tailWord_4687404 prefixEnd_4687404 2406891273807683743993027 := by
  unfold tailWord_4687404
  simp only [CollatzResearch.WordTrace]
  refine ⟨85481834555171663856838633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113975779406895551809118177 85481834555171663856838633)
  ·
    refine ⟨64111375916378747892628975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85481834555171663856838633 64111375916378747892628975)
    ·
      refine ⟨96167063874568121838943463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64111375916378747892628975 96167063874568121838943463)
      ·
        refine ⟨144250595811852182758415195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96167063874568121838943463 144250595811852182758415195)
        ·
          refine ⟨216375893717778274137622793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144250595811852182758415195 216375893717778274137622793)
          ·
            refine ⟨162281920288333705603217095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216375893717778274137622793 162281920288333705603217095)
            ·
              refine ⟨243422880432500558404825643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162281920288333705603217095 243422880432500558404825643)
              ·
                refine ⟨365134320648750837607238465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243422880432500558404825643 365134320648750837607238465)
                ·
                  refine ⟨273850740486563128205428849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 365134320648750837607238465 273850740486563128205428849)
                  ·
                    refine ⟨205388055364922346154071637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 273850740486563128205428849 205388055364922346154071637)
                    ·
                      refine ⟨2406891273807683743993027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 205388055364922346154071637 2406891273807683743993027)
                      ·
                        rfl

theorem cell23_4687404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_4687404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687404 prefixEnd_4687404 := by exact prefixLift 4687404
  have htrace : WordTrace (prefixWord ++ tailWord_4687404) baseStart_4687404 baseEnd_4687404 := by
    simpa [prefixWord, tailWord_4687404, baseEnd_4687404] using wordTrace_append hprefix tailTrace_4687404
  have hstable : (prefixWord ++ tailWord_4687404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687404).length < 2 ^ (prefixWord ++ tailWord_4687404).sum := by decide
  have hdescent : baseEnd_4687404 < baseStart_4687404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687411 : List Nat := [1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 5]
def baseStart_4687411 : Nat := 118140960795 + 4687411 * 2 ^ 59
def prefixEnd_4687411 : Nat := 4983230072969 + 3 ^ 40 * 4687411 * 2
def baseEnd_4687411 : Nat := 2406894868172265216605495

theorem tailTrace_4687411 : CollatzResearch.WordTrace tailWord_4687411 prefixEnd_4687411 2406894868172265216605495 := by
  unfold tailWord_4687411
  simp only [CollatzResearch.WordTrace]
  refine ⟨170963924421317967909182087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113975949614211978606121391 170963924421317967909182087)
  ·
    refine ⟨256445886631976951863773131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170963924421317967909182087 256445886631976951863773131)
    ·
      refine ⟨384668829947965427795659697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256445886631976951863773131 384668829947965427795659697)
      ·
        refine ⟨288501622460974070846744773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 384668829947965427795659697 288501622460974070846744773)
        ·
          refine ⟨54094054211432638283764645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 288501622460974070846744773 54094054211432638283764645)
          ·
            refine ⟨10142635164643619678205871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54094054211432638283764645 10142635164643619678205871)
            ·
              refine ⟨15213952746965429517308807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10142635164643619678205871 15213952746965429517308807)
              ·
                refine ⟨22820929120448144275963211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15213952746965429517308807 22820929120448144275963211)
                ·
                  refine ⟨34231393680672216413944817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22820929120448144275963211 34231393680672216413944817)
                  ·
                    refine ⟨25673545260504162310458613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34231393680672216413944817 25673545260504162310458613)
                    ·
                      refine ⟨2406894868172265216605495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25673545260504162310458613 2406894868172265216605495)
                      ·
                        rfl

theorem cell23_4687411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 5].length) (baseStart_4687411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687411 prefixEnd_4687411 := by exact prefixLift 4687411
  have htrace : WordTrace (prefixWord ++ tailWord_4687411) baseStart_4687411 baseEnd_4687411 := by
    simpa [prefixWord, tailWord_4687411, baseEnd_4687411] using wordTrace_append hprefix tailTrace_4687411
  have hstable : (prefixWord ++ tailWord_4687411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687411).length < 2 ^ (prefixWord ++ tailWord_4687411).sum := by decide
  have hdescent : baseEnd_4687411 < baseStart_4687411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687438 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2]
def baseStart_4687438 : Nat := 118140960795 + 4687438 * 2 ^ 59
def prefixEnd_4687438 : Nat := 4983230072969 + 3 ^ 40 * 4687438 * 2
def baseEnd_4687438 : Nat := 2406908732149936610967871

theorem tailTrace_4687438 : CollatzResearch.WordTrace tailWord_4687438 prefixEnd_4687438 2406908732149936610967871 := by
  unfold tailWord_4687438
  simp only [CollatzResearch.WordTrace]
  refine ⟨21370613649027518940051871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113976606128146767680276645 21370613649027518940051871)
  ·
    refine ⟨32055920473541278410077807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21370613649027518940051871 32055920473541278410077807)
    ·
      refine ⟨48083880710311917615116711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32055920473541278410077807 48083880710311917615116711)
      ·
        refine ⟨72125821065467876422675067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48083880710311917615116711 72125821065467876422675067)
        ·
          refine ⟨108188731598201814634012601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72125821065467876422675067 108188731598201814634012601)
          ·
            refine ⟨81141548698651360975509451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108188731598201814634012601 81141548698651360975509451)
            ·
              refine ⟨121712323047977041463264177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81141548698651360975509451 121712323047977041463264177)
              ·
                refine ⟨91284242285982781097448133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121712323047977041463264177 91284242285982781097448133)
                ·
                  refine ⟨17115795428621771455771525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91284242285982781097448133 17115795428621771455771525)
                  ·
                    refine ⟨3209211642866582147957161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17115795428621771455771525 3209211642866582147957161)
                    ·
                      refine ⟨2406908732149936610967871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3209211642866582147957161 2406908732149936610967871)
                      ·
                        rfl

theorem cell23_4687438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2].length) (baseStart_4687438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687438 prefixEnd_4687438 := by exact prefixLift 4687438
  have htrace : WordTrace (prefixWord ++ tailWord_4687438) baseStart_4687438 baseEnd_4687438 := by
    simpa [prefixWord, tailWord_4687438, baseEnd_4687438] using wordTrace_append hprefix tailTrace_4687438
  have hstable : (prefixWord ++ tailWord_4687438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687438).length < 2 ^ (prefixWord ++ tailWord_4687438).sum := by decide
  have hdescent : baseEnd_4687438 < baseStart_4687438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687471 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 2, 5, 3]
def baseStart_4687471 : Nat := 118140960795 + 4687471 * 2 ^ 59
def prefixEnd_4687471 : Nat := 4983230072969 + 3 ^ 40 * 4687471 * 2
def baseEnd_4687471 : Nat := 2406925677011534981855219

theorem tailTrace_4687471 : CollatzResearch.WordTrace tailWord_4687471 prefixEnd_4687471 2406925677011534981855219 := by
  unfold tailWord_4687471
  simp only [CollatzResearch.WordTrace]
  refine ⟨170966112801100598156366267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113977408534067065437577511 170966112801100598156366267)
  ·
    refine ⟨256449169201650897234549401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170966112801100598156366267 256449169201650897234549401)
    ·
      refine ⟨192336876901238172925912051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256449169201650897234549401 192336876901238172925912051)
      ·
        refine ⟨288505315351857259388868077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192336876901238172925912051 288505315351857259388868077)
        ·
          refine ⟨108189493256946472270825529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 288505315351857259388868077 108189493256946472270825529)
          ·
            refine ⟨81142119942709854203119147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108189493256946472270825529 81142119942709854203119147)
            ·
              refine ⟨121713179914064781304678721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81142119942709854203119147 121713179914064781304678721)
              ·
                refine ⟨91284884935548585978509041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121713179914064781304678721 91284884935548585978509041)
                ·
                  refine ⟨68463663701661439483881781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91284884935548585978509041 68463663701661439483881781)
                  ·
                    refine ⟨6418468472030759951613917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68463663701661439483881781 6418468472030759951613917)
                    ·
                      refine ⟨2406925677011534981855219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6418468472030759951613917 2406925677011534981855219)
                      ·
                        rfl

theorem cell23_4687471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5, 3].length) (baseStart_4687471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687471 prefixEnd_4687471 := by exact prefixLift 4687471
  have htrace : WordTrace (prefixWord ++ tailWord_4687471) baseStart_4687471 baseEnd_4687471 := by
    simpa [prefixWord, tailWord_4687471, baseEnd_4687471] using wordTrace_append hprefix tailTrace_4687471
  have hstable : (prefixWord ++ tailWord_4687471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687471).length < 2 ^ (prefixWord ++ tailWord_4687471).sum := by decide
  have hdescent : baseEnd_4687471 < baseStart_4687471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687492 : List Nat := [2, 3, 2, 1, 4, 2, 1, 1, 2, 2, 3]
def baseStart_4687492 : Nat := 118140960795 + 4687492 * 2 ^ 59
def prefixEnd_4687492 : Nat := 4983230072969 + 3 ^ 40 * 4687492 * 2
def baseEnd_4687492 : Nat := 2406936460105279399692623

theorem tailTrace_4687492 : CollatzResearch.WordTrace tailWord_4687492 prefixEnd_4687492 2406936460105279399692623 := by
  unfold tailWord_4687492
  simp only [CollatzResearch.WordTrace]
  refine ⟨85483439367012259371440365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113977919156016345828587153 85483439367012259371440365)
  ·
    refine ⟨32056289762629597264290137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85483439367012259371440365 32056289762629597264290137)
    ·
      refine ⟨24042217321972197948217603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32056289762629597264290137 24042217321972197948217603)
      ·
        refine ⟨36063325982958296922326405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24042217321972197948217603 36063325982958296922326405)
        ·
          refine ⟨6761873621804680672936201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36063325982958296922326405 6761873621804680672936201)
          ·
            refine ⟨5071405216353510504702151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6761873621804680672936201 5071405216353510504702151)
            ·
              refine ⟨7607107824530265757053227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5071405216353510504702151 7607107824530265757053227)
              ·
                refine ⟨11410661736795398635579841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7607107824530265757053227 11410661736795398635579841)
                ·
                  refine ⟨8557996302596548976684881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11410661736795398635579841 8557996302596548976684881)
                  ·
                    refine ⟨6418497226947411732513661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8557996302596548976684881 6418497226947411732513661)
                    ·
                      refine ⟨2406936460105279399692623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6418497226947411732513661 2406936460105279399692623)
                      ·
                        rfl

theorem cell23_4687492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_4687492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687492 prefixEnd_4687492 := by exact prefixLift 4687492
  have htrace : WordTrace (prefixWord ++ tailWord_4687492) baseStart_4687492 baseEnd_4687492 := by
    simpa [prefixWord, tailWord_4687492, baseEnd_4687492] using wordTrace_append hprefix tailTrace_4687492
  have hstable : (prefixWord ++ tailWord_4687492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687492).length < 2 ^ (prefixWord ++ tailWord_4687492).sum := by decide
  have hdescent : baseEnd_4687492 < baseStart_4687492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687538 : List Nat := [3, 2, 1, 1, 1, 2, 5, 1, 1, 6]
def baseStart_4687538 : Nat := 118140960795 + 4687538 * 2 ^ 59
def prefixEnd_4687538 : Nat := 4983230072969 + 3 ^ 40 * 4687538 * 2
def baseEnd_4687538 : Nat := 802320026738462073239137

theorem tailTrace_4687538 : CollatzResearch.WordTrace tailWord_4687538 prefixEnd_4687538 802320026738462073239137 := by
  unfold tailWord_4687538
  simp only [CollatzResearch.WordTrace]
  refine ⟨42742139122964467149763817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113979037661238579066036845 42742139122964467149763817)
  ·
    refine ⟨32056604342223350362322863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42742139122964467149763817 32056604342223350362322863)
    ·
      refine ⟨48084906513335025543484295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32056604342223350362322863 48084906513335025543484295)
      ·
        refine ⟨72127359770002538315226443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48084906513335025543484295 72127359770002538315226443)
        ·
          refine ⟨108191039655003807472839665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72127359770002538315226443 108191039655003807472839665)
          ·
            refine ⟨81143279741252855604629749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108191039655003807472839665 81143279741252855604629749)
            ·
              refine ⟨7607182475742455212934039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81143279741252855604629749 7607182475742455212934039)
              ·
                refine ⟨11410773713613682819401059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7607182475742455212934039 11410773713613682819401059)
                ·
                  refine ⟨17116160570420524229101589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11410773713613682819401059 17116160570420524229101589)
                  ·
                    refine ⟨802320026738462073239137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17116160570420524229101589 802320026738462073239137)
                    ·
                      rfl

theorem cell23_4687538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_4687538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687538 prefixEnd_4687538 := by exact prefixLift 4687538
  have htrace : WordTrace (prefixWord ++ tailWord_4687538) baseStart_4687538 baseEnd_4687538 := by
    simpa [prefixWord, tailWord_4687538, baseEnd_4687538] using wordTrace_append hprefix tailTrace_4687538
  have hstable : (prefixWord ++ tailWord_4687538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687538).length < 2 ^ (prefixWord ++ tailWord_4687538).sum := by decide
  have hdescent : baseEnd_4687538 < baseStart_4687538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687542 : List Nat := [5, 1, 3, 1, 1, 1, 1, 4, 1, 5]
def baseStart_4687542 : Nat := 118140960795 + 4687542 * 2 ^ 59
def prefixEnd_4687542 : Nat := 4983230072969 + 3 ^ 40 * 4687542 * 2
def baseEnd_4687542 : Nat := 802320711379334734689131

theorem tailTrace_4687542 : CollatzResearch.WordTrace tailWord_4687542 prefixEnd_4687542 802320711379334734689131 := by
  unfold tailWord_4687542
  simp only [CollatzResearch.WordTrace]
  refine ⟨10685543898990211080137555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113979134922562251521467253 10685543898990211080137555)
  ·
    refine ⟨16028315848485316620206333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10685543898990211080137555 16028315848485316620206333)
    ·
      refine ⟨6010618443181993732577375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16028315848485316620206333 6010618443181993732577375)
      ·
        refine ⟨9015927664772990598866063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6010618443181993732577375 9015927664772990598866063)
        ·
          refine ⟨13523891497159485898299095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9015927664772990598866063 13523891497159485898299095)
          ·
            refine ⟨20285837245739228847448643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13523891497159485898299095 20285837245739228847448643)
            ·
              refine ⟨30428755868608843271172965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20285837245739228847448643 30428755868608843271172965)
              ·
                refine ⟨5705391725364158113344931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30428755868608843271172965 5705391725364158113344931)
                ·
                  refine ⟨8558087588046237170017397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5705391725364158113344931 8558087588046237170017397)
                  ·
                    refine ⟨802320711379334734689131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8558087588046237170017397 802320711379334734689131)
                    ·
                      rfl

theorem cell23_4687542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_4687542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687542 prefixEnd_4687542 := by exact prefixLift 4687542
  have htrace : WordTrace (prefixWord ++ tailWord_4687542) baseStart_4687542 baseEnd_4687542 := by
    simpa [prefixWord, tailWord_4687542, baseEnd_4687542] using wordTrace_append hprefix tailTrace_4687542
  have hstable : (prefixWord ++ tailWord_4687542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687542).length < 2 ^ (prefixWord ++ tailWord_4687542).sum := by decide
  have hdescent : baseEnd_4687542 < baseStart_4687542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687551 : List Nat := [1, 1, 2, 2, 2, 3, 3, 9]
def baseStart_4687551 : Nat := 118140960795 + 4687551 * 2 ^ 59
def prefixEnd_4687551 : Nat := 4983230072969 + 3 ^ 40 * 4687551 * 2
def baseEnd_4687551 : Nat := 89146916869033135883513

theorem tailTrace_4687551 : CollatzResearch.WordTrace tailWord_4687551 prefixEnd_4687551 89146916869033135883513 := by
  unfold tailWord_4687551
  simp only [CollatzResearch.WordTrace]
  refine ⟨170969030640810771819278507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113979353760540514546185671 170969030640810771819278507)
  ·
    refine ⟨256453545961216157728917761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170969030640810771819278507 256453545961216157728917761)
    ·
      refine ⟨192340159470912118296688321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256453545961216157728917761 192340159470912118296688321)
      ·
        refine ⟨144255119603184088722516241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192340159470912118296688321 144255119603184088722516241)
        ·
          refine ⟨108191339702388066541887181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144255119603184088722516241 108191339702388066541887181)
          ·
            refine ⟨40571752388395524953207693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108191339702388066541887181 40571752388395524953207693)
            ·
              refine ⟨15214407145648321857452885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40571752388395524953207693 15214407145648321857452885)
              ·
                refine ⟨89146916869033135883513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15214407145648321857452885 89146916869033135883513)
                ·
                  rfl

theorem cell23_4687551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 9].length) (baseStart_4687551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687551 prefixEnd_4687551 := by exact prefixLift 4687551
  have htrace : WordTrace (prefixWord ++ tailWord_4687551) baseStart_4687551 baseEnd_4687551 := by
    simpa [prefixWord, tailWord_4687551, baseEnd_4687551] using wordTrace_append hprefix tailTrace_4687551
  have hstable : (prefixWord ++ tailWord_4687551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687551).length < 2 ^ (prefixWord ++ tailWord_4687551).sum := by decide
  have hdescent : baseEnd_4687551 < baseStart_4687551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687611 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 3, 8]
def baseStart_4687611 : Nat := 118140960795 + 4687611 * 2 ^ 59
def prefixEnd_4687611 : Nat := 4983230072969 + 3 ^ 40 * 4687611 * 2
def baseEnd_4687611 : Nat := 802332521434388144701525

theorem tailTrace_4687611 : CollatzResearch.WordTrace tailWord_4687611 prefixEnd_4687611 802332521434388144701525 := by
  unfold tailWord_4687611
  simp only [CollatzResearch.WordTrace]
  refine ⟨170971219020593402066462687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113980812680395601377641791 170971219020593402066462687)
  ·
    refine ⟨256456828530890103099694031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170971219020593402066462687 256456828530890103099694031)
    ·
      refine ⟨384685242796335154649541047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256456828530890103099694031 384685242796335154649541047)
      ·
        refine ⟨577027864194502731974311571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384685242796335154649541047 577027864194502731974311571)
        ·
          refine ⟨865541796291754097961467357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 577027864194502731974311571 865541796291754097961467357)
          ·
            refine ⟨324578173609407786735550259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 865541796291754097961467357 324578173609407786735550259)
            ·
              refine ⟨486867260414111680103325389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324578173609407786735550259 486867260414111680103325389)
              ·
                refine ⟨182575222655291880038747021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 486867260414111680103325389 182575222655291880038747021)
                ·
                  refine ⟨68465708495734455014530133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 182575222655291880038747021 68465708495734455014530133)
                  ·
                    refine ⟨802332521434388144701525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68465708495734455014530133 802332521434388144701525)
                    ·
                      rfl

theorem cell23_4687611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 8].length) (baseStart_4687611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687611 prefixEnd_4687611 := by exact prefixLift 4687611
  have htrace : WordTrace (prefixWord ++ tailWord_4687611) baseStart_4687611 baseEnd_4687611 := by
    simpa [prefixWord, tailWord_4687611, baseEnd_4687611] using wordTrace_append hprefix tailTrace_4687611
  have hstable : (prefixWord ++ tailWord_4687611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687611).length < 2 ^ (prefixWord ++ tailWord_4687611).sum := by decide
  have hdescent : baseEnd_4687611 < baseStart_4687611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687636 : List Nat := [2, 4, 4, 1, 2, 1, 1, 8]
def baseStart_4687636 : Nat := 118140960795 + 4687636 * 2 ^ 59
def prefixEnd_4687636 : Nat := 4983230072969 + 3 ^ 40 * 4687636 * 2
def baseEnd_4687636 : Nat := 89148533382204697640443

theorem tailTrace_4687636 : CollatzResearch.WordTrace tailWord_4687636 prefixEnd_4687636 89148533382204697640443 := by
  unfold tailWord_4687636
  simp only [CollatzResearch.WordTrace]
  refine ⟨85486065422751415668061381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113981420563668554224081841 85486065422751415668061381)
  ·
    refine ⟨16028637266765890437761509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85486065422751415668061381 16028637266765890437761509)
    ·
      refine ⟨3005369487518604457080283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16028637266765890437761509 3005369487518604457080283)
      ·
        refine ⟨4508054231277906685620425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3005369487518604457080283 4508054231277906685620425)
        ·
          refine ⟨3381040673458430014215319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4508054231277906685620425 3381040673458430014215319)
          ·
            refine ⟨5071561010187645021322979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3381040673458430014215319 5071561010187645021322979)
            ·
              refine ⟨7607341515281467531984469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5071561010187645021322979 7607341515281467531984469)
              ·
                refine ⟨89148533382204697640443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7607341515281467531984469 89148533382204697640443)
                ·
                  rfl

theorem cell23_4687636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 8].length) (baseStart_4687636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687636 prefixEnd_4687636 := by exact prefixLift 4687636
  have htrace : WordTrace (prefixWord ++ tailWord_4687636) baseStart_4687636 baseEnd_4687636 := by
    simpa [prefixWord, tailWord_4687636, baseEnd_4687636] using wordTrace_append hprefix tailTrace_4687636
  have hstable : (prefixWord ++ tailWord_4687636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687636).length < 2 ^ (prefixWord ++ tailWord_4687636).sum := by decide
  have hdescent : baseEnd_4687636 < baseStart_4687636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687646 : List Nat := [4, 3, 2, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_4687646 : Nat := 118140960795 + 4687646 * 2 ^ 59
def prefixEnd_4687646 : Nat := 4983230072969 + 3 ^ 40 * 4687646 * 2
def baseEnd_4687646 : Nat := 2407015536126071797166915

theorem tailTrace_4687646 : CollatzResearch.WordTrace tailWord_4687646 prefixEnd_4687646 2407015536126071797166915 := by
  unfold tailWord_4687646
  simp only [CollatzResearch.WordTrace]
  refine ⟨21371561946933325380498349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113981663716977735362657861 21371561946933325380498349)
  ·
    refine ⟨8014335730099997017686881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21371561946933325380498349 8014335730099997017686881)
    ·
      refine ⟨6010751797574997763265161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8014335730099997017686881 6010751797574997763265161)
      ·
        refine ⟨4508063848181248322448871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6010751797574997763265161 4508063848181248322448871)
        ·
          refine ⟨6762095772271872483673307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4508063848181248322448871 6762095772271872483673307)
          ·
            refine ⟨10143143658407808725509961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6762095772271872483673307 10143143658407808725509961)
            ·
              refine ⟨7607357743805856544132471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10143143658407808725509961 7607357743805856544132471)
              ·
                refine ⟨11411036615708784816198707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7607357743805856544132471 11411036615708784816198707)
                ·
                  refine ⟨17116554923563177224298061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11411036615708784816198707 17116554923563177224298061)
                  ·
                    refine ⟨6418708096336191459111773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17116554923563177224298061 6418708096336191459111773)
                    ·
                      refine ⟨2407015536126071797166915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6418708096336191459111773 2407015536126071797166915)
                      ·
                        rfl

theorem cell23_4687646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_4687646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687646 prefixEnd_4687646 := by exact prefixLift 4687646
  have htrace : WordTrace (prefixWord ++ tailWord_4687646) baseStart_4687646 baseEnd_4687646 := by
    simpa [prefixWord, tailWord_4687646, baseEnd_4687646] using wordTrace_append hprefix tailTrace_4687646
  have hstable : (prefixWord ++ tailWord_4687646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687646).length < 2 ^ (prefixWord ++ tailWord_4687646).sum := by decide
  have hdescent : baseEnd_4687646 < baseStart_4687646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687652 : List Nat := [2, 3, 1, 3, 2, 1, 1, 3, 1, 4, 2]
def baseStart_4687652 : Nat := 118140960795 + 4687652 * 2 ^ 59
def prefixEnd_4687652 : Nat := 4983230072969 + 3 ^ 40 * 4687652 * 2
def baseEnd_4687652 : Nat := 2407018617009998773691887

theorem tailTrace_4687652 : CollatzResearch.WordTrace tailWord_4687652 prefixEnd_4687652 2407018617009998773691887 := by
  unfold tailWord_4687652
  simp only [CollatzResearch.WordTrace]
  refine ⟨85486357206722433034352605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113981809608963244045803473 85486357206722433034352605)
  ·
    refine ⟨32057383952520912387882227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85486357206722433034352605 32057383952520912387882227)
    ·
      refine ⟨48086075928781368581823341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32057383952520912387882227 48086075928781368581823341)
      ·
        refine ⟨18032278473293013218183753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48086075928781368581823341 18032278473293013218183753)
        ·
          refine ⟨13524208854969759913637815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18032278473293013218183753 13524208854969759913637815)
          ·
            refine ⟨20286313282454639870456723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13524208854969759913637815 20286313282454639870456723)
            ·
              refine ⟨30429469923681959805685085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20286313282454639870456723 30429469923681959805685085)
              ·
                refine ⟨11411051221380734927131907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30429469923681959805685085 11411051221380734927131907)
                ·
                  refine ⟨17116576832071102390697861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11411051221380734927131907 17116576832071102390697861)
                  ·
                    refine ⟨3209358156013331698255849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17116576832071102390697861 3209358156013331698255849)
                    ·
                      refine ⟨2407018617009998773691887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3209358156013331698255849 2407018617009998773691887)
                      ·
                        rfl

theorem cell23_4687652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_4687652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687652 prefixEnd_4687652 := by exact prefixLift 4687652
  have htrace : WordTrace (prefixWord ++ tailWord_4687652) baseStart_4687652 baseEnd_4687652 := by
    simpa [prefixWord, tailWord_4687652, baseEnd_4687652] using wordTrace_append hprefix tailTrace_4687652
  have hstable : (prefixWord ++ tailWord_4687652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687652).length < 2 ^ (prefixWord ++ tailWord_4687652).sum := by decide
  have hdescent : baseEnd_4687652 < baseStart_4687652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687673 : List Nat := [1, 2, 1, 7, 1, 2, 2, 1, 1, 3, 2]
def baseStart_4687673 : Nat := 118140960795 + 4687673 * 2 ^ 59
def prefixEnd_4687673 : Nat := 4983230072969 + 3 ^ 40 * 4687673 * 2
def baseEnd_4687673 : Nat := 2407029400103743191529291

theorem tailTrace_4687673 : CollatzResearch.WordTrace tailWord_4687673 prefixEnd_4687673 2407029400103743191529291 := by
  unfold tailWord_4687673
  simp only [CollatzResearch.WordTrace]
  refine ⟨170973480346368786655219673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113982320230912524436813115 170973480346368786655219673)
  ·
    refine ⟨128230110259776589991414755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170973480346368786655219673 128230110259776589991414755)
    ·
      refine ⟨192345165389664884987122133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128230110259776589991414755 192345165389664884987122133)
      ·
        refine ⟨4508089813820270741885675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 192345165389664884987122133 4508089813820270741885675)
        ·
          refine ⟨6762134720730406112828513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4508089813820270741885675 6762134720730406112828513)
          ·
            refine ⟨5071601040547804584621385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6762134720730406112828513 5071601040547804584621385)
            ·
              refine ⟨3803700780410853438466039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5071601040547804584621385 3803700780410853438466039)
              ·
                refine ⟨5705551170616280157699059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3803700780410853438466039 5705551170616280157699059)
                ·
                  refine ⟨8558326755924420236548589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5705551170616280157699059 8558326755924420236548589)
                  ·
                    refine ⟨3209372533471657588705721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8558326755924420236548589 3209372533471657588705721)
                    ·
                      refine ⟨2407029400103743191529291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3209372533471657588705721 2407029400103743191529291)
                      ·
                        rfl

theorem cell23_4687673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_4687673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687673 prefixEnd_4687673 := by exact prefixLift 4687673
  have htrace : WordTrace (prefixWord ++ tailWord_4687673) baseStart_4687673 baseEnd_4687673 := by
    simpa [prefixWord, tailWord_4687673, baseEnd_4687673] using wordTrace_append hprefix tailTrace_4687673
  have hstable : (prefixWord ++ tailWord_4687673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687673).length < 2 ^ (prefixWord ++ tailWord_4687673).sum := by decide
  have hdescent : baseEnd_4687673 < baseStart_4687673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687725 : List Nat := [1, 5, 1, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_4687725 : Nat := 118140960795 + 4687725 * 2 ^ 59
def prefixEnd_4687725 : Nat := 4983230072969 + 3 ^ 40 * 4687725 * 2
def baseEnd_4687725 : Nat := 2407056101097776988079051

theorem tailTrace_4687725 : CollatzResearch.WordTrace tailWord_4687725 prefixEnd_4687725 2407056101097776988079051 := by
  unfold tailWord_4687725
  simp only [CollatzResearch.WordTrace]
  refine ⟨170975376942180399536112629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113983584628120266357408419 170975376942180399536112629)
  ·
    refine ⟨16028941588329412456510559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 170975376942180399536112629 16028941588329412456510559)
    ·
      refine ⟨24043412382494118684765839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16028941588329412456510559 24043412382494118684765839)
      ·
        refine ⟨36065118573741178027148759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24043412382494118684765839 36065118573741178027148759)
        ·
          refine ⟨54097677860611767040723139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36065118573741178027148759 54097677860611767040723139)
          ·
            refine ⟨81146516790917650561084709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54097677860611767040723139 81146516790917650561084709)
            ·
              refine ⟨15214971898297059480203383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81146516790917650561084709 15214971898297059480203383)
              ·
                refine ⟨22822457847445589220305075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15214971898297059480203383 22822457847445589220305075)
                ·
                  refine ⟨34233686771168383830457613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22822457847445589220305075 34233686771168383830457613)
                  ·
                    refine ⟨12837632539188143936421605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34233686771168383830457613 12837632539188143936421605)
                    ·
                      refine ⟨2407056101097776988079051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12837632539188143936421605 2407056101097776988079051)
                      ·
                        rfl

theorem cell23_4687725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_4687725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687725 prefixEnd_4687725 := by exact prefixLift 4687725
  have htrace : WordTrace (prefixWord ++ tailWord_4687725) baseStart_4687725 baseEnd_4687725 := by
    simpa [prefixWord, tailWord_4687725, baseEnd_4687725] using wordTrace_append hprefix tailTrace_4687725
  have hstable : (prefixWord ++ tailWord_4687725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687725).length < 2 ^ (prefixWord ++ tailWord_4687725).sum := by decide
  have hdescent : baseEnd_4687725 < baseStart_4687725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687728 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 5]
def baseStart_4687728 : Nat := 118140960795 + 4687728 * 2 ^ 59
def prefixEnd_4687728 : Nat := 4983230072969 + 3 ^ 40 * 4687728 * 2
def baseEnd_4687728 : Nat := 2407057641539740476341537

theorem tailTrace_4687728 : CollatzResearch.WordTrace tailWord_4687728 prefixEnd_4687728 2407057641539740476341537 := by
  unfold tailWord_4687728
  simp only [CollatzResearch.WordTrace]
  refine ⟨85487743180584765524235919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113983657574113020698981225 85487743180584765524235919)
  ·
    refine ⟨128231614770877148286353879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85487743180584765524235919 128231614770877148286353879)
    ·
      refine ⟨192347422156315722429530819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128231614770877148286353879 192347422156315722429530819)
      ·
        refine ⟨288521133234473583644296229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192347422156315722429530819 288521133234473583644296229)
        ·
          refine ⟨54097712481463796933305543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 288521133234473583644296229 54097712481463796933305543)
          ·
            refine ⟨81146568722195695399958315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54097712481463796933305543 81146568722195695399958315)
            ·
              refine ⟨121719853083293543099937473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81146568722195695399958315 121719853083293543099937473)
              ·
                refine ⟨91289889812470157324953105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121719853083293543099937473 91289889812470157324953105)
                ·
                  refine ⟨68467417359352617993714829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91289889812470157324953105 68467417359352617993714829)
                  ·
                    refine ⟨25675281509757231747643061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68467417359352617993714829 25675281509757231747643061)
                    ·
                      refine ⟨2407057641539740476341537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25675281509757231747643061 2407057641539740476341537)
                      ·
                        rfl

theorem cell23_4687728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 5].length) (baseStart_4687728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687728 prefixEnd_4687728 := by exact prefixLift 4687728
  have htrace : WordTrace (prefixWord ++ tailWord_4687728) baseStart_4687728 baseEnd_4687728 := by
    simpa [prefixWord, tailWord_4687728, baseEnd_4687728] using wordTrace_append hprefix tailTrace_4687728
  have hstable : (prefixWord ++ tailWord_4687728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687728).length < 2 ^ (prefixWord ++ tailWord_4687728).sum := by decide
  have hdescent : baseEnd_4687728 < baseStart_4687728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687738 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6]
def baseStart_4687738 : Nat := 118140960795 + 4687738 * 2 ^ 59
def prefixEnd_4687738 : Nat := 4983230072969 + 3 ^ 40 * 4687738 * 2
def baseEnd_4687738 : Nat := 2407062776346285437216491

theorem tailTrace_4687738 : CollatzResearch.WordTrace tailWord_4687738 prefixEnd_4687738 2407062776346285437216491 := by
  unfold tailWord_4687738
  simp only [CollatzResearch.WordTrace]
  refine ⟨42743962772783325689083967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113983900727422201837557245 42743962772783325689083967)
  ·
    refine ⟨64115944159174988533625951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42743962772783325689083967 64115944159174988533625951)
    ·
      refine ⟨96173916238762482800438927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64115944159174988533625951 96173916238762482800438927)
      ·
        refine ⟨144260874358143724200658391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96173916238762482800438927 144260874358143724200658391)
        ·
          refine ⟨216391311537215586300987587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144260874358143724200658391 216391311537215586300987587)
          ·
            refine ⟨324586967305823379451481381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216391311537215586300987587 324586967305823379451481381)
            ·
              refine ⟨60860056369841883647152759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 324586967305823379451481381 60860056369841883647152759)
              ·
                refine ⟨91290084554762825470729139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60860056369841883647152759 91290084554762825470729139)
                ·
                  refine ⟨136935126832144238206093709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91290084554762825470729139 136935126832144238206093709)
                  ·
                    refine ⟨51350672562054089327285141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 136935126832144238206093709 51350672562054089327285141)
                    ·
                      refine ⟨2407062776346285437216491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51350672562054089327285141 2407062776346285437216491)
                      ·
                        rfl

theorem cell23_4687738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_4687738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687738 prefixEnd_4687738 := by exact prefixLift 4687738
  have htrace : WordTrace (prefixWord ++ tailWord_4687738) baseStart_4687738 baseEnd_4687738 := by
    simpa [prefixWord, tailWord_4687738, baseEnd_4687738] using wordTrace_append hprefix tailTrace_4687738
  have hstable : (prefixWord ++ tailWord_4687738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687738).length < 2 ^ (prefixWord ++ tailWord_4687738).sum := by decide
  have hdescent : baseEnd_4687738 < baseStart_4687738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687765 : List Nat := [1, 3, 2, 1, 1, 3, 3, 3, 6]
def baseStart_4687765 : Nat := 118140960795 + 4687765 * 2 ^ 59
def prefixEnd_4687765 : Nat := 4983230072969 + 3 ^ 40 * 4687765 * 2
def baseEnd_4687765 : Nat := 267452960035995203508763

theorem tailTrace_4687765 : CollatzResearch.WordTrace tailWord_4687765 prefixEnd_4687765 267452960035995203508763 := by
  unfold tailWord_4687765
  simp only [CollatzResearch.WordTrace]
  refine ⟨170976835862035486367568749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113984557241356990911712499 170976835862035486367568749)
  ·
    refine ⟨64116313448263307387838281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170976835862035486367568749 64116313448263307387838281)
    ·
      refine ⟨48087235086197480540878711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64116313448263307387838281 48087235086197480540878711)
      ·
        refine ⟨72130852629296220811318067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48087235086197480540878711 72130852629296220811318067)
        ·
          refine ⟨108196278943944331216977101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72130852629296220811318067 108196278943944331216977101)
          ·
            refine ⟨40573604603979124206366413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108196278943944331216977101 40573604603979124206366413)
            ·
              refine ⟨15215101726492171577387405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40573604603979124206366413 15215101726492171577387405)
              ·
                refine ⟨5705663147434564341520277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15215101726492171577387405 5705663147434564341520277)
                ·
                  refine ⟨267452960035995203508763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5705663147434564341520277 267452960035995203508763)
                  ·
                    rfl

theorem cell23_4687765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 6].length) (baseStart_4687765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687765 prefixEnd_4687765 := by exact prefixLift 4687765
  have htrace : WordTrace (prefixWord ++ tailWord_4687765) baseStart_4687765 baseEnd_4687765 := by
    simpa [prefixWord, tailWord_4687765, baseEnd_4687765] using wordTrace_append hprefix tailTrace_4687765
  have hstable : (prefixWord ++ tailWord_4687765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687765).length < 2 ^ (prefixWord ++ tailWord_4687765).sum := by decide
  have hdescent : baseEnd_4687765 < baseStart_4687765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687802 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2]
def baseStart_4687802 : Nat := 118140960795 + 4687802 * 2 ^ 59
def prefixEnd_4687802 : Nat := 4983230072969 + 3 ^ 40 * 4687802 * 2
def baseEnd_4687802 : Nat := 2407095639108173186816197

theorem tailTrace_4687802 : CollatzResearch.WordTrace tailWord_4687802 prefixEnd_4687802 2407095639108173186816197 := by
  unfold tailWord_4687802
  simp only [CollatzResearch.WordTrace]
  refine ⟨42744546340725360421666415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113985456908600961124443773 42744546340725360421666415)
  ·
    refine ⟨64116819511088040632499623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42744546340725360421666415 64116819511088040632499623)
    ·
      refine ⟨96175229266632060948749435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64116819511088040632499623 96175229266632060948749435)
      ·
        refine ⟨144262843899948091423124153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96175229266632060948749435 144262843899948091423124153)
        ·
          refine ⟨108197132924961068567343115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144262843899948091423124153 108197132924961068567343115)
          ·
            refine ⟨162295699387441602851014673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108197132924961068567343115 162295699387441602851014673)
            ·
              refine ⟨121721774540581202138261005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162295699387441602851014673 121721774540581202138261005)
              ·
                refine ⟨45645665452717950801847877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121721774540581202138261005 45645665452717950801847877)
                ·
                  refine ⟨8558562272384615775346477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45645665452717950801847877 8558562272384615775346477)
                  ·
                    refine ⟨3209460852144230915754929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8558562272384615775346477 3209460852144230915754929)
                    ·
                      refine ⟨2407095639108173186816197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3209460852144230915754929 2407095639108173186816197)
                      ·
                        rfl

theorem cell23_4687802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2].length) (baseStart_4687802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687802 prefixEnd_4687802 := by exact prefixLift 4687802
  have htrace : WordTrace (prefixWord ++ tailWord_4687802) baseStart_4687802 baseEnd_4687802 := by
    simpa [prefixWord, tailWord_4687802, baseEnd_4687802] using wordTrace_append hprefix tailTrace_4687802
  have hstable : (prefixWord ++ tailWord_4687802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687802).length < 2 ^ (prefixWord ++ tailWord_4687802).sum := by decide
  have hdescent : baseEnd_4687802 < baseStart_4687802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687826 : List Nat := [3, 2, 2, 3, 2, 1, 1, 2, 3, 1, 3]
def baseStart_4687826 : Nat := 118140960795 + 4687826 * 2 ^ 59
def prefixEnd_4687826 : Nat := 4983230072969 + 3 ^ 40 * 4687826 * 2
def baseEnd_4687826 : Nat := 2407107962643881092916087

theorem tailTrace_4687826 : CollatzResearch.WordTrace tailWord_4687826 prefixEnd_4687826 2407107962643881092916087 := by
  unfold tailWord_4687826
  simp only [CollatzResearch.WordTrace]
  refine ⟨42744765178703623446384833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113986040476542995857026221 42744765178703623446384833)
  ·
    refine ⟨32058573884027717584788625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42744765178703623446384833 32058573884027717584788625)
    ·
      refine ⟨24043930413020788188591469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32058573884027717584788625 24043930413020788188591469)
      ·
        refine ⟨9016473904882795570721801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24043930413020788188591469 9016473904882795570721801)
        ·
          refine ⟨6762355428662096678041351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9016473904882795570721801 6762355428662096678041351)
          ·
            refine ⟨10143533142993145017062027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6762355428662096678041351 10143533142993145017062027)
            ·
              refine ⟨15215299714489717525593041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10143533142993145017062027 15215299714489717525593041)
              ·
                refine ⟨11411474785867288144194781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15215299714489717525593041 11411474785867288144194781)
                ·
                  refine ⟨4279303044700233054073043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11411474785867288144194781 4279303044700233054073043)
                  ·
                    refine ⟨6418954567050349581109565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4279303044700233054073043 6418954567050349581109565)
                    ·
                      refine ⟨2407107962643881092916087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6418954567050349581109565 2407107962643881092916087)
                      ·
                        rfl

theorem cell23_4687826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_4687826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687826 prefixEnd_4687826 := by exact prefixLift 4687826
  have htrace : WordTrace (prefixWord ++ tailWord_4687826) baseStart_4687826 baseEnd_4687826 := by
    simpa [prefixWord, tailWord_4687826, baseEnd_4687826] using wordTrace_append hprefix tailTrace_4687826
  have hstable : (prefixWord ++ tailWord_4687826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687826).length < 2 ^ (prefixWord ++ tailWord_4687826).sum := by decide
  have hdescent : baseEnd_4687826 < baseStart_4687826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687832 : List Nat := [2, 1, 2, 2, 2, 2, 2, 4, 1, 1, 4]
def baseStart_4687832 : Nat := 118140960795 + 4687832 * 2 ^ 59
def prefixEnd_4687832 : Nat := 4983230072969 + 3 ^ 40 * 4687832 * 2
def baseEnd_4687832 : Nat := 2407111043527808069441059

theorem tailTrace_4687832 : CollatzResearch.WordTrace tailWord_4687832 prefixEnd_4687832 2407111043527808069441059 := by
  unfold tailWord_4687832
  simp only [CollatzResearch.WordTrace]
  refine ⟨85489639776396378405128875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113986186368528504540171833 85489639776396378405128875)
  ·
    refine ⟨128234459664594567607693313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85489639776396378405128875 128234459664594567607693313)
    ·
      refine ⟨96175844748445925705769985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128234459664594567607693313 96175844748445925705769985)
      ·
        refine ⟨72131883561334444279327489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96175844748445925705769985 72131883561334444279327489)
        ·
          refine ⟨54098912671000833209495617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72131883561334444279327489 54098912671000833209495617)
          ·
            refine ⟨40574184503250624907121713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54098912671000833209495617 40574184503250624907121713)
            ·
              refine ⟨30430638377437968680341285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40574184503250624907121713 30430638377437968680341285)
              ·
                refine ⟨5705744695769619127563991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30430638377437968680341285 5705744695769619127563991)
                ·
                  refine ⟨8558617043654428691345987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5705744695769619127563991 8558617043654428691345987)
                  ·
                    refine ⟨12837925565481643037018981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8558617043654428691345987 12837925565481643037018981)
                    ·
                      refine ⟨2407111043527808069441059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12837925565481643037018981 2407111043527808069441059)
                      ·
                        rfl

theorem cell23_4687832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_4687832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687832 prefixEnd_4687832 := by exact prefixLift 4687832
  have htrace : WordTrace (prefixWord ++ tailWord_4687832) baseStart_4687832 baseEnd_4687832 := by
    simpa [prefixWord, tailWord_4687832, baseEnd_4687832] using wordTrace_append hprefix tailTrace_4687832
  have hstable : (prefixWord ++ tailWord_4687832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687832).length < 2 ^ (prefixWord ++ tailWord_4687832).sum := by decide
  have hdescent : baseEnd_4687832 < baseStart_4687832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687876 : List Nat := [2, 3, 2, 4, 1, 2, 1, 1, 1, 6]
def baseStart_4687876 : Nat := 118140960795 + 4687876 * 2 ^ 59
def prefixEnd_4687876 : Nat := 4983230072969 + 3 ^ 40 * 4687876 * 2
def baseEnd_4687876 : Nat := 802377878892201965763619

theorem tailTrace_4687876 : CollatzResearch.WordTrace tailWord_4687876 prefixEnd_4687876 802377878892201965763619 := by
  unfold tailWord_4687876
  simp only [CollatzResearch.WordTrace]
  refine ⟨85490442182316676162429741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113987256243088901549906321 85490442182316676162429741)
  ·
    refine ⟨32058915818368753560911153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85490442182316676162429741 32058915818368753560911153)
    ·
      refine ⟨24044186863776565170683365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32058915818368753560911153 24044186863776565170683365)
      ·
        refine ⟨4508285036958105969503131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24044186863776565170683365 4508285036958105969503131)
        ·
          refine ⟨6762427555437158954254697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4508285036958105969503131 6762427555437158954254697)
          ·
            refine ⟨5071820666577869215691023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6762427555437158954254697 5071820666577869215691023)
            ·
              refine ⟨7607730999866803823536535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5071820666577869215691023 7607730999866803823536535)
              ·
                refine ⟨11411596499800205735304803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7607730999866803823536535 11411596499800205735304803)
                ·
                  refine ⟨17117394749700308602957205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11411596499800205735304803 17117394749700308602957205)
                  ·
                    refine ⟨802377878892201965763619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17117394749700308602957205 802377878892201965763619)
                    ·
                      rfl

theorem cell23_4687876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_4687876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687876 prefixEnd_4687876 := by exact prefixLift 4687876
  have htrace : WordTrace (prefixWord ++ tailWord_4687876) baseStart_4687876 baseEnd_4687876 := by
    simpa [prefixWord, tailWord_4687876, baseEnd_4687876] using wordTrace_append hprefix tailTrace_4687876
  have hstable : (prefixWord ++ tailWord_4687876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687876).length < 2 ^ (prefixWord ++ tailWord_4687876).sum := by decide
  have hdescent : baseEnd_4687876 < baseStart_4687876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687879 : List Nat := [1, 1, 4, 3, 1, 4, 1, 1, 1, 2, 4]
def baseStart_4687879 : Nat := 118140960795 + 4687879 * 2 ^ 59
def prefixEnd_4687879 : Nat := 4983230072969 + 3 ^ 40 * 4687879 * 2
def baseEnd_4687879 : Nat := 2407135177118569385553343

theorem tailTrace_4687879 : CollatzResearch.WordTrace tailWord_4687879 prefixEnd_4687879 2407135177118569385553343 := by
  unfold tailWord_4687879
  simp only [CollatzResearch.WordTrace]
  refine ⟨170980993783622483837218691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113987329189081655891479127 170980993783622483837218691)
  ·
    refine ⟨256471490675433725755828037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170980993783622483837218691 256471490675433725755828037)
    ·
      refine ⟨48088404501643823579217757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 256471490675433725755828037 48088404501643823579217757)
      ·
        refine ⟨18033151688116433842206659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48088404501643823579217757 18033151688116433842206659)
        ·
          refine ⟨27049727532174650763309989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18033151688116433842206659 27049727532174650763309989)
          ·
            refine ⟨5071823912282747018120623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27049727532174650763309989 5071823912282747018120623)
            ·
              refine ⟨7607735868424120527180935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5071823912282747018120623 7607735868424120527180935)
              ·
                refine ⟨11411603802636180790771403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7607735868424120527180935 11411603802636180790771403)
                ·
                  refine ⟨17117405703954271186157105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11411603802636180790771403 17117405703954271186157105)
                  ·
                    refine ⟨12838054277965703389617829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17117405703954271186157105 12838054277965703389617829)
                    ·
                      refine ⟨2407135177118569385553343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12838054277965703389617829 2407135177118569385553343)
                      ·
                        rfl

theorem cell23_4687879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_4687879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687879 prefixEnd_4687879 := by exact prefixLift 4687879
  have htrace : WordTrace (prefixWord ++ tailWord_4687879) baseStart_4687879 baseEnd_4687879 := by
    simpa [prefixWord, tailWord_4687879, baseEnd_4687879] using wordTrace_append hprefix tailTrace_4687879
  have hstable : (prefixWord ++ tailWord_4687879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687879).length < 2 ^ (prefixWord ++ tailWord_4687879).sum := by decide
  have hdescent : baseEnd_4687879 < baseStart_4687879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687900 : List Nat := [2, 2, 3, 1, 3, 3, 1, 3, 1, 2, 2]
def baseStart_4687900 : Nat := 118140960795 + 4687900 * 2 ^ 59
def prefixEnd_4687900 : Nat := 4983230072969 + 3 ^ 40 * 4687900 * 2
def baseEnd_4687900 : Nat := 2407145960212313803390747

theorem tailTrace_4687900 : CollatzResearch.WordTrace tailWord_4687900 prefixEnd_4687900 2407145960212313803390747 := by
  unfold tailWord_4687900
  simp only [CollatzResearch.WordTrace]
  refine ⟨85490879858273202211866577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113987839811030936282488769 85490879858273202211866577)
  ·
    refine ⟨64118159893704901658899933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85490879858273202211866577 64118159893704901658899933)
    ·
      refine ⟨24044309960139338122087475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64118159893704901658899933 24044309960139338122087475)
      ·
        refine ⟨36066464940209007183131213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24044309960139338122087475 36066464940209007183131213)
        ·
          refine ⟨13524924352578377693674205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36066464940209007183131213 13524924352578377693674205)
          ·
            refine ⟨5071846632216891635127827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13524924352578377693674205 5071846632216891635127827)
            ·
              refine ⟨7607769948325337452691741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5071846632216891635127827 7607769948325337452691741)
              ·
                refine ⟨2852913730622001544759403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7607769948325337452691741 2852913730622001544759403)
                ·
                  refine ⟨4279370595933002317139105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2852913730622001544759403 4279370595933002317139105)
                  ·
                    refine ⟨3209527946949751737854329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4279370595933002317139105 3209527946949751737854329)
                    ·
                      refine ⟨2407145960212313803390747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3209527946949751737854329 2407145960212313803390747)
                      ·
                        rfl

theorem cell23_4687900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_4687900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687900 prefixEnd_4687900 := by exact prefixLift 4687900
  have htrace : WordTrace (prefixWord ++ tailWord_4687900) baseStart_4687900 baseEnd_4687900 := by
    simpa [prefixWord, tailWord_4687900, baseEnd_4687900] using wordTrace_append hprefix tailTrace_4687900
  have hstable : (prefixWord ++ tailWord_4687900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687900).length < 2 ^ (prefixWord ++ tailWord_4687900).sum := by decide
  have hdescent : baseEnd_4687900 < baseStart_4687900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687915 : List Nat := [1, 1, 1, 1, 2, 1, 4, 4, 2, 6]
def baseStart_4687915 : Nat := 118140960795 + 4687915 * 2 ^ 59
def prefixEnd_4687915 : Nat := 4983230072969 + 3 ^ 40 * 4687915 * 2
def baseEnd_4687915 : Nat := 802384554140710414901059

theorem tailTrace_4687915 : CollatzResearch.WordTrace tailWord_4687915 prefixEnd_4687915 802384554140710414901059 := by
  unfold tailWord_4687915
  simp only [CollatzResearch.WordTrace]
  refine ⟨170982306811492061985529199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113988204540994707990352799 170982306811492061985529199)
  ·
    refine ⟨256473460217238092978293799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170982306811492061985529199 256473460217238092978293799)
    ·
      refine ⟨384710190325857139467440699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256473460217238092978293799 384710190325857139467440699)
      ·
        refine ⟨577065285488785709201161049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384710190325857139467440699 577065285488785709201161049)
        ·
          refine ⟨432798964116589281900870787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 577065285488785709201161049 432798964116589281900870787)
          ·
            refine ⟨649198446174883922851306181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432798964116589281900870787 649198446174883922851306181)
            ·
              refine ⟨121724708657790735534619909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 649198446174883922851306181 121724708657790735534619909)
              ·
                refine ⟨22823382873335762912741233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121724708657790735534619909 22823382873335762912741233)
                ·
                  refine ⟨17117537155001822184555925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22823382873335762912741233 17117537155001822184555925)
                  ·
                    refine ⟨802384554140710414901059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17117537155001822184555925 802384554140710414901059)
                    ·
                      rfl

theorem cell23_4687915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 6].length) (baseStart_4687915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687915 prefixEnd_4687915 := by exact prefixLift 4687915
  have htrace : WordTrace (prefixWord ++ tailWord_4687915) baseStart_4687915 baseEnd_4687915 := by
    simpa [prefixWord, tailWord_4687915, baseEnd_4687915] using wordTrace_append hprefix tailTrace_4687915
  have hstable : (prefixWord ++ tailWord_4687915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687915).length < 2 ^ (prefixWord ++ tailWord_4687915).sum := by decide
  have hdescent : baseEnd_4687915 < baseStart_4687915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687926 : List Nat := [5, 1, 2, 1, 1, 1, 2, 2, 3, 3, 2]
def baseStart_4687926 : Nat := 118140960795 + 4687926 * 2 ^ 59
def prefixEnd_4687926 : Nat := 4983230072969 + 3 ^ 40 * 4687926 * 2
def baseEnd_4687926 : Nat := 2407159310709330701665627

theorem tailTrace_4687926 : CollatzResearch.WordTrace tailWord_4687926 prefixEnd_4687926 2407159310709330701665627 := by
  unfold tailWord_4687926
  simp only [CollatzResearch.WordTrace]
  refine ⟨10686419250903263179011227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113988472009634807242786421 10686419250903263179011227)
  ·
    refine ⟨16029628876354894768516841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10686419250903263179011227 16029628876354894768516841)
    ·
      refine ⟨12022221657266171076387631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16029628876354894768516841 12022221657266171076387631)
      ·
        refine ⟨18033332485899256614581447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12022221657266171076387631 18033332485899256614581447)
        ·
          refine ⟨27049998728848884921872171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18033332485899256614581447 27049998728848884921872171)
          ·
            refine ⟨40574998093273327382808257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27049998728848884921872171 40574998093273327382808257)
            ·
              refine ⟨30431248569954995537106193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40574998093273327382808257 30431248569954995537106193)
              ·
                refine ⟨22823436427466246652829645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30431248569954995537106193 22823436427466246652829645)
                ·
                  refine ⟨8558788660299842494811117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22823436427466246652829645 8558788660299842494811117)
                  ·
                    refine ⟨3209545747612440935554169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8558788660299842494811117 3209545747612440935554169)
                    ·
                      refine ⟨2407159310709330701665627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3209545747612440935554169 2407159310709330701665627)
                      ·
                        rfl

theorem cell23_4687926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_4687926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687926 prefixEnd_4687926 := by exact prefixLift 4687926
  have htrace : WordTrace (prefixWord ++ tailWord_4687926) baseStart_4687926 baseEnd_4687926 := by
    simpa [prefixWord, tailWord_4687926, baseEnd_4687926] using wordTrace_append hprefix tailTrace_4687926
  have hstable : (prefixWord ++ tailWord_4687926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687926).length < 2 ^ (prefixWord ++ tailWord_4687926).sum := by decide
  have hdescent : baseEnd_4687926 < baseStart_4687926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687939 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 6, 2, 2]
def baseStart_4687939 : Nat := 118140960795 + 4687939 * 2 ^ 59
def prefixEnd_4687939 : Nat := 4983230072969 + 3 ^ 40 * 4687939 * 2
def baseEnd_4687939 : Nat := 2407165985957839150803067

theorem tailTrace_4687939 : CollatzResearch.WordTrace tailWord_4687939 prefixEnd_4687939 2407165985957839150803067 := by
  unfold tailWord_4687939
  simp only [CollatzResearch.WordTrace]
  refine ⟨170983182163405114084402871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113988788108936742722935247 170983182163405114084402871)
  ·
    refine ⟨256474773245107671126604307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170983182163405114084402871 256474773245107671126604307)
    ·
      refine ⟨384712159867661506689906461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256474773245107671126604307 384712159867661506689906461)
      ·
        refine ⟨144267059950373065008714923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 384712159867661506689906461 144267059950373065008714923)
        ·
          refine ⟨216400589925559597513072385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144267059950373065008714923 216400589925559597513072385)
          ·
            refine ⟨162300442444169698134804289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216400589925559597513072385 162300442444169698134804289)
            ·
              refine ⟨121725331833127273601103217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162300442444169698134804289 121725331833127273601103217)
              ·
                refine ⟨91293998874845455200827413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121725331833127273601103217 91293998874845455200827413)
                ·
                  refine ⟨4279406197258380712538785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 91293998874845455200827413 4279406197258380712538785)
                  ·
                    refine ⟨3209554647943785534404089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4279406197258380712538785 3209554647943785534404089)
                    ·
                      refine ⟨2407165985957839150803067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3209554647943785534404089 2407165985957839150803067)
                      ·
                        rfl

theorem cell23_4687939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6, 2, 2].length) (baseStart_4687939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687939 prefixEnd_4687939 := by exact prefixLift 4687939
  have htrace : WordTrace (prefixWord ++ tailWord_4687939) baseStart_4687939 baseEnd_4687939 := by
    simpa [prefixWord, tailWord_4687939, baseEnd_4687939] using wordTrace_append hprefix tailTrace_4687939
  have hstable : (prefixWord ++ tailWord_4687939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687939).length < 2 ^ (prefixWord ++ tailWord_4687939).sum := by decide
  have hdescent : baseEnd_4687939 < baseStart_4687939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687945 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 9]
def baseStart_4687945 : Nat := 118140960795 + 4687945 * 2 ^ 59
def prefixEnd_4687945 : Nat := 4983230072969 + 3 ^ 40 * 4687945 * 2
def baseEnd_4687945 : Nat := 267463229649085125258671

theorem tailTrace_4687945 : CollatzResearch.WordTrace tailWord_4687945 prefixEnd_4687945 267463229649085125258671 := by
  unfold tailWord_4687945
  simp only [CollatzResearch.WordTrace]
  refine ⟨170983401001383377109121289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113988934000922251406080859 170983401001383377109121289)
  ·
    refine ⟨128237550751037532831840967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170983401001383377109121289 128237550751037532831840967)
    ·
      refine ⟨192356326126556299247761451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128237550751037532831840967 192356326126556299247761451)
      ·
        refine ⟨288534489189834448871642177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192356326126556299247761451 288534489189834448871642177)
        ·
          refine ⟨216400866892375836653731633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288534489189834448871642177 216400866892375836653731633)
          ·
            refine ⟨162300650169281877490298725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216400866892375836653731633 162300650169281877490298725)
            ·
              refine ⟨30431371906740352029431011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 162300650169281877490298725 30431371906740352029431011)
              ·
                refine ⟨45647057860110528044146517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30431371906740352029431011 45647057860110528044146517)
                ·
                  refine ⟨267463229649085125258671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45647057860110528044146517 267463229649085125258671)
                  ·
                    rfl

theorem cell23_4687945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 9].length) (baseStart_4687945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687945 prefixEnd_4687945 := by exact prefixLift 4687945
  have htrace : WordTrace (prefixWord ++ tailWord_4687945) baseStart_4687945 baseEnd_4687945 := by
    simpa [prefixWord, tailWord_4687945, baseEnd_4687945] using wordTrace_append hprefix tailTrace_4687945
  have hstable : (prefixWord ++ tailWord_4687945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687945).length < 2 ^ (prefixWord ++ tailWord_4687945).sum := by decide
  have hdescent : baseEnd_4687945 < baseStart_4687945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4687973 : List Nat := [1, 3, 1, 3, 2, 3, 2, 2, 2, 2, 2]
def baseStart_4687973 : Nat := 118140960795 + 4687973 * 2 ^ 59
def prefixEnd_4687973 : Nat := 4983230072969 + 3 ^ 40 * 4687973 * 2
def baseEnd_4687973 : Nat := 2407183444300092017777911

theorem tailTrace_4687973 : CollatzResearch.WordTrace tailWord_4687973 prefixEnd_4687973 2407183444300092017777911 := by
  unfold tailWord_4687973
  simp only [CollatzResearch.WordTrace]
  refine ⟨170984422245281937891140573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113989614830187958594093715 170984422245281937891140573)
  ·
    refine ⟨64119158341980726709177715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170984422245281937891140573 64119158341980726709177715)
    ·
      refine ⟨96178737512971090063766573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64119158341980726709177715 96178737512971090063766573)
      ·
        refine ⟨36067026567364158773912465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96178737512971090063766573 36067026567364158773912465)
        ·
          refine ⟨27050269925523119080434349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36067026567364158773912465 27050269925523119080434349)
          ·
            refine ⟨10143851222071169655162881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27050269925523119080434349 10143851222071169655162881)
            ·
              refine ⟨7607888416553377241372161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10143851222071169655162881 7607888416553377241372161)
              ·
                refine ⟨5705916312415032931029121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7607888416553377241372161 5705916312415032931029121)
                ·
                  refine ⟨4279437234311274698271841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5705916312415032931029121 4279437234311274698271841)
                  ·
                    refine ⟨3209577925733456023703881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4279437234311274698271841 3209577925733456023703881)
                    ·
                      refine ⟨2407183444300092017777911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3209577925733456023703881 2407183444300092017777911)
                      ·
                        rfl

theorem cell23_4687973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_4687973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4687973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4687973 prefixEnd_4687973 := by exact prefixLift 4687973
  have htrace : WordTrace (prefixWord ++ tailWord_4687973) baseStart_4687973 baseEnd_4687973 := by
    simpa [prefixWord, tailWord_4687973, baseEnd_4687973] using wordTrace_append hprefix tailTrace_4687973
  have hstable : (prefixWord ++ tailWord_4687973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4687973).length < 2 ^ (prefixWord ++ tailWord_4687973).sum := by decide
  have hdescent : baseEnd_4687973 < baseStart_4687973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4687973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688086 : List Nat := [5, 2, 1, 2, 1, 1, 2, 1, 8]
def baseStart_4688086 : Nat := 118140960795 + 4688086 * 2 ^ 59
def prefixEnd_4688086 : Nat := 4983230072969 + 3 ^ 40 * 4688086 * 2
def baseEnd_4688086 : Nat := 267471274179338897296099

theorem tailTrace_4688086 : CollatzResearch.WordTrace tailWord_4688086 prefixEnd_4688086 267471274179338897296099 := by
  unfold tailWord_4688086
  simp only [CollatzResearch.WordTrace]
  refine ⟨10686783980867034886875257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113992362462581705460002741 10686783980867034886875257)
  ·
    refine ⟨8015087985650276165156443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10686783980867034886875257 8015087985650276165156443)
    ·
      refine ⟨12022631978475414247734665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8015087985650276165156443 12022631978475414247734665)
      ·
        refine ⟨9016973983856560685800999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12022631978475414247734665 9016973983856560685800999)
        ·
          refine ⟨13525460975784841028701499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9016973983856560685800999 13525460975784841028701499)
          ·
            refine ⟨20288191463677261543052249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13525460975784841028701499 20288191463677261543052249)
            ·
              refine ⟨15216143597757946157289187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20288191463677261543052249 15216143597757946157289187)
              ·
                refine ⟨22824215396636919235933781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15216143597757946157289187 22824215396636919235933781)
                ·
                  refine ⟨267471274179338897296099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22824215396636919235933781 267471274179338897296099)
                  ·
                    rfl

theorem cell23_4688086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_4688086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688086 prefixEnd_4688086 := by exact prefixLift 4688086
  have htrace : WordTrace (prefixWord ++ tailWord_4688086) baseStart_4688086 baseEnd_4688086 := by
    simpa [prefixWord, tailWord_4688086, baseEnd_4688086] using wordTrace_append hprefix tailTrace_4688086
  have hstable : (prefixWord ++ tailWord_4688086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688086).length < 2 ^ (prefixWord ++ tailWord_4688086).sum := by decide
  have hdescent : baseEnd_4688086 < baseStart_4688086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688103 : List Nat := [1, 1, 5, 3, 1, 3, 2, 1, 6]
def baseStart_4688103 : Nat := 118140960795 + 4688103 * 2 ^ 59
def prefixEnd_4688103 : Nat := 4983230072969 + 3 ^ 40 * 4688103 * 2
def baseEnd_4688103 : Nat := 267472244087241834350257

theorem tailTrace_4688103 : CollatzResearch.WordTrace tailWord_4688103 prefixEnd_4688103 267472244087241834350257 := by
  unfold tailWord_4688103
  simp only [CollatzResearch.WordTrace]
  refine ⟨170989163734810970093372963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113992775823207313395581975 170989163734810970093372963)
  ·
    refine ⟨256483745602216455140059445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170989163734810970093372963 256483745602216455140059445)
    ·
      refine ⟨24045351150207792669380573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 256483745602216455140059445 24045351150207792669380573)
      ·
        refine ⟨9017006681327922251017715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24045351150207792669380573 9017006681327922251017715)
        ·
          refine ⟨13525510021991883376526573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9017006681327922251017715 13525510021991883376526573)
          ·
            refine ⟨5072066258246956266197465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13525510021991883376526573 5072066258246956266197465)
            ·
              refine ⟨3804049693685217199648099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5072066258246956266197465 3804049693685217199648099)
              ·
                refine ⟨5706074540527825799472149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3804049693685217199648099 5706074540527825799472149)
                ·
                  refine ⟨267472244087241834350257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5706074540527825799472149 267472244087241834350257)
                  ·
                    rfl

theorem cell23_4688103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 6].length) (baseStart_4688103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688103 prefixEnd_4688103 := by exact prefixLift 4688103
  have htrace : WordTrace (prefixWord ++ tailWord_4688103) baseStart_4688103 baseEnd_4688103 := by
    simpa [prefixWord, tailWord_4688103, baseEnd_4688103] using wordTrace_append hprefix tailTrace_4688103
  have hstable : (prefixWord ++ tailWord_4688103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688103).length < 2 ^ (prefixWord ++ tailWord_4688103).sum := by decide
  have hdescent : baseEnd_4688103 < baseStart_4688103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688106 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 4, 3, 2]
def baseStart_4688106 : Nat := 118140960795 + 4688106 * 2 ^ 59
def prefixEnd_4688106 : Nat := 4983230072969 + 3 ^ 40 * 4688106 * 2
def baseEnd_4688106 : Nat := 2407251737227139997414799

theorem tailTrace_4688106 : CollatzResearch.WordTrace tailWord_4688106 prefixEnd_4688106 2407251737227139997414799 := by
  unfold tailWord_4688106
  simp only [CollatzResearch.WordTrace]
  refine ⟨42747318288450025401433043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113992848769200067737154781 42747318288450025401433043)
  ·
    refine ⟨64120977432675038102149565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42747318288450025401433043 64120977432675038102149565)
    ·
      refine ⟨24045366537253139288306087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64120977432675038102149565 24045366537253139288306087)
      ·
        refine ⟨36068049805879708932459131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24045366537253139288306087 36068049805879708932459131)
        ·
          refine ⟨54102074708819563398688697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36068049805879708932459131 54102074708819563398688697)
          ·
            refine ⟨40576556031614672549016523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54102074708819563398688697 40576556031614672549016523)
            ·
              refine ⟨60864834047422008823524785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40576556031614672549016523 60864834047422008823524785)
              ·
                refine ⟨45648625535566506617643589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60864834047422008823524785 45648625535566506617643589)
                ·
                  refine ⟨8559117287918719990808173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45648625535566506617643589 8559117287918719990808173)
                  ·
                    refine ⟨3209668982969519996553065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8559117287918719990808173 3209668982969519996553065)
                    ·
                      refine ⟨2407251737227139997414799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3209668982969519996553065 2407251737227139997414799)
                      ·
                        rfl

theorem cell23_4688106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_4688106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688106 prefixEnd_4688106 := by exact prefixLift 4688106
  have htrace : WordTrace (prefixWord ++ tailWord_4688106) baseStart_4688106 baseEnd_4688106 := by
    simpa [prefixWord, tailWord_4688106, baseEnd_4688106] using wordTrace_append hprefix tailTrace_4688106
  have hstable : (prefixWord ++ tailWord_4688106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688106).length < 2 ^ (prefixWord ++ tailWord_4688106).sum := by decide
  have hdescent : baseEnd_4688106 < baseStart_4688106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688112 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 5, 6]
def baseStart_4688112 : Nat := 118140960795 + 4688112 * 2 ^ 59
def prefixEnd_4688112 : Nat := 4983230072969 + 3 ^ 40 * 4688112 * 2
def baseEnd_4688112 : Nat := 802418272703688991313257

theorem tailTrace_4688112 : CollatzResearch.WordTrace tailWord_4688112 prefixEnd_4688112 802418272703688991313257 := by
  unfold tailWord_4688112
  simp only [CollatzResearch.WordTrace]
  refine ⟨85494745995889182315225295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113992994661185576420300393 85494745995889182315225295)
  ·
    refine ⟨128242118993833773472837943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85494745995889182315225295 128242118993833773472837943)
    ·
      refine ⟨192363178490750660209256915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128242118993833773472837943 192363178490750660209256915)
      ·
        refine ⟨288544767736125990313885373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192363178490750660209256915 288544767736125990313885373)
        ·
          refine ⟨108204287901047246367707015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 288544767736125990313885373 108204287901047246367707015)
          ·
            refine ⟨162306431851570869551560523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108204287901047246367707015 162306431851570869551560523)
            ·
              refine ⟨243459647777356304327340785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162306431851570869551560523 243459647777356304327340785)
              ·
                refine ⟨182594735833017228245505589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 243459647777356304327340785 182594735833017228245505589)
                ·
                  refine ⟨17118256484345365148016149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 182594735833017228245505589 17118256484345365148016149)
                  ·
                    refine ⟨802418272703688991313257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17118256484345365148016149 802418272703688991313257)
                    ·
                      rfl

theorem cell23_4688112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 5, 6].length) (baseStart_4688112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688112 prefixEnd_4688112 := by exact prefixLift 4688112
  have htrace : WordTrace (prefixWord ++ tailWord_4688112) baseStart_4688112 baseEnd_4688112 := by
    simpa [prefixWord, tailWord_4688112, baseEnd_4688112] using wordTrace_append hprefix tailTrace_4688112
  have hstable : (prefixWord ++ tailWord_4688112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688112).length < 2 ^ (prefixWord ++ tailWord_4688112).sum := by decide
  have hdescent : baseEnd_4688112 < baseStart_4688112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688129 : List Nat := [1, 2, 4, 1, 1, 2, 3, 2, 1, 6]
def baseStart_4688129 : Nat := 118140960795 + 4688129 * 2 ^ 59
def prefixEnd_4688129 : Nat := 4983230072969 + 3 ^ 40 * 4688129 * 2
def baseEnd_4688129 : Nat := 802421182427397802475731

theorem tailTrace_4688129 : CollatzResearch.WordTrace tailWord_4688129 prefixEnd_4688129 802421182427397802475731 := by
  unfold tailWord_4688129
  simp only [CollatzResearch.WordTrace]
  refine ⟨170990112032716776533819441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113993408021811184355879627 170990112032716776533819441)
  ·
    refine ⟨128242584024537582400364581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170990112032716776533819441 128242584024537582400364581)
    ·
      refine ⟨24045484504600796700068359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128242584024537582400364581 24045484504600796700068359)
      ·
        refine ⟨36068226756901195050102539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24045484504600796700068359 36068226756901195050102539)
        ·
          refine ⟨54102340135351792575153809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36068226756901195050102539 54102340135351792575153809)
          ·
            refine ⟨40576755101513844431365357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54102340135351792575153809 40576755101513844431365357)
            ·
              refine ⟨15216283163067691661762009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40576755101513844431365357 15216283163067691661762009)
              ·
                refine ⟨11412212372300768746321507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15216283163067691661762009 11412212372300768746321507)
                ·
                  refine ⟨17118318558451153119482261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11412212372300768746321507 17118318558451153119482261)
                  ·
                    refine ⟨802421182427397802475731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17118318558451153119482261 802421182427397802475731)
                    ·
                      rfl

theorem cell23_4688129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_4688129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688129 prefixEnd_4688129 := by exact prefixLift 4688129
  have htrace : WordTrace (prefixWord ++ tailWord_4688129) baseStart_4688129 baseEnd_4688129 := by
    simpa [prefixWord, tailWord_4688129, baseEnd_4688129] using wordTrace_append hprefix tailTrace_4688129
  have hstable : (prefixWord ++ tailWord_4688129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688129).length < 2 ^ (prefixWord ++ tailWord_4688129).sum := by decide
  have hdescent : baseEnd_4688129 < baseStart_4688129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688159 : List Nat := [1, 1, 2, 4, 3, 1, 3, 8]
def baseStart_4688159 : Nat := 118140960795 + 4688159 * 2 ^ 59
def prefixEnd_4688159 : Nat := 4983230072969 + 3 ^ 40 * 4688159 * 2
def baseEnd_4688159 : Nat := 89158479692660307038965

theorem tailTrace_4688159 : CollatzResearch.WordTrace tailWord_4688159 prefixEnd_4688159 89158479692660307038965 := by
  unfold tailWord_4688159
  simp only [CollatzResearch.WordTrace]
  refine ⟨170991206222608091657411531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113994137481738727771607687 170991206222608091657411531)
  ·
    refine ⟨256486809333912137486117297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170991206222608091657411531 256486809333912137486117297)
    ·
      refine ⟨192365107000434103114587973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256486809333912137486117297 192365107000434103114587973)
      ·
        refine ⟨36068457562581394333985245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 192365107000434103114587973 36068457562581394333985245)
        ·
          refine ⟨13525671585968022875244467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36068457562581394333985245 13525671585968022875244467)
          ·
            refine ⟨20288507378952034312866701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13525671585968022875244467 20288507378952034312866701)
            ·
              refine ⟨7608190267107012867325013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20288507378952034312866701 7608190267107012867325013)
              ·
                refine ⟨89158479692660307038965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7608190267107012867325013 89158479692660307038965)
                ·
                  rfl

theorem cell23_4688159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 8].length) (baseStart_4688159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688159 prefixEnd_4688159 := by exact prefixLift 4688159
  have htrace : WordTrace (prefixWord ++ tailWord_4688159) baseStart_4688159 baseEnd_4688159 := by
    simpa [prefixWord, tailWord_4688159, baseEnd_4688159] using wordTrace_append hprefix tailTrace_4688159
  have hstable : (prefixWord ++ tailWord_4688159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688159).length < 2 ^ (prefixWord ++ tailWord_4688159).sum := by decide
  have hdescent : baseEnd_4688159 < baseStart_4688159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688174 : List Nat := [4, 1, 3, 3, 2, 1, 1, 1, 2, 3, 2]
def baseStart_4688174 : Nat := 118140960795 + 4688174 * 2 ^ 59
def prefixEnd_4688174 : Nat := 4983230072969 + 3 ^ 40 * 4688174 * 2
def baseEnd_4688174 : Nat := 2407286653911645731364487

theorem tailTrace_4688174 : CollatzResearch.WordTrace tailWord_4688174 prefixEnd_4688174 2407286653911645731364487 := by
  unfold tailWord_4688174
  simp only [CollatzResearch.WordTrace]
  refine ⟨21373969164694218652400947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113994502211702499479471717 21373969164694218652400947)
  ·
    refine ⟨32060953747041327978601421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21373969164694218652400947 32060953747041327978601421)
    ·
      refine ⟨12022857655140497991975533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32060953747041327978601421 12022857655140497991975533)
      ·
        refine ⟨4508571620677686746990825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12022857655140497991975533 4508571620677686746990825)
        ·
          refine ⟨3381428715508265060243119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4508571620677686746990825 3381428715508265060243119)
          ·
            refine ⟨5072143073262397590364679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3381428715508265060243119 5072143073262397590364679)
            ·
              refine ⟨7608214609893596385547019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5072143073262397590364679 7608214609893596385547019)
              ·
                refine ⟨11412321914840394578320529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7608214609893596385547019 11412321914840394578320529)
                ·
                  refine ⟨8559241436130295933740397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11412321914840394578320529 8559241436130295933740397)
                  ·
                    refine ⟨3209715538548860975152649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8559241436130295933740397 3209715538548860975152649)
                    ·
                      refine ⟨2407286653911645731364487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3209715538548860975152649 2407286653911645731364487)
                      ·
                        rfl

theorem cell23_4688174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_4688174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688174 prefixEnd_4688174 := by exact prefixLift 4688174
  have htrace : WordTrace (prefixWord ++ tailWord_4688174) baseStart_4688174 baseEnd_4688174 := by
    simpa [prefixWord, tailWord_4688174, baseEnd_4688174] using wordTrace_append hprefix tailTrace_4688174
  have hstable : (prefixWord ++ tailWord_4688174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688174).length < 2 ^ (prefixWord ++ tailWord_4688174).sum := by decide
  have hdescent : baseEnd_4688174 < baseStart_4688174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688186 : List Nat := [3, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3]
def baseStart_4688186 : Nat := 118140960795 + 4688186 * 2 ^ 59
def prefixEnd_4688186 : Nat := 4983230072969 + 3 ^ 40 * 4688186 * 2
def baseEnd_4688186 : Nat := 2407292815679499684414431

theorem tailTrace_4688186 : CollatzResearch.WordTrace tailWord_4688186 prefixEnd_4688186 2407292815679499684414431 := by
  unfold tailWord_4688186
  simp only [CollatzResearch.WordTrace]
  refine ⟨42748047748377568817161103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113994793995673516845762941 42748047748377568817161103)
  ·
    refine ⟨64122071622566353225741655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42748047748377568817161103 64122071622566353225741655)
    ·
      refine ⟨96183107433849529838612483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64122071622566353225741655 96183107433849529838612483)
      ·
        refine ⟨144274661150774294757918725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96183107433849529838612483 144274661150774294757918725)
        ·
          refine ⟨27051498965770180267109761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144274661150774294757918725 27051498965770180267109761)
          ·
            refine ⟨20288624224327635200332321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27051498965770180267109761 20288624224327635200332321)
            ·
              refine ⟨15216468168245726400249241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20288624224327635200332321 15216468168245726400249241)
              ·
                refine ⟨11412351126184294800186931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15216468168245726400249241 11412351126184294800186931)
                ·
                  refine ⟨17118526689276442200280397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11412351126184294800186931 17118526689276442200280397)
                  ·
                    refine ⟨6419447508478665825105149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17118526689276442200280397 6419447508478665825105149)
                    ·
                      refine ⟨2407292815679499684414431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6419447508478665825105149 2407292815679499684414431)
                      ·
                        rfl

theorem cell23_4688186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3].length) (baseStart_4688186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688186 prefixEnd_4688186 := by exact prefixLift 4688186
  have htrace : WordTrace (prefixWord ++ tailWord_4688186) baseStart_4688186 baseEnd_4688186 := by
    simpa [prefixWord, tailWord_4688186, baseEnd_4688186] using wordTrace_append hprefix tailTrace_4688186
  have hstable : (prefixWord ++ tailWord_4688186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688186).length < 2 ^ (prefixWord ++ tailWord_4688186).sum := by decide
  have hdescent : baseEnd_4688186 < baseStart_4688186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688190 : List Nat := [4, 2, 1, 2, 1, 2, 4, 1, 1, 2, 3]
def baseStart_4688190 : Nat := 118140960795 + 4688190 * 2 ^ 59
def prefixEnd_4688190 : Nat := 4983230072969 + 3 ^ 40 * 4688190 * 2
def baseEnd_4688190 : Nat := 2407294869602117668764413

theorem tailTrace_4688190 : CollatzResearch.WordTrace tailWord_4688190 prefixEnd_4688190 2407294869602117668764413 := by
  unfold tailWord_4688190
  simp only [CollatzResearch.WordTrace]
  refine ⟨21374042110686972993973753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113994891256997189301193349 21374042110686972993973753)
  ·
    refine ⟨16030531583015229745480315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21374042110686972993973753 16030531583015229745480315)
    ·
      refine ⟨24045797374522844618220473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16030531583015229745480315 24045797374522844618220473)
      ·
        refine ⟨18034348030892133463665355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24045797374522844618220473 18034348030892133463665355)
        ·
          refine ⟨27051522046338200195498033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18034348030892133463665355 27051522046338200195498033)
          ·
            refine ⟨20288641534753650146623525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27051522046338200195498033 20288641534753650146623525)
            ·
              refine ⟨3804120287766309402491911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20288641534753650146623525 3804120287766309402491911)
              ·
                refine ⟨5706180431649464103737867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3804120287766309402491911 5706180431649464103737867)
                ·
                  refine ⟨8559270647474196155606801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5706180431649464103737867 8559270647474196155606801)
                  ·
                    refine ⟨6419452985605647116705101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8559270647474196155606801 6419452985605647116705101)
                    ·
                      refine ⟨2407294869602117668764413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6419452985605647116705101 2407294869602117668764413)
                      ·
                        rfl

theorem cell23_4688190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_4688190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688190 prefixEnd_4688190 := by exact prefixLift 4688190
  have htrace : WordTrace (prefixWord ++ tailWord_4688190) baseStart_4688190 baseEnd_4688190 := by
    simpa [prefixWord, tailWord_4688190, baseEnd_4688190] using wordTrace_append hprefix tailTrace_4688190
  have hstable : (prefixWord ++ tailWord_4688190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688190).length < 2 ^ (prefixWord ++ tailWord_4688190).sum := by decide
  have hdescent : baseEnd_4688190 < baseStart_4688190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688239 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 4]
def baseStart_4688239 : Nat := 118140960795 + 4688239 * 2 ^ 59
def prefixEnd_4688239 : Nat := 4983230072969 + 3 ^ 40 * 4688239 * 2
def baseEnd_4688239 : Nat := 2407320030154187977051687

theorem tailTrace_4688239 : CollatzResearch.WordTrace tailWord_4688239 prefixEnd_4688239 2407320030154187977051687 := by
  unfold tailWord_4688239
  simp only [CollatzResearch.WordTrace]
  refine ⟨170994124062318265320323771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113996082708212176880215847 170994124062318265320323771)
  ·
    refine ⟨256491186093477397980485657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170994124062318265320323771 256491186093477397980485657)
    ·
      refine ⟨192368389570108048485364243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256491186093477397980485657 192368389570108048485364243)
      ·
        refine ⟨288552584355162072728046365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192368389570108048485364243 288552584355162072728046365)
        ·
          refine ⟨108207219133185777273017387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 288552584355162072728046365 108207219133185777273017387)
          ·
            refine ⟨162310828699778665909526081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108207219133185777273017387 162310828699778665909526081)
            ·
              refine ⟨121733121524833999432144561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162310828699778665909526081 121733121524833999432144561)
              ·
                refine ⟨91299841143625499574108421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121733121524833999432144561 91299841143625499574108421)
                ·
                  refine ⟨17118720214429781170145329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91299841143625499574108421 17118720214429781170145329)
                  ·
                    refine ⟨12839040160822335877608997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17118720214429781170145329 12839040160822335877608997)
                    ·
                      refine ⟨2407320030154187977051687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12839040160822335877608997 2407320030154187977051687)
                      ·
                        rfl

theorem cell23_4688239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 4].length) (baseStart_4688239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688239 prefixEnd_4688239 := by exact prefixLift 4688239
  have htrace : WordTrace (prefixWord ++ tailWord_4688239) baseStart_4688239 baseEnd_4688239 := by
    simpa [prefixWord, tailWord_4688239, baseEnd_4688239] using wordTrace_append hprefix tailTrace_4688239
  have hstable : (prefixWord ++ tailWord_4688239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688239).length < 2 ^ (prefixWord ++ tailWord_4688239).sum := by decide
  have hdescent : baseEnd_4688239 < baseStart_4688239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688260 : List Nat := [2, 3, 2, 1, 1, 2, 2, 4, 2, 2, 2]
def baseStart_4688260 : Nat := 118140960795 + 4688260 * 2 ^ 59
def prefixEnd_4688260 : Nat := 4983230072969 + 3 ^ 40 * 4688260 * 2
def baseEnd_4688260 : Nat := 2407330813247932394889091

theorem tailTrace_4688260 : CollatzResearch.WordTrace tailWord_4688260 prefixEnd_4688260 2407330813247932394889091 := by
  unfold tailWord_4688260
  simp only [CollatzResearch.WordTrace]
  refine ⟨85497444997621092953419117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113996593330161457271225489 85497444997621092953419117)
  ·
    refine ⟨32061541874107909857532169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85497444997621092953419117 32061541874107909857532169)
    ·
      refine ⟨24046156405580932393149127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32061541874107909857532169 24046156405580932393149127)
      ·
        refine ⟨36069234608371398589723691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24046156405580932393149127 36069234608371398589723691)
        ·
          refine ⟨54103851912557097884585537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36069234608371398589723691 54103851912557097884585537)
          ·
            refine ⟨40577888934417823413439153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54103851912557097884585537 40577888934417823413439153)
            ·
              refine ⟨30433416700813367560079365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40577888934417823413439153 30433416700813367560079365)
              ·
                refine ⟨5706265631402506417514881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30433416700813367560079365 5706265631402506417514881)
                ·
                  refine ⟨4279699223551879813136161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5706265631402506417514881 4279699223551879813136161)
                  ·
                    refine ⟨3209774417663909859852121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4279699223551879813136161 3209774417663909859852121)
                    ·
                      refine ⟨2407330813247932394889091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3209774417663909859852121 2407330813247932394889091)
                      ·
                        rfl

theorem cell23_4688260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_4688260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688260 prefixEnd_4688260 := by exact prefixLift 4688260
  have htrace : WordTrace (prefixWord ++ tailWord_4688260) baseStart_4688260 baseEnd_4688260 := by
    simpa [prefixWord, tailWord_4688260, baseEnd_4688260] using wordTrace_append hprefix tailTrace_4688260
  have hstable : (prefixWord ++ tailWord_4688260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688260).length < 2 ^ (prefixWord ++ tailWord_4688260).sum := by decide
  have hdescent : baseEnd_4688260 < baseStart_4688260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688279 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 3, 7]
def baseStart_4688279 : Nat := 118140960795 + 4688279 * 2 ^ 59
def prefixEnd_4688279 : Nat := 4983230072969 + 3 ^ 40 * 4688279 * 2
def baseEnd_4688279 : Nat := 802446856460122606850501

theorem tailTrace_4688279 : CollatzResearch.WordTrace tailWord_4688279 prefixEnd_4688279 802446856460122606850501 := by
  unfold tailWord_4688279
  simp only [CollatzResearch.WordTrace]
  refine ⟨170995582982173352151779891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113997055321448901434519927 170995582982173352151779891)
  ·
    refine ⟨256493374473260028227669837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170995582982173352151779891 256493374473260028227669837)
    ·
      refine ⟨96185015427472510585376189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256493374473260028227669837 96185015427472510585376189)
      ·
        refine ⟨36069380785302191469516071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96185015427472510585376189 36069380785302191469516071)
        ·
          refine ⟨54104071177953287204274107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36069380785302191469516071 54104071177953287204274107)
          ·
            refine ⟨81156106766929930806411161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54104071177953287204274107 81156106766929930806411161)
            ·
              refine ⟨60867080075197448104808371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81156106766929930806411161 60867080075197448104808371)
              ·
                refine ⟨91300620112796172157212557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60867080075197448104808371 91300620112796172157212557)
                ·
                  refine ⟨34237732542298564558954709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91300620112796172157212557 34237732542298564558954709)
                  ·
                    refine ⟨802446856460122606850501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34237732542298564558954709 802446856460122606850501)
                    ·
                      rfl

theorem cell23_4688279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 7].length) (baseStart_4688279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688279 prefixEnd_4688279 := by exact prefixLift 4688279
  have htrace : WordTrace (prefixWord ++ tailWord_4688279) baseStart_4688279 baseEnd_4688279 := by
    simpa [prefixWord, tailWord_4688279, baseEnd_4688279] using wordTrace_append hprefix tailTrace_4688279
  have hstable : (prefixWord ++ tailWord_4688279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688279).length < 2 ^ (prefixWord ++ tailWord_4688279).sum := by decide
  have hdescent : baseEnd_4688279 < baseStart_4688279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688360 : List Nat := [2, 1, 4, 1, 1, 3, 1, 5, 1, 4]
def baseStart_4688360 : Nat := 118140960795 + 4688360 * 2 ^ 59
def prefixEnd_4688360 : Nat := 4983230072969 + 3 ^ 40 * 4688360 * 2
def baseEnd_4688360 : Nat := 802460720437794001212877

theorem tailTrace_4688360 : CollatzResearch.WordTrace tailWord_4688360 prefixEnd_4688360 802460720437794001212877 := by
  unfold tailWord_4688360
  simp only [CollatzResearch.WordTrace]
  refine ⟨85499268647439951492739267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113999024863253268656985689 85499268647439951492739267)
  ·
    refine ⟨128248902971159927239108901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85499268647439951492739267 128248902971159927239108901)
    ·
      refine ⟨24046669307092486357332919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128248902971159927239108901 24046669307092486357332919)
      ·
        refine ⟨36070003960638729535999379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24046669307092486357332919 36070003960638729535999379)
        ·
          refine ⟨54105005940958094303999069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36070003960638729535999379 54105005940958094303999069)
          ·
            refine ⟨20289377227859285363999651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54105005940958094303999069 20289377227859285363999651)
            ·
              refine ⟨30434065841788928045999477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20289377227859285363999651 30434065841788928045999477)
              ·
                refine ⟨2853193672667712004312451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30434065841788928045999477 2853193672667712004312451)
                ·
                  refine ⟨4279790509001568006468677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2853193672667712004312451 4279790509001568006468677)
                  ·
                    refine ⟨802460720437794001212877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4279790509001568006468677 802460720437794001212877)
                    ·
                      rfl

theorem cell23_4688360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_4688360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688360 prefixEnd_4688360 := by exact prefixLift 4688360
  have htrace : WordTrace (prefixWord ++ tailWord_4688360) baseStart_4688360 baseEnd_4688360 := by
    simpa [prefixWord, tailWord_4688360, baseEnd_4688360] using wordTrace_append hprefix tailTrace_4688360
  have hstable : (prefixWord ++ tailWord_4688360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688360).length < 2 ^ (prefixWord ++ tailWord_4688360).sum := by decide
  have hdescent : baseEnd_4688360 < baseStart_4688360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688393 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 6, 3, 2]
def baseStart_4688393 : Nat := 118140960795 + 4688393 * 2 ^ 59
def prefixEnd_4688393 : Nat := 4983230072969 + 3 ^ 40 * 4688393 * 2
def baseEnd_4688393 : Nat := 2407399106174980374525979

theorem tailTrace_4688393 : CollatzResearch.WordTrace tailWord_4688393 prefixEnd_4688393 2407399106174980374525979 := by
  unfold tailWord_4688393
  simp only [CollatzResearch.WordTrace]
  refine ⟨170999740903760349621429833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113999827269173566414286555 170999740903760349621429833)
  ·
    refine ⟨128249805677820262216072375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170999740903760349621429833 128249805677820262216072375)
    ·
      refine ⟨192374708516730393324108563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128249805677820262216072375 192374708516730393324108563)
      ·
        refine ⟨288562062775095589986162845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192374708516730393324108563 288562062775095589986162845)
        ·
          refine ⟨108210773540660846244811067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 288562062775095589986162845 108210773540660846244811067)
          ·
            refine ⟨162316160310991269367216601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108210773540660846244811067 162316160310991269367216601)
            ·
              refine ⟨121737120233243452025412451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162316160310991269367216601 121737120233243452025412451)
              ·
                refine ⟨182605680349865178038118677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121737120233243452025412451 182605680349865178038118677)
                ·
                  refine ⟨8559641266399930220536813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 182605680349865178038118677 8559641266399930220536813)
                  ·
                    refine ⟨3209865474899973832701305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8559641266399930220536813 3209865474899973832701305)
                    ·
                      refine ⟨2407399106174980374525979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3209865474899973832701305 2407399106174980374525979)
                      ·
                        rfl

theorem cell23_4688393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 3, 2].length) (baseStart_4688393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688393 prefixEnd_4688393 := by exact prefixLift 4688393
  have htrace : WordTrace (prefixWord ++ tailWord_4688393) baseStart_4688393 baseEnd_4688393 := by
    simpa [prefixWord, tailWord_4688393, baseEnd_4688393] using wordTrace_append hprefix tailTrace_4688393
  have hstable : (prefixWord ++ tailWord_4688393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688393).length < 2 ^ (prefixWord ++ tailWord_4688393).sum := by decide
  have hdescent : baseEnd_4688393 < baseStart_4688393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688403 : List Nat := [1, 1, 1, 2, 1, 5, 4, 2, 1, 5]
def baseStart_4688403 : Nat := 118140960795 + 4688403 * 2 ^ 59
def prefixEnd_4688403 : Nat := 4983230072969 + 3 ^ 40 * 4688403 * 2
def baseEnd_4688403 : Nat := 802468080327175111800311

theorem tailTrace_4688403 : CollatzResearch.WordTrace tailWord_4688403 prefixEnd_4688403 802468080327175111800311 := by
  unfold tailWord_4688403
  simp only [CollatzResearch.WordTrace]
  refine ⟨171000105633724121329293863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114000070422482747552862575 171000105633724121329293863)
  ·
    refine ⟨256500158450586181993940795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171000105633724121329293863 256500158450586181993940795)
    ·
      refine ⟨384750237675879272990911193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256500158450586181993940795 384750237675879272990911193)
      ·
        refine ⟨288562678256909454743183395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 384750237675879272990911193 288562678256909454743183395)
        ·
          refine ⟨432844017385364182114775093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288562678256909454743183395 432844017385364182114775093)
          ·
            refine ⟨40579126629877892073260165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 432844017385364182114775093 40579126629877892073260165)
            ·
              refine ⟨7608586243102104763736281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40579126629877892073260165 7608586243102104763736281)
              ·
                refine ⟨5706439682326578572802211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7608586243102104763736281 5706439682326578572802211)
                ·
                  refine ⟨8559659523489867859203317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5706439682326578572802211 8559659523489867859203317)
                  ·
                    refine ⟨802468080327175111800311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8559659523489867859203317 802468080327175111800311)
                    ·
                      rfl

theorem cell23_4688403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 5].length) (baseStart_4688403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688403 prefixEnd_4688403 := by exact prefixLift 4688403
  have htrace : WordTrace (prefixWord ++ tailWord_4688403) baseStart_4688403 baseEnd_4688403 := by
    simpa [prefixWord, tailWord_4688403, baseEnd_4688403] using wordTrace_append hprefix tailTrace_4688403
  have hstable : (prefixWord ++ tailWord_4688403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688403).length < 2 ^ (prefixWord ++ tailWord_4688403).sum := by decide
  have hdescent : baseEnd_4688403 < baseStart_4688403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688433 : List Nat := [1, 2, 2, 3, 1, 1, 4, 1, 4, 4]
def baseStart_4688433 : Nat := 118140960795 + 4688433 * 2 ^ 59
def prefixEnd_4688433 : Nat := 4983230072969 + 3 ^ 40 * 4688433 * 2
def baseEnd_4688433 : Nat := 802473215133720072675265

theorem tailTrace_4688433 : CollatzResearch.WordTrace tailWord_4688433 prefixEnd_4688433 802473215133720072675265 := by
  unfold tailWord_4688433
  simp only [CollatzResearch.WordTrace]
  refine ⟨171001199823615436452885953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114000799882410290968590635 171001199823615436452885953)
  ·
    refine ⟨128250899867711577339664465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171001199823615436452885953 128250899867711577339664465)
    ·
      refine ⟨96188174900783683004748349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128250899867711577339664465 96188174900783683004748349)
      ·
        refine ⟨36070565587793881126780631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96188174900783683004748349 36070565587793881126780631)
        ·
          refine ⟨54105848381690821690170947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36070565587793881126780631 54105848381690821690170947)
          ·
            refine ⟨81158772572536232535256421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54105848381690821690170947 81158772572536232535256421)
            ·
              refine ⟨15217269857350543600360579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81158772572536232535256421 15217269857350543600360579)
              ·
                refine ⟨22825904786025815400540869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15217269857350543600360579 22825904786025815400540869)
                ·
                  refine ⟨4279857147379840387601413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22825904786025815400540869 4279857147379840387601413)
                  ·
                    refine ⟨802473215133720072675265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4279857147379840387601413 802473215133720072675265)
                    ·
                      rfl

theorem cell23_4688433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4, 4].length) (baseStart_4688433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688433 prefixEnd_4688433 := by exact prefixLift 4688433
  have htrace : WordTrace (prefixWord ++ tailWord_4688433) baseStart_4688433 baseEnd_4688433 := by
    simpa [prefixWord, tailWord_4688433, baseEnd_4688433] using wordTrace_append hprefix tailTrace_4688433
  have hstable : (prefixWord ++ tailWord_4688433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688433).length < 2 ^ (prefixWord ++ tailWord_4688433).sum := by decide
  have hdescent : baseEnd_4688433 < baseStart_4688433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688454 : List Nat := [6, 1, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_4688454 : Nat := 118140960795 + 4688454 * 2 ^ 59
def prefixEnd_4688454 : Nat := 4983230072969 + 3 ^ 40 * 4688454 * 2
def baseEnd_4688454 : Nat := 802476809498301545287733

theorem tailTrace_4688454 : CollatzResearch.WordTrace tailWord_4688454 prefixEnd_4688454 802476809498301545287733 := by
  unfold tailWord_4688454
  simp only [CollatzResearch.WordTrace]
  refine ⟨5343811429891854907481263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 114001310504359571359600277 5343811429891854907481263)
  ·
    refine ⟨8015717144837782361221895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5343811429891854907481263 8015717144837782361221895)
    ·
      refine ⟨12023575717256673541832843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8015717144837782361221895 12023575717256673541832843)
      ·
        refine ⟨18035363575885010312749265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12023575717256673541832843 18035363575885010312749265)
        ·
          refine ⟨13526522681913757734561949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18035363575885010312749265 13526522681913757734561949)
          ·
            refine ⟨5072446005717659150460731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13526522681913757734561949 5072446005717659150460731)
            ·
              refine ⟨7608669008576488725691097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5072446005717659150460731 7608669008576488725691097)
              ·
                refine ⟨5706501756432366544268323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7608669008576488725691097 5706501756432366544268323)
                ·
                  refine ⟨8559752634648549816402485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5706501756432366544268323 8559752634648549816402485)
                  ·
                    refine ⟨802476809498301545287733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8559752634648549816402485 802476809498301545287733)
                    ·
                      rfl

theorem cell23_4688454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_4688454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688454 prefixEnd_4688454 := by exact prefixLift 4688454
  have htrace : WordTrace (prefixWord ++ tailWord_4688454) baseStart_4688454 baseEnd_4688454 := by
    simpa [prefixWord, tailWord_4688454, baseEnd_4688454] using wordTrace_append hprefix tailTrace_4688454
  have hstable : (prefixWord ++ tailWord_4688454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688454).length < 2 ^ (prefixWord ++ tailWord_4688454).sum := by decide
  have hdescent : baseEnd_4688454 < baseStart_4688454 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688493 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 2, 7]
def baseStart_4688493 : Nat := 118140960795 + 4688493 * 2 ^ 59
def prefixEnd_4688493 : Nat := 4983230072969 + 3 ^ 40 * 4688493 * 2
def baseEnd_4688493 : Nat := 802483484746809994425173

theorem tailTrace_4688493 : CollatzResearch.WordTrace tailWord_4688493 prefixEnd_4688493 802483484746809994425173 := by
  unfold tailWord_4688493
  simp only [CollatzResearch.WordTrace]
  refine ⟨171003388203398066700070133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114002258802265377800046755 171003388203398066700070133)
  ·
    refine ⟨16031567644068568753131575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 171003388203398066700070133 16031567644068568753131575)
    ·
      refine ⟨24047351466102853129697363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16031567644068568753131575 24047351466102853129697363)
      ·
        refine ⟨36071027199154279694546045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24047351466102853129697363 36071027199154279694546045)
        ·
          refine ⟨13526635199682854885454767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36071027199154279694546045 13526635199682854885454767)
          ·
            refine ⟨20289952799524282328182151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13526635199682854885454767 20289952799524282328182151)
            ·
              refine ⟨30434929199286423492273227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20289952799524282328182151 30434929199286423492273227)
              ·
                refine ⟨45652393798929635238409841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30434929199286423492273227 45652393798929635238409841)
                ·
                  refine ⟨34239295349197226428807381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45652393798929635238409841 34239295349197226428807381)
                  ·
                    refine ⟨802483484746809994425173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34239295349197226428807381 802483484746809994425173)
                    ·
                      rfl

theorem cell23_4688493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_4688493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688493 prefixEnd_4688493 := by exact prefixLift 4688493
  have htrace : WordTrace (prefixWord ++ tailWord_4688493) baseStart_4688493 baseEnd_4688493 := by
    simpa [prefixWord, tailWord_4688493, baseEnd_4688493] using wordTrace_append hprefix tailTrace_4688493
  have hstable : (prefixWord ++ tailWord_4688493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688493).length < 2 ^ (prefixWord ++ tailWord_4688493).sum := by decide
  have hdescent : baseEnd_4688493 < baseStart_4688493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688513 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_4688513 : Nat := 118140960795 + 4688513 * 2 ^ 59
def prefixEnd_4688513 : Nat := 4983230072969 + 3 ^ 40 * 4688513 * 2
def baseEnd_4688513 : Nat := 2407460723853519905025427

theorem tailTrace_4688513 : CollatzResearch.WordTrace tailWord_4688513 prefixEnd_4688513 2407460723853519905025427 := by
  unfold tailWord_4688513
  simp only [CollatzResearch.WordTrace]
  refine ⟨171004117663325610115798193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114002745108883740077198795 171004117663325610115798193)
  ·
    refine ⟨128253088247494207586848645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171004117663325610115798193 128253088247494207586848645)
    ·
      refine ⟨24047454046405163922534121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128253088247494207586848645 24047454046405163922534121)
      ·
        refine ⟨18035590534803872941900591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24047454046405163922534121 18035590534803872941900591)
        ·
          refine ⟨27053385802205809412850887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18035590534803872941900591 27053385802205809412850887)
          ·
            refine ⟨40580078703308714119276331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27053385802205809412850887 40580078703308714119276331)
            ·
              refine ⟨60870118054963071178914497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40580078703308714119276331 60870118054963071178914497)
              ·
                refine ⟨45652588541222303384185873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60870118054963071178914497 45652588541222303384185873)
                ·
                  refine ⟨34239441405916727538139405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45652588541222303384185873 34239441405916727538139405)
                  ·
                    refine ⟨12839790527218772826802277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34239441405916727538139405 12839790527218772826802277)
                    ·
                      refine ⟨2407460723853519905025427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12839790527218772826802277 2407460723853519905025427)
                      ·
                        rfl

theorem cell23_4688513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_4688513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688513 prefixEnd_4688513 := by exact prefixLift 4688513
  have htrace : WordTrace (prefixWord ++ tailWord_4688513) baseStart_4688513 baseEnd_4688513 := by
    simpa [prefixWord, tailWord_4688513, baseEnd_4688513] using wordTrace_append hprefix tailTrace_4688513
  have hstable : (prefixWord ++ tailWord_4688513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688513).length < 2 ^ (prefixWord ++ tailWord_4688513).sum := by decide
  have hdescent : baseEnd_4688513 < baseStart_4688513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688547 : List Nat := [1, 1, 1, 4, 1, 1, 2, 6, 2, 2, 2]
def baseStart_4688547 : Nat := 118140960795 + 4688547 * 2 ^ 59
def prefixEnd_4688547 : Nat := 4983230072969 + 3 ^ 40 * 4688547 * 2
def baseEnd_4688547 : Nat := 2407478182195772772000271

theorem tailTrace_4688547 : CollatzResearch.WordTrace tailWord_4688547 prefixEnd_4688547 2407478182195772772000271 := by
  unfold tailWord_4688547
  simp only [CollatzResearch.WordTrace]
  refine ⟨171005357745202433922535895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114003571830134955948357263 171005357745202433922535895)
  ·
    refine ⟨256508036617803650883803843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171005357745202433922535895 256508036617803650883803843)
    ·
      refine ⟨384762054926705476325705765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256508036617803650883803843 384762054926705476325705765)
      ·
        refine ⟨72142885298757276811069831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 384762054926705476325705765 72142885298757276811069831)
        ·
          refine ⟨108214327948135915216604747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72142885298757276811069831 108214327948135915216604747)
          ·
            refine ⟨162321491922203872824907121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108214327948135915216604747 162321491922203872824907121)
            ·
              refine ⟨121741118941652904618680341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162321491922203872824907121 121741118941652904618680341)
              ·
                refine ⟨5706614950389979904000641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 121741118941652904618680341 5706614950389979904000641)
                ·
                  refine ⟨4279961212792484928000481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5706614950389979904000641 4279961212792484928000481)
                  ·
                    refine ⟨3209970909594363696000361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4279961212792484928000481 3209970909594363696000361)
                    ·
                      refine ⟨2407478182195772772000271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3209970909594363696000361 2407478182195772772000271)
                      ·
                        rfl

theorem cell23_4688547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2, 2, 2].length) (baseStart_4688547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688547 prefixEnd_4688547 := by exact prefixLift 4688547
  have htrace : WordTrace (prefixWord ++ tailWord_4688547) baseStart_4688547 baseEnd_4688547 := by
    simpa [prefixWord, tailWord_4688547, baseEnd_4688547] using wordTrace_append hprefix tailTrace_4688547
  have hstable : (prefixWord ++ tailWord_4688547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688547).length < 2 ^ (prefixWord ++ tailWord_4688547).sum := by decide
  have hdescent : baseEnd_4688547 < baseStart_4688547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688593 : List Nat := [1, 2, 2, 1, 2, 3, 2, 2, 1, 2, 5]
def baseStart_4688593 : Nat := 118140960795 + 4688593 * 2 ^ 59
def prefixEnd_4688593 : Nat := 4983230072969 + 3 ^ 40 * 4688593 * 2
def baseEnd_4688593 : Nat := 2407501802305879592025059

theorem tailTrace_4688593 : CollatzResearch.WordTrace tailWord_4688593 prefixEnd_4688593 2407501802305879592025059 := by
  unfold tailWord_4688593
  simp only [CollatzResearch.WordTrace]
  refine ⟨171007035503035783778710433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114004690335357189185806955 171007035503035783778710433)
  ·
    refine ⟨128255276627276837834032825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171007035503035783778710433 128255276627276837834032825)
    ·
      refine ⟨96191457470457628375524619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128255276627276837834032825 96191457470457628375524619)
      ·
        refine ⟨144287186205686442563286929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96191457470457628375524619 144287186205686442563286929)
        ·
          refine ⟨108215389654264831922465197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144287186205686442563286929 108215389654264831922465197)
          ·
            refine ⟨40580771120349311970924449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108215389654264831922465197 40580771120349311970924449)
            ·
              refine ⟨30435578340261983978193337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40580771120349311970924449 30435578340261983978193337)
              ·
                refine ⟨22826683755196487983645003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30435578340261983978193337 22826683755196487983645003)
                ·
                  refine ⟨34240025632794731975467505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22826683755196487983645003 34240025632794731975467505)
                  ·
                    refine ⟨25680019224596048981600629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34240025632794731975467505 25680019224596048981600629)
                    ·
                      refine ⟨2407501802305879592025059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25680019224596048981600629 2407501802305879592025059)
                      ·
                        rfl

theorem cell23_4688593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_4688593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688593 prefixEnd_4688593 := by exact prefixLift 4688593
  have htrace : WordTrace (prefixWord ++ tailWord_4688593) baseStart_4688593 baseEnd_4688593 := by
    simpa [prefixWord, tailWord_4688593, baseEnd_4688593] using wordTrace_append hprefix tailTrace_4688593
  have hstable : (prefixWord ++ tailWord_4688593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688593).length < 2 ^ (prefixWord ++ tailWord_4688593).sum := by decide
  have hdescent : baseEnd_4688593 < baseStart_4688593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688600 : List Nat := [2, 1, 2, 2, 3, 3, 1, 2, 2, 5]
def baseStart_4688600 : Nat := 118140960795 + 4688600 * 2 ^ 59
def prefixEnd_4688600 : Nat := 4983230072969 + 3 ^ 40 * 4688600 * 2
def baseEnd_4688600 : Nat := 802501798890153688212509

theorem tailTrace_4688600 : CollatzResearch.WordTrace tailWord_4688600 prefixEnd_4688600 802501798890153688212509 := by
  unfold tailWord_4688600
  simp only [CollatzResearch.WordTrace]
  refine ⟨85503645407005211987107627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114004860542673615982810169 85503645407005211987107627)
  ·
    refine ⟨128255468110507817980661441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85503645407005211987107627 128255468110507817980661441)
    ·
      refine ⟨96191601082880863485496081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128255468110507817980661441 96191601082880863485496081)
      ·
        refine ⟨72143700812160647614122061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96191601082880863485496081 72143700812160647614122061)
        ·
          refine ⟨27053887804560242855295773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72143700812160647614122061 27053887804560242855295773)
          ·
            refine ⟨10145207926710091070735915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27053887804560242855295773 10145207926710091070735915)
            ·
              refine ⟨15217811890065136606103873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10145207926710091070735915 15217811890065136606103873)
              ·
                refine ⟨11413358917548852454577905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15217811890065136606103873 11413358917548852454577905)
                ·
                  refine ⟨8560019188161639340933429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11413358917548852454577905 8560019188161639340933429)
                  ·
                    refine ⟨802501798890153688212509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8560019188161639340933429 802501798890153688212509)
                    ·
                      rfl

theorem cell23_4688600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 2, 5].length) (baseStart_4688600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688600 prefixEnd_4688600 := by exact prefixLift 4688600
  have htrace : WordTrace (prefixWord ++ tailWord_4688600) baseStart_4688600 baseEnd_4688600 := by
    simpa [prefixWord, tailWord_4688600, baseEnd_4688600] using wordTrace_append hprefix tailTrace_4688600
  have hstable : (prefixWord ++ tailWord_4688600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688600).length < 2 ^ (prefixWord ++ tailWord_4688600).sum := by decide
  have hdescent : baseEnd_4688600 < baseStart_4688600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688620 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 1, 6, 2]
def baseStart_4688620 : Nat := 118140960795 + 4688620 * 2 ^ 59
def prefixEnd_4688620 : Nat := 4983230072969 + 3 ^ 40 * 4688620 * 2
def baseEnd_4688620 : Nat := 2407515666283550986387435

theorem tailTrace_4688620 : CollatzResearch.WordTrace tailWord_4688620 prefixEnd_4688620 2407515666283550986387435 := by
  unfold tailWord_4688620
  simp only [CollatzResearch.WordTrace]
  refine ⟨85504010136968983694971657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114005346849291978259962209 85504010136968983694971657)
  ·
    refine ⟨64128007602726737771228743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85504010136968983694971657 64128007602726737771228743)
    ·
      refine ⟨96192011404090106656843115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64128007602726737771228743 96192011404090106656843115)
      ·
        refine ⟨144288017106135159985264673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96192011404090106656843115 144288017106135159985264673)
        ·
          refine ⟨108216012829601369988948505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144288017106135159985264673 108216012829601369988948505)
          ·
            refine ⟨81162009622201027491711379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108216012829601369988948505 81162009622201027491711379)
            ·
              refine ⟨121743014433301541237567069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81162009622201027491711379 121743014433301541237567069)
              ·
                refine ⟨45653630412488077964087651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121743014433301541237567069 45653630412488077964087651)
                ·
                  refine ⟨68480445618732116946131477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45653630412488077964087651 68480445618732116946131477)
                  ·
                    refine ⟨3210020888378067981849913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68480445618732116946131477 3210020888378067981849913)
                    ·
                      refine ⟨2407515666283550986387435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3210020888378067981849913 2407515666283550986387435)
                      ·
                        rfl

theorem cell23_4688620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 6, 2].length) (baseStart_4688620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688620 prefixEnd_4688620 := by exact prefixLift 4688620
  have htrace : WordTrace (prefixWord ++ tailWord_4688620) baseStart_4688620 baseEnd_4688620 := by
    simpa [prefixWord, tailWord_4688620, baseEnd_4688620] using wordTrace_append hprefix tailTrace_4688620
  have hstable : (prefixWord ++ tailWord_4688620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688620).length < 2 ^ (prefixWord ++ tailWord_4688620).sum := by decide
  have hdescent : baseEnd_4688620 < baseStart_4688620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688633 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 2, 4, 4]
def baseStart_4688633 : Nat := 118140960795 + 4688633 * 2 ^ 59
def prefixEnd_4688633 : Nat := 4983230072969 + 3 ^ 40 * 4688633 * 2
def baseEnd_4688633 : Nat := 2407522341532059435524875

theorem tailTrace_4688633 : CollatzResearch.WordTrace tailWord_4688633 prefixEnd_4688633 2407522341532059435524875 := by
  unfold tailWord_4688633
  simp only [CollatzResearch.WordTrace]
  refine ⟨171008494422890870610166553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114005662948593913740111035 171008494422890870610166553)
  ·
    refine ⟨128256370817168152957624915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171008494422890870610166553 128256370817168152957624915)
    ·
      refine ⟨192384556225752229436437373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128256370817168152957624915 192384556225752229436437373)
      ·
        refine ⟨72144208584657086038664015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192384556225752229436437373 72144208584657086038664015)
        ·
          refine ⟨108216312876985629057996023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72144208584657086038664015 108216312876985629057996023)
          ·
            refine ⟨162324469315478443586994035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108216312876985629057996023 162324469315478443586994035)
            ·
              refine ⟨243486703973217665380491053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162324469315478443586994035 243486703973217665380491053)
              ·
                refine ⟨91307513989956624517684145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 243486703973217665380491053 91307513989956624517684145)
                ·
                  refine ⟨68480635492467468388263109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91307513989956624517684145 68480635492467468388263109)
                  ·
                    refine ⟨12840119154837650322799333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68480635492467468388263109 12840119154837650322799333)
                    ·
                      refine ⟨2407522341532059435524875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12840119154837650322799333 2407522341532059435524875)
                      ·
                        rfl

theorem cell23_4688633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_4688633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688633 prefixEnd_4688633 := by exact prefixLift 4688633
  have htrace : WordTrace (prefixWord ++ tailWord_4688633) baseStart_4688633 baseEnd_4688633 := by
    simpa [prefixWord, tailWord_4688633, baseEnd_4688633] using wordTrace_append hprefix tailTrace_4688633
  have hstable : (prefixWord ++ tailWord_4688633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688633).length < 2 ^ (prefixWord ++ tailWord_4688633).sum := by decide
  have hdescent : baseEnd_4688633 < baseStart_4688633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688690 : List Nat := [3, 2, 1, 1, 3, 1, 1, 3, 3, 5]
def baseStart_4688690 : Nat := 118140960795 + 4688690 * 2 ^ 59
def prefixEnd_4688690 : Nat := 4983230072969 + 3 ^ 40 * 4688690 * 2
def baseEnd_4688690 : Nat := 802517203309788570837371

theorem tailTrace_4688690 : CollatzResearch.WordTrace tailWord_4688690 prefixEnd_4688690 802517203309788570837371 := by
  unfold tailWord_4688690
  simp only [CollatzResearch.WordTrace]
  refine ⟨42752643345921092336247881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114007048922456246229994349 42752643345921092336247881)
  ·
    refine ⟨32064482509440819252185911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42752643345921092336247881 32064482509440819252185911)
    ·
      refine ⟨48096723764161228878278867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32064482509440819252185911 48096723764161228878278867)
      ·
        refine ⟨72145085646241843317418301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48096723764161228878278867 72145085646241843317418301)
        ·
          refine ⟨27054407117340691244031863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72145085646241843317418301 27054407117340691244031863)
          ·
            refine ⟨40581610676011036866047795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27054407117340691244031863 40581610676011036866047795)
            ·
              refine ⟨60872416014016555299071693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40581610676011036866047795 60872416014016555299071693)
              ·
                refine ⟨22827156005256208237151885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60872416014016555299071693 22827156005256208237151885)
                ·
                  refine ⟨8560183501971078088931957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22827156005256208237151885 8560183501971078088931957)
                  ·
                    refine ⟨802517203309788570837371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8560183501971078088931957 802517203309788570837371)
                    ·
                      rfl

theorem cell23_4688690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_4688690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688690 prefixEnd_4688690 := by exact prefixLift 4688690
  have htrace : WordTrace (prefixWord ++ tailWord_4688690) baseStart_4688690 baseEnd_4688690 := by
    simpa [prefixWord, tailWord_4688690, baseEnd_4688690] using wordTrace_append hprefix tailTrace_4688690
  have hstable : (prefixWord ++ tailWord_4688690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688690).length < 2 ^ (prefixWord ++ tailWord_4688690).sum := by decide
  have hdescent : baseEnd_4688690 < baseStart_4688690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688730 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5]
def baseStart_4688730 : Nat := 118140960795 + 4688730 * 2 ^ 59
def prefixEnd_4688730 : Nat := 4983230072969 + 3 ^ 40 * 4688730 * 2
def baseEnd_4688730 : Nat := 2407572149155545556011929

theorem tailTrace_4688730 : CollatzResearch.WordTrace tailWord_4688730 prefixEnd_4688730 2407572149155545556011929 := by
  unfold tailWord_4688730
  simp only [CollatzResearch.WordTrace]
  refine ⟨42753008075884864044111911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114008021535692970784298429 42753008075884864044111911)
  ·
    refine ⟨64129512113827296066167867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42753008075884864044111911 64129512113827296066167867)
    ·
      refine ⟨96194268170740944099251801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64129512113827296066167867 96194268170740944099251801)
      ·
        refine ⟨72145701128055708074438851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96194268170740944099251801 72145701128055708074438851)
        ·
          refine ⟨108218551692083562111658277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72145701128055708074438851 108218551692083562111658277)
          ·
            refine ⟨20290978442265667895935927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108218551692083562111658277 20290978442265667895935927)
            ·
              refine ⟨30436467663398501843903891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20290978442265667895935927 30436467663398501843903891)
              ·
                refine ⟨45654701495097752765855837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30436467663398501843903891 45654701495097752765855837)
                ·
                  refine ⟨17120513060661657287195939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45654701495097752765855837 17120513060661657287195939)
                  ·
                    refine ⟨25680769590992485930793909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17120513060661657287195939 25680769590992485930793909)
                    ·
                      refine ⟨2407572149155545556011929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25680769590992485930793909 2407572149155545556011929)
                      ·
                        rfl

theorem cell23_4688730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_4688730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688730 prefixEnd_4688730 := by exact prefixLift 4688730
  have htrace : WordTrace (prefixWord ++ tailWord_4688730) baseStart_4688730 baseEnd_4688730 := by
    simpa [prefixWord, tailWord_4688730, baseEnd_4688730] using wordTrace_append hprefix tailTrace_4688730
  have hstable : (prefixWord ++ tailWord_4688730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688730).length < 2 ^ (prefixWord ++ tailWord_4688730).sum := by decide
  have hdescent : baseEnd_4688730 < baseStart_4688730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688744 : List Nat := [2, 1, 4, 2, 1, 3, 2, 2, 1, 1, 4]
def baseStart_4688744 : Nat := 118140960795 + 4688744 * 2 ^ 59
def prefixEnd_4688744 : Nat := 4983230072969 + 3 ^ 40 * 4688744 * 2
def baseEnd_4688744 : Nat := 2407579337884708501236865

theorem tailTrace_4688744 : CollatzResearch.WordTrace tailWord_4688744 prefixEnd_4688744 2407579337884708501236865 := by
  unfold tailWord_4688744
  simp only [CollatzResearch.WordTrace]
  refine ⟨85506271462744368283728643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114008361950325824378304857 85506271462744368283728643)
  ·
    refine ⟨128259407194116552425592965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85506271462744368283728643 128259407194116552425592965)
    ·
      refine ⟨24048638848896853579798681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128259407194116552425592965 24048638848896853579798681)
      ·
        refine ⟨18036479136672640184849011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24048638848896853579798681 18036479136672640184849011)
        ·
          refine ⟨27054718705008960277273517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18036479136672640184849011 27054718705008960277273517)
          ·
            refine ⟨10145519514378360103977569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27054718705008960277273517 10145519514378360103977569)
            ·
              refine ⟨7609139635783770077983177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10145519514378360103977569 7609139635783770077983177)
              ·
                refine ⟨5706854726837827558487383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7609139635783770077983177 5706854726837827558487383)
                ·
                  refine ⟨8560282090256741337731075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5706854726837827558487383 8560282090256741337731075)
                  ·
                    refine ⟨12840423135385112006596613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8560282090256741337731075 12840423135385112006596613)
                    ·
                      refine ⟨2407579337884708501236865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12840423135385112006596613 2407579337884708501236865)
                      ·
                        rfl

theorem cell23_4688744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_4688744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688744 prefixEnd_4688744 := by exact prefixLift 4688744
  have htrace : WordTrace (prefixWord ++ tailWord_4688744) baseStart_4688744 baseEnd_4688744 := by
    simpa [prefixWord, tailWord_4688744, baseEnd_4688744] using wordTrace_append hprefix tailTrace_4688744
  have hstable : (prefixWord ++ tailWord_4688744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688744).length < 2 ^ (prefixWord ++ tailWord_4688744).sum := by decide
  have hdescent : baseEnd_4688744 < baseStart_4688744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688747 : List Nat := [1, 1, 1, 1, 2, 2, 5, 4, 1, 2, 3]
def baseStart_4688747 : Nat := 118140960795 + 4688747 * 2 ^ 59
def prefixEnd_4688747 : Nat := 4983230072969 + 3 ^ 40 * 4688747 * 2
def baseEnd_4688747 : Nat := 2407580878326671989499351

theorem tailTrace_4688747 : CollatzResearch.WordTrace tailWord_4688747 prefixEnd_4688747 2407580878326671989499351 := by
  unfold tailWord_4688747
  simp only [CollatzResearch.WordTrace]
  refine ⟨171012652344477868079816495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114008434896318578719877663 171012652344477868079816495)
  ·
    refine ⟨256518978516716802119724743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171012652344477868079816495 256518978516716802119724743)
    ·
      refine ⟨384778467775075203179587115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256518978516716802119724743 384778467775075203179587115)
      ·
        refine ⟨577167701662612804769380673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384778467775075203179587115 577167701662612804769380673)
        ·
          refine ⟨432875776246959603577035505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 577167701662612804769380673 432875776246959603577035505)
          ·
            refine ⟨324656832185219702682776629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 432875776246959603577035505 324656832185219702682776629)
            ·
              refine ⟨30436578017364347126510309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 324656832185219702682776629 30436578017364347126510309)
              ·
                refine ⟨5706858378255815086220683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30436578017364347126510309 5706858378255815086220683)
                ·
                  refine ⟨8560287567383722629331025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5706858378255815086220683 8560287567383722629331025)
                  ·
                    refine ⟨6420215675537791971998269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8560287567383722629331025 6420215675537791971998269)
                    ·
                      refine ⟨2407580878326671989499351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6420215675537791971998269 2407580878326671989499351)
                      ·
                        rfl

theorem cell23_4688747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 2, 3].length) (baseStart_4688747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688747 prefixEnd_4688747 := by exact prefixLift 4688747
  have htrace : WordTrace (prefixWord ++ tailWord_4688747) baseStart_4688747 baseEnd_4688747 := by
    simpa [prefixWord, tailWord_4688747, baseEnd_4688747] using wordTrace_append hprefix tailTrace_4688747
  have hstable : (prefixWord ++ tailWord_4688747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688747).length < 2 ^ (prefixWord ++ tailWord_4688747).sum := by decide
  have hdescent : baseEnd_4688747 < baseStart_4688747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688778 : List Nat := [3, 1, 2, 4, 1, 3, 1, 1, 3, 2, 2]
def baseStart_4688778 : Nat := 118140960795 + 4688778 * 2 ^ 59
def prefixEnd_4688778 : Nat := 4983230072969 + 3 ^ 40 * 4688778 * 2
def baseEnd_4688778 : Nat := 2407596796226961368211709

theorem tailTrace_4688778 : CollatzResearch.WordTrace tailWord_4688778 prefixEnd_4688778 2407596796226961368211709 := by
  unfold tailWord_4688778
  simp only [CollatzResearch.WordTrace]
  refine ⟨42753445751841390093548747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114009188671577040249463325 42753445751841390093548747)
  ·
    refine ⟨64130168627762085140323121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42753445751841390093548747 64130168627762085140323121)
    ·
      refine ⟨48097626470821563855242341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64130168627762085140323121 48097626470821563855242341)
      ·
        refine ⟨9018304963279043222857939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48097626470821563855242341 9018304963279043222857939)
        ·
          refine ⟨13527457444918564834286909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9018304963279043222857939 13527457444918564834286909)
          ·
            refine ⟨5072796541844461812857591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13527457444918564834286909 5072796541844461812857591)
            ·
              refine ⟨7609194812766692719286387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5072796541844461812857591 7609194812766692719286387)
              ·
                refine ⟨11413792219150039078929581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7609194812766692719286387 11413792219150039078929581)
                ·
                  refine ⟨4280172082181264654598593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11413792219150039078929581 4280172082181264654598593)
                  ·
                    refine ⟨3210129061635948490948945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4280172082181264654598593 3210129061635948490948945)
                    ·
                      refine ⟨2407596796226961368211709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3210129061635948490948945 2407596796226961368211709)
                      ·
                        rfl

theorem cell23_4688778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_4688778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688778 prefixEnd_4688778 := by exact prefixLift 4688778
  have htrace : WordTrace (prefixWord ++ tailWord_4688778) baseStart_4688778 baseEnd_4688778 := by
    simpa [prefixWord, tailWord_4688778, baseEnd_4688778] using wordTrace_append hprefix tailTrace_4688778
  have hstable : (prefixWord ++ tailWord_4688778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688778).length < 2 ^ (prefixWord ++ tailWord_4688778).sum := by decide
  have hdescent : baseEnd_4688778 < baseStart_4688778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688804 : List Nat := [2, 3, 1, 2, 1, 2, 3, 1, 3, 3, 2]
def baseStart_4688804 : Nat := 118140960795 + 4688804 * 2 ^ 59
def prefixEnd_4688804 : Nat := 4983230072969 + 3 ^ 40 * 4688804 * 2
def baseEnd_4688804 : Nat := 2407610146723978266486589

theorem tailTrace_4688804 : CollatzResearch.WordTrace tailWord_4688804 prefixEnd_4688804 2407610146723978266486589 := by
  unfold tailWord_4688804
  simp only [CollatzResearch.WordTrace]
  refine ⟨85507365652635683407320733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114009820870180911209760977 85507365652635683407320733)
  ·
    refine ⟨32065262119738381277745275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85507365652635683407320733 32065262119738381277745275)
    ·
      refine ⟨48097893179607571916617913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32065262119738381277745275 48097893179607571916617913)
      ·
        refine ⟨36073419884705678937463435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48097893179607571916617913 36073419884705678937463435)
        ·
          refine ⟨54110129827058518406195153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36073419884705678937463435 54110129827058518406195153)
          ·
            refine ⟨40582597370293888804646365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54110129827058518406195153 40582597370293888804646365)
            ·
              refine ⟨15218474013860208301742387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40582597370293888804646365 15218474013860208301742387)
              ·
                refine ⟨22827711020790312452613581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15218474013860208301742387 22827711020790312452613581)
                ·
                  refine ⟨8560391632796367169730093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22827711020790312452613581 8560391632796367169730093)
                  ·
                    refine ⟨3210146862298637688648785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8560391632796367169730093 3210146862298637688648785)
                    ·
                      refine ⟨2407610146723978266486589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3210146862298637688648785 2407610146723978266486589)
                      ·
                        rfl

theorem cell23_4688804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_4688804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688804 prefixEnd_4688804 := by exact prefixLift 4688804
  have htrace : WordTrace (prefixWord ++ tailWord_4688804) baseStart_4688804 baseEnd_4688804 := by
    simpa [prefixWord, tailWord_4688804, baseEnd_4688804] using wordTrace_append hprefix tailTrace_4688804
  have hstable : (prefixWord ++ tailWord_4688804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688804).length < 2 ^ (prefixWord ++ tailWord_4688804).sum := by decide
  have hdescent : baseEnd_4688804 < baseStart_4688804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688845 : List Nat := [1, 6, 3, 1, 1, 1, 2, 1, 1, 3, 3]
def baseStart_4688845 : Nat := 118140960795 + 4688845 * 2 ^ 59
def prefixEnd_4688845 : Nat := 4983230072969 + 3 ^ 40 * 4688845 * 2
def baseEnd_4688845 : Nat := 2407631199430812606073901

theorem tailTrace_4688845 : CollatzResearch.WordTrace tailWord_4688845 prefixEnd_4688845 2407631199430812606073901 := by
  unfold tailWord_4688845
  simp only [CollatzResearch.WordTrace]
  refine ⟨171016226698122830816883989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114010817798748553877922659 171016226698122830816883989)
  ·
    refine ⟨8016385626474507694541437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 171016226698122830816883989 8016385626474507694541437)
    ·
      refine ⟨3006144609927940385453039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8016385626474507694541437 3006144609927940385453039)
      ·
        refine ⟨4509216914891910578179559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3006144609927940385453039 4509216914891910578179559)
        ·
          refine ⟨6763825372337865867269339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4509216914891910578179559 6763825372337865867269339)
          ·
            refine ⟨10145738058506798800904009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6763825372337865867269339 10145738058506798800904009)
            ·
              refine ⟨7609303543880099100678007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10145738058506798800904009 7609303543880099100678007)
              ·
                refine ⟨11413955315820148651017011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7609303543880099100678007 11413955315820148651017011)
                ·
                  refine ⟨17120932973730222976525517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11413955315820148651017011 17120932973730222976525517)
                  ·
                    refine ⟨6420349865148833616197069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17120932973730222976525517 6420349865148833616197069)
                    ·
                      refine ⟨2407631199430812606073901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6420349865148833616197069 2407631199430812606073901)
                      ·
                        rfl

theorem cell23_4688845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_4688845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688845 prefixEnd_4688845 := by exact prefixLift 4688845
  have htrace : WordTrace (prefixWord ++ tailWord_4688845) baseStart_4688845 baseEnd_4688845 := by
    simpa [prefixWord, tailWord_4688845, baseEnd_4688845] using wordTrace_append hprefix tailTrace_4688845
  have hstable : (prefixWord ++ tailWord_4688845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688845).length < 2 ^ (prefixWord ++ tailWord_4688845).sum := by decide
  have hdescent : baseEnd_4688845 < baseStart_4688845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688847 : List Nat := [1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 4]
def baseStart_4688847 : Nat := 118140960795 + 4688847 * 2 ^ 59
def prefixEnd_4688847 : Nat := 4983230072969 + 3 ^ 40 * 4688847 * 2
def baseEnd_4688847 : Nat := 2407632226392121598248891

theorem tailTrace_4688847 : CollatzResearch.WordTrace tailWord_4688847 prefixEnd_4688847 2407632226392121598248891 := by
  unfold tailWord_4688847
  simp only [CollatzResearch.WordTrace]
  refine ⟨171016299644115585158456795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114010866429410390105637863 171016299644115585158456795)
  ·
    refine ⟨256524449466173377737685193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171016299644115585158456795 256524449466173377737685193)
    ·
      refine ⟨192393337099630033303263895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256524449466173377737685193 192393337099630033303263895)
      ·
        refine ⟨288590005649445049954895843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192393337099630033303263895 288590005649445049954895843)
        ·
          refine ⟨432885008474167574932343765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288590005649445049954895843 432885008474167574932343765)
          ·
            refine ⟨10145742386113302537476807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 432885008474167574932343765 10145742386113302537476807)
            ·
              refine ⟨15218613579169953806215211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10145742386113302537476807 15218613579169953806215211)
              ·
                refine ⟨22827920368754930709322817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15218613579169953806215211 22827920368754930709322817)
                ·
                  refine ⟨17120940276566198031992113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22827920368754930709322817 17120940276566198031992113)
                  ·
                    refine ⟨12840705207424648523994085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17120940276566198031992113 12840705207424648523994085)
                    ·
                      refine ⟨2407632226392121598248891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12840705207424648523994085 2407632226392121598248891)
                      ·
                        rfl

theorem cell23_4688847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 4].length) (baseStart_4688847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688847 prefixEnd_4688847 := by exact prefixLift 4688847
  have htrace : WordTrace (prefixWord ++ tailWord_4688847) baseStart_4688847 baseEnd_4688847 := by
    simpa [prefixWord, tailWord_4688847, baseEnd_4688847] using wordTrace_append hprefix tailTrace_4688847
  have hstable : (prefixWord ++ tailWord_4688847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688847).length < 2 ^ (prefixWord ++ tailWord_4688847).sum := by decide
  have hdescent : baseEnd_4688847 < baseStart_4688847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688857 : List Nat := [1, 2, 1, 2, 5, 2, 1, 2, 7]
def baseStart_4688857 : Nat := 118140960795 + 4688857 * 2 ^ 59
def prefixEnd_4688857 : Nat := 4983230072969 + 3 ^ 40 * 4688857 * 2
def baseEnd_4688857 : Nat := 267515262355407395458205

theorem tailTrace_4688857 : CollatzResearch.WordTrace tailWord_4688857 prefixEnd_4688857 267515262355407395458205 := by
  unfold tailWord_4688857
  simp only [CollatzResearch.WordTrace]
  refine ⟨171016664374079356866320825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114011109582719571244213883 171016664374079356866320825)
  ·
    refine ⟨128262498280559517649740619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171016664374079356866320825 128262498280559517649740619)
    ·
      refine ⟨192393747420839276474610929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128262498280559517649740619 192393747420839276474610929)
      ·
        refine ⟨144295310565629457355958197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192393747420839276474610929 144295310565629457355958197)
        ·
          refine ⟨13527685365527761627121081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 144295310565629457355958197 13527685365527761627121081)
          ·
            refine ⟨10145764024145821220340811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13527685365527761627121081 10145764024145821220340811)
            ·
              refine ⟨15218646036218731830511217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10145764024145821220340811 15218646036218731830511217)
              ·
                refine ⟨11413984527164048872883413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15218646036218731830511217 11413984527164048872883413)
                ·
                  refine ⟨267515262355407395458205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11413984527164048872883413 267515262355407395458205)
                  ·
                    rfl

theorem cell23_4688857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 7].length) (baseStart_4688857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688857 prefixEnd_4688857 := by exact prefixLift 4688857
  have htrace : WordTrace (prefixWord ++ tailWord_4688857) baseStart_4688857 baseEnd_4688857 := by
    simpa [prefixWord, tailWord_4688857, baseEnd_4688857] using wordTrace_append hprefix tailTrace_4688857
  have hstable : (prefixWord ++ tailWord_4688857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688857).length < 2 ^ (prefixWord ++ tailWord_4688857).sum := by decide
  have hdescent : baseEnd_4688857 < baseStart_4688857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688867 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 1, 5, 3]
def baseStart_4688867 : Nat := 118140960795 + 4688867 * 2 ^ 59
def prefixEnd_4688867 : Nat := 4983230072969 + 3 ^ 40 * 4688867 * 2
def baseEnd_4688867 : Nat := 2407642496005211519998799

theorem tailTrace_4688867 : CollatzResearch.WordTrace tailWord_4688867 prefixEnd_4688867 2407642496005211519998799 := by
  unfold tailWord_4688867
  simp only [CollatzResearch.WordTrace]
  refine ⟨171017029104043128574184855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114011352736028752382789903 171017029104043128574184855)
  ·
    refine ⟨256525543656064692861277283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171017029104043128574184855 256525543656064692861277283)
    ·
      refine ⟨384788315484097039291915925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256525543656064692861277283 384788315484097039291915925)
      ·
        refine ⟨18036952288317048716808559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 384788315484097039291915925 18036952288317048716808559)
        ·
          refine ⟨27055428432475573075212839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18036952288317048716808559 27055428432475573075212839)
          ·
            refine ⟨40583142648713359612819259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27055428432475573075212839 40583142648713359612819259)
            ·
              refine ⟨60874713973070039419228889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40583142648713359612819259 60874713973070039419228889)
              ·
                refine ⟨45656035479802529564421667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60874713973070039419228889 45656035479802529564421667)
                ·
                  refine ⟨68484053219703794346632501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45656035479802529564421667 68484053219703794346632501)
                  ·
                    refine ⟨6420379989347230719996797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68484053219703794346632501 6420379989347230719996797)
                    ·
                      refine ⟨2407642496005211519998799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6420379989347230719996797 2407642496005211519998799)
                      ·
                        rfl

theorem cell23_4688867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_4688867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688867 prefixEnd_4688867 := by exact prefixLift 4688867
  have htrace : WordTrace (prefixWord ++ tailWord_4688867) baseStart_4688867 baseEnd_4688867 := by
    simpa [prefixWord, tailWord_4688867, baseEnd_4688867] using wordTrace_append hprefix tailTrace_4688867
  have hstable : (prefixWord ++ tailWord_4688867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688867).length < 2 ^ (prefixWord ++ tailWord_4688867).sum := by decide
  have hdescent : baseEnd_4688867 < baseStart_4688867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688874 : List Nat := [3, 1, 3, 1, 2, 2, 1, 5, 5]
def baseStart_4688874 : Nat := 118140960795 + 4688874 * 2 ^ 59
def prefixEnd_4688874 : Nat := 4983230072969 + 3 ^ 40 * 4688874 * 2
def baseEnd_4688874 : Nat := 267516232263310332512363

theorem tailTrace_4688874 : CollatzResearch.WordTrace tailWord_4688874 prefixEnd_4688874 267516232263310332512363 := by
  unfold tailWord_4688874
  simp only [CollatzResearch.WordTrace]
  refine ⟨42754321103754442192422419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114011522943345179179793117 42754321103754442192422419)
  ·
    refine ⟨64131481655631663288633629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42754321103754442192422419 64131481655631663288633629)
    ·
      refine ⟨24049305620861873733237611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64131481655631663288633629 24049305620861873733237611)
      ·
        refine ⟨36073958431292810599856417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24049305620861873733237611 36073958431292810599856417)
        ·
          refine ⟨27055468823469607949892313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36073958431292810599856417 27055468823469607949892313)
          ·
            refine ⟨20291601617602205962419235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27055468823469607949892313 20291601617602205962419235)
            ·
              refine ⟨30437402426403308943628853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20291601617602205962419235 30437402426403308943628853)
              ·
                refine ⟨2853506477475310213465205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30437402426403308943628853 2853506477475310213465205)
                ·
                  refine ⟨267516232263310332512363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2853506477475310213465205 267516232263310332512363)
                  ·
                    rfl

theorem cell23_4688874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5, 5].length) (baseStart_4688874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688874 prefixEnd_4688874 := by exact prefixLift 4688874
  have htrace : WordTrace (prefixWord ++ tailWord_4688874) baseStart_4688874 baseEnd_4688874 := by
    simpa [prefixWord, tailWord_4688874, baseEnd_4688874] using wordTrace_append hprefix tailTrace_4688874
  have hstable : (prefixWord ++ tailWord_4688874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688874).length < 2 ^ (prefixWord ++ tailWord_4688874).sum := by decide
  have hdescent : baseEnd_4688874 < baseStart_4688874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688885 : List Nat := [1, 3, 5, 2, 1, 1, 1, 1, 4, 2, 2]
def baseStart_4688885 : Nat := 118140960795 + 4688885 * 2 ^ 59
def prefixEnd_4688885 : Nat := 4983230072969 + 3 ^ 40 * 4688885 * 2
def baseEnd_4688885 : Nat := 2407651738656992449573717

theorem tailTrace_4688885 : CollatzResearch.WordTrace tailWord_4688885 prefixEnd_4688885 2407651738656992449573717 := by
  unfold tailWord_4688885
  simp only [CollatzResearch.WordTrace]
  refine ⟨171017685617977917648340109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114011790411985278432226739 171017685617977917648340109)
  ·
    refine ⟨64131632106741719118127541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171017685617977917648340109 64131632106741719118127541)
    ·
      refine ⟨6012340510007036167324457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64131632106741719118127541 6012340510007036167324457)
      ·
        refine ⟨4509255382505277125493343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6012340510007036167324457 4509255382505277125493343)
        ·
          refine ⟨6763883073757915688240015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4509255382505277125493343 6763883073757915688240015)
          ·
            refine ⟨10145824610636873532360023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6763883073757915688240015 10145824610636873532360023)
            ·
              refine ⟨15218736915955310298540035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10145824610636873532360023 15218736915955310298540035)
              ·
                refine ⟨22828105373932965447810053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15218736915955310298540035 22828105373932965447810053)
                ·
                  refine ⟨4280269757612431021464385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22828105373932965447810053 4280269757612431021464385)
                  ·
                    refine ⟨3210202318209323266098289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4280269757612431021464385 3210202318209323266098289)
                    ·
                      refine ⟨2407651738656992449573717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3210202318209323266098289 2407651738656992449573717)
                      ·
                        rfl

theorem cell23_4688885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_4688885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688885 prefixEnd_4688885 := by exact prefixLift 4688885
  have htrace : WordTrace (prefixWord ++ tailWord_4688885) baseStart_4688885 baseEnd_4688885 := by
    simpa [prefixWord, tailWord_4688885, baseEnd_4688885] using wordTrace_append hprefix tailTrace_4688885
  have hstable : (prefixWord ++ tailWord_4688885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688885).length < 2 ^ (prefixWord ++ tailWord_4688885).sum := by decide
  have hdescent : baseEnd_4688885 < baseStart_4688885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688907 : List Nat := [1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 4]
def baseStart_4688907 : Nat := 118140960795 + 4688907 * 2 ^ 59
def prefixEnd_4688907 : Nat := 4983230072969 + 3 ^ 40 * 4688907 * 2
def baseEnd_4688907 : Nat := 2407663035231391363498615

theorem tailTrace_4688907 : CollatzResearch.WordTrace tailWord_4688907 prefixEnd_4688907 2407663035231391363498615 := by
  unfold tailWord_4688907
  simp only [CollatzResearch.WordTrace]
  refine ⟨171018488023898215405640975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114012325349265476937093983 171018488023898215405640975)
  ·
    refine ⟨256527732035847323108461463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171018488023898215405640975 256527732035847323108461463)
    ·
      refine ⟨384791598053770984662692195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256527732035847323108461463 384791598053770984662692195)
      ·
        refine ⟨577187397080656476994038293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384791598053770984662692195 577187397080656476994038293)
        ·
          refine ⟨27055659238155772359095545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 577187397080656476994038293 27055659238155772359095545)
          ·
            refine ⟨20291744428616829269321659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27055659238155772359095545 20291744428616829269321659)
            ·
              refine ⟨30437616642925243903982489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20291744428616829269321659 30437616642925243903982489)
              ·
                refine ⟨22828212482193932927986867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30437616642925243903982489 22828212482193932927986867)
                ·
                  refine ⟨34242318723290899391980301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22828212482193932927986867 34242318723290899391980301)
                  ·
                    refine ⟨12840869521234087271992613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34242318723290899391980301 12840869521234087271992613)
                    ·
                      refine ⟨2407663035231391363498615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12840869521234087271992613 2407663035231391363498615)
                      ·
                        rfl

theorem cell23_4688907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 4].length) (baseStart_4688907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688907 prefixEnd_4688907 := by exact prefixLift 4688907
  have htrace : WordTrace (prefixWord ++ tailWord_4688907) baseStart_4688907 baseEnd_4688907 := by
    simpa [prefixWord, tailWord_4688907, baseEnd_4688907] using wordTrace_append hprefix tailTrace_4688907
  have hstable : (prefixWord ++ tailWord_4688907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688907).length < 2 ^ (prefixWord ++ tailWord_4688907).sum := by decide
  have hdescent : baseEnd_4688907 < baseStart_4688907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688944 : List Nat := [2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 3]
def baseStart_4688944 : Nat := 118140960795 + 4688944 * 2 ^ 59
def prefixEnd_4688944 : Nat := 4983230072969 + 3 ^ 40 * 4688944 * 2
def baseEnd_4688944 : Nat := 2407682034015607718735945

theorem tailTrace_4688944 : CollatzResearch.WordTrace tailWord_4688944 prefixEnd_4688944 2407682034015607718735945 := by
  unfold tailWord_4688944
  simp only [CollatzResearch.WordTrace]
  refine ⟨85509918762382085362368943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114013225016509447149825257 85509918762382085362368943)
  ·
    refine ⟨128264878143573128043553415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85509918762382085362368943 128264878143573128043553415)
    ·
      refine ⟨192397317215359692065330123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128264878143573128043553415 192397317215359692065330123)
      ·
        refine ⟨288595975823039538097995185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192397317215359692065330123 288595975823039538097995185)
        ·
          refine ⟨216446981867279653573496389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288595975823039538097995185 216446981867279653573496389)
          ·
            refine ⟨40583809100114935045030573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 216446981867279653573496389 40583809100114935045030573)
            ·
              refine ⟨15218928412543100641886465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40583809100114935045030573 15218928412543100641886465)
              ·
                refine ⟨11414196309407325481414849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15218928412543100641886465 11414196309407325481414849)
                ·
                  refine ⟨8560647232055494111061137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11414196309407325481414849 8560647232055494111061137)
                  ·
                    refine ⟨6420485424041620583295853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8560647232055494111061137 6420485424041620583295853)
                    ·
                      refine ⟨2407682034015607718735945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6420485424041620583295853 2407682034015607718735945)
                      ·
                        rfl

theorem cell23_4688944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 3].length) (baseStart_4688944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688944 prefixEnd_4688944 := by exact prefixLift 4688944
  have htrace : WordTrace (prefixWord ++ tailWord_4688944) baseStart_4688944 baseEnd_4688944 := by
    simpa [prefixWord, tailWord_4688944, baseEnd_4688944] using wordTrace_append hprefix tailTrace_4688944
  have hstable : (prefixWord ++ tailWord_4688944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688944).length < 2 ^ (prefixWord ++ tailWord_4688944).sum := by decide
  have hdescent : baseEnd_4688944 < baseStart_4688944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4688947 : List Nat := [1, 1, 1, 2, 4, 1, 1, 6, 6]
def baseStart_4688947 : Nat := 118140960795 + 4688947 * 2 ^ 59
def prefixEnd_4688947 : Nat := 4983230072969 + 3 ^ 40 * 4688947 * 2
def baseEnd_4688947 : Nat := 267520397161952356333159

theorem tailTrace_4688947 : CollatzResearch.WordTrace tailWord_4688947 prefixEnd_4688947 267520397161952356333159 := by
  unfold tailWord_4688947
  simp only [CollatzResearch.WordTrace]
  refine ⟨171019946943753302237097095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114013297962502201491398063 171019946943753302237097095)
  ·
    refine ⟨256529920415629953355645643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171019946943753302237097095 256529920415629953355645643)
    ·
      refine ⟨384794880623444930033468465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256529920415629953355645643 384794880623444930033468465)
      ·
        refine ⟨288596160467583697525101349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 384794880623444930033468465 288596160467583697525101349)
        ·
          refine ⟨54111780087671943285956503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 288596160467583697525101349 54111780087671943285956503)
          ·
            refine ⟨81167670131507914928934755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54111780087671943285956503 81167670131507914928934755)
            ·
              refine ⟨121751505197261872393402133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81167670131507914928934755 121751505197261872393402133)
              ·
                refine ⟨5707101806121650268440725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 121751505197261872393402133 5707101806121650268440725)
                ·
                  refine ⟨267520397161952356333159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5707101806121650268440725 267520397161952356333159)
                  ·
                    rfl

theorem cell23_4688947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 6].length) (baseStart_4688947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4688947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4688947 prefixEnd_4688947 := by exact prefixLift 4688947
  have htrace : WordTrace (prefixWord ++ tailWord_4688947) baseStart_4688947 baseEnd_4688947 := by
    simpa [prefixWord, tailWord_4688947, baseEnd_4688947] using wordTrace_append hprefix tailTrace_4688947
  have hstable : (prefixWord ++ tailWord_4688947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4688947).length < 2 ^ (prefixWord ++ tailWord_4688947).sum := by decide
  have hdescent : baseEnd_4688947 < baseStart_4688947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4688947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689001 : List Nat := [1, 2, 1, 1, 1, 6, 2, 2, 2, 3, 2]
def baseStart_4689001 : Nat := 118140960795 + 4689001 * 2 ^ 59
def prefixEnd_4689001 : Nat := 4983230072969 + 3 ^ 40 * 4689001 * 2
def baseEnd_4689001 : Nat := 2407711302412913995723183

theorem tailTrace_4689001 : CollatzResearch.WordTrace tailWord_4689001 prefixEnd_4689001 2407711302412913995723183 := by
  unfold tailWord_4689001
  simp only [CollatzResearch.WordTrace]
  refine ⟨171021916485557669459562857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114014610990371779639708571 171021916485557669459562857)
  ·
    refine ⟨128266437364168252094672143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171021916485557669459562857 128266437364168252094672143)
    ·
      refine ⟨192399656046252378142008215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128266437364168252094672143 192399656046252378142008215)
      ·
        refine ⟨288599484069378567213012323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192399656046252378142008215 288599484069378567213012323)
        ·
          refine ⟨432899226104067850819518485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288599484069378567213012323 432899226104067850819518485)
          ·
            refine ⟨20292151223628180507164929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 432899226104067850819518485 20292151223628180507164929)
            ·
              refine ⟨15219113417721135380373697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20292151223628180507164929 15219113417721135380373697)
              ·
                refine ⟨11414335063290851535280273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15219113417721135380373697 11414335063290851535280273)
                ·
                  refine ⟨8560751297468138651460205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11414335063290851535280273 8560751297468138651460205)
                  ·
                    refine ⟨3210281736550551994297577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8560751297468138651460205 3210281736550551994297577)
                    ·
                      refine ⟨2407711302412913995723183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3210281736550551994297577 2407711302412913995723183)
                      ·
                        rfl

theorem cell23_4689001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 3, 2].length) (baseStart_4689001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689001 prefixEnd_4689001 := by exact prefixLift 4689001
  have htrace : WordTrace (prefixWord ++ tailWord_4689001) baseStart_4689001 baseEnd_4689001 := by
    simpa [prefixWord, tailWord_4689001, baseEnd_4689001] using wordTrace_append hprefix tailTrace_4689001
  have hstable : (prefixWord ++ tailWord_4689001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689001).length < 2 ^ (prefixWord ++ tailWord_4689001).sum := by decide
  have hdescent : baseEnd_4689001 < baseStart_4689001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689007 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 3, 6]
def baseStart_4689007 : Nat := 118140960795 + 4689007 * 2 ^ 59
def prefixEnd_4689007 : Nat := 4983230072969 + 3 ^ 40 * 4689007 * 2
def baseEnd_4689007 : Nat := 802571461098946990749385

theorem tailTrace_4689007 : CollatzResearch.WordTrace tailWord_4689007 prefixEnd_4689007 802571461098946990749385 := by
  unfold tailWord_4689007
  simp only [CollatzResearch.WordTrace]
  refine ⟨171022135323535932484281275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114014756882357288322854183 171022135323535932484281275)
  ·
    refine ⟨256533202985303898726421913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171022135323535932484281275 256533202985303898726421913)
    ·
      refine ⟨192399902238977924044816435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256533202985303898726421913 192399902238977924044816435)
      ·
        refine ⟨288599853358466886067224653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192399902238977924044816435 288599853358466886067224653)
        ·
          refine ⟨108224945009425082275209245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 288599853358466886067224653 108224945009425082275209245)
          ·
            refine ⟨40584354378534405853203467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108224945009425082275209245 40584354378534405853203467)
            ·
              refine ⟨60876531567801608779805201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40584354378534405853203467 60876531567801608779805201)
              ·
                refine ⟨45657398675851206584853901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60876531567801608779805201 45657398675851206584853901)
                ·
                  refine ⟨17121524503444202469320213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45657398675851206584853901 17121524503444202469320213)
                  ·
                    refine ⟨802571461098946990749385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17121524503444202469320213 802571461098946990749385)
                    ·
                      rfl

theorem cell23_4689007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 6].length) (baseStart_4689007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689007 prefixEnd_4689007 := by exact prefixLift 4689007
  have htrace : WordTrace (prefixWord ++ tailWord_4689007) baseStart_4689007 baseEnd_4689007 := by
    simpa [prefixWord, tailWord_4689007, baseEnd_4689007] using wordTrace_append hprefix tailTrace_4689007
  have hstable : (prefixWord ++ tailWord_4689007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689007).length < 2 ^ (prefixWord ++ tailWord_4689007).sum := by decide
  have hdescent : baseEnd_4689007 < baseStart_4689007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689008 : List Nat := [2, 1, 1, 1, 5, 1, 3, 4, 1, 1, 3]
def baseStart_4689008 : Nat := 118140960795 + 4689008 * 2 ^ 59
def prefixEnd_4689008 : Nat := 4983230072969 + 3 ^ 40 * 4689008 * 2
def baseEnd_4689008 : Nat := 2407714896777495468335651

theorem tailTrace_4689008 : CollatzResearch.WordTrace tailWord_4689008 prefixEnd_4689008 2407714896777495468335651 := by
  unfold tailWord_4689008
  simp only [CollatzResearch.WordTrace]
  refine ⟨85511085898266154827533839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114014781197688206436711785 85511085898266154827533839)
  ·
    refine ⟨128266628847399232241300759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85511085898266154827533839 128266628847399232241300759)
    ·
      refine ⟨192399943271098848361951139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128266628847399232241300759 192399943271098848361951139)
      ·
        refine ⟨288599914906648272542926709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192399943271098848361951139 288599914906648272542926709)
        ·
          refine ⟨27056242022498275550899379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 288599914906648272542926709 27056242022498275550899379)
          ·
            refine ⟨40584363033747413326349069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27056242022498275550899379 40584363033747413326349069)
            ·
              refine ⟨15219136137655279997380901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40584363033747413326349069 15219136137655279997380901)
              ·
                refine ⟨2853588025810364999508919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15219136137655279997380901 2853588025810364999508919)
                ·
                  refine ⟨4280382038715547499263379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2853588025810364999508919 4280382038715547499263379)
                  ·
                    refine ⟨6420573058073321248895069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4280382038715547499263379 6420573058073321248895069)
                    ·
                      refine ⟨2407714896777495468335651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6420573058073321248895069 2407714896777495468335651)
                      ·
                        rfl

theorem cell23_4689008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4, 1, 1, 3].length) (baseStart_4689008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689008 prefixEnd_4689008 := by exact prefixLift 4689008
  have htrace : WordTrace (prefixWord ++ tailWord_4689008) baseStart_4689008 baseEnd_4689008 := by
    simpa [prefixWord, tailWord_4689008, baseEnd_4689008] using wordTrace_append hprefix tailTrace_4689008
  have hstable : (prefixWord ++ tailWord_4689008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689008).length < 2 ^ (prefixWord ++ tailWord_4689008).sum := by decide
  have hdescent : baseEnd_4689008 < baseStart_4689008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689048 : List Nat := [2, 1, 2, 4, 2, 1, 4, 1, 1, 1, 4]
def baseStart_4689048 : Nat := 118140960795 + 4689048 * 2 ^ 59
def prefixEnd_4689048 : Nat := 4983230072969 + 3 ^ 40 * 4689048 * 2
def baseEnd_4689048 : Nat := 2407735436003675311835467

theorem tailTrace_4689048 : CollatzResearch.WordTrace tailWord_4689048 prefixEnd_4689048 2407735436003675311835467 := by
  unfold tailWord_4689048
  simp only [CollatzResearch.WordTrace]
  refine ⟨85511815358193698243261899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114015753810924930991015865 85511815358193698243261899)
  ·
    refine ⟨128267723037290547364892849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85511815358193698243261899 128267723037290547364892849)
    ·
      refine ⟨96200792277967910523669637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128267723037290547364892849 96200792277967910523669637)
      ·
        refine ⟨18037648552118983223188057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96200792277967910523669637 18037648552118983223188057)
        ·
          refine ⟨13528236414089237417391043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18037648552118983223188057 13528236414089237417391043)
          ·
            refine ⟨20292354621133856126086565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13528236414089237417391043 20292354621133856126086565)
            ·
              refine ⟨3804816491462598023641231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20292354621133856126086565 3804816491462598023641231)
              ·
                refine ⟨5707224737193897035461847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3804816491462598023641231 5707224737193897035461847)
                ·
                  refine ⟨8560837105790845553192771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5707224737193897035461847 8560837105790845553192771)
                  ·
                    refine ⟨12841255658686268329789157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8560837105790845553192771 12841255658686268329789157)
                    ·
                      refine ⟨2407735436003675311835467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12841255658686268329789157 2407735436003675311835467)
                      ·
                        rfl

theorem cell23_4689048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_4689048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689048 prefixEnd_4689048 := by exact prefixLift 4689048
  have htrace : WordTrace (prefixWord ++ tailWord_4689048) baseStart_4689048 baseEnd_4689048 := by
    simpa [prefixWord, tailWord_4689048, baseEnd_4689048] using wordTrace_append hprefix tailTrace_4689048
  have hstable : (prefixWord ++ tailWord_4689048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689048).length < 2 ^ (prefixWord ++ tailWord_4689048).sum := by decide
  have hdescent : baseEnd_4689048 < baseStart_4689048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689058 : List Nat := [3, 3, 1, 3, 2, 1, 1, 1, 4, 4]
def baseStart_4689058 : Nat := 118140960795 + 4689058 * 2 ^ 59
def prefixEnd_4689058 : Nat := 4983230072969 + 3 ^ 40 * 4689058 * 2
def baseEnd_4689058 : Nat := 802580190270073424236807

theorem tailTrace_4689058 : CollatzResearch.WordTrace tailWord_4689058 prefixEnd_4689058 802580190270073424236807 := by
  unfold tailWord_4689058
  simp only [CollatzResearch.WordTrace]
  refine ⟨42755998861587792048596957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114015996964234112129591885 42755998861587792048596957)
  ·
    refine ⟨16033499573095422018223859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42755998861587792048596957 16033499573095422018223859)
    ·
      refine ⟨24050249359643133027335789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16033499573095422018223859 24050249359643133027335789)
      ·
        refine ⟨9018843509866174885250921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24050249359643133027335789 9018843509866174885250921)
        ·
          refine ⟨6764132632399631163938191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9018843509866174885250921 6764132632399631163938191)
          ·
            refine ⟨10146198948599446745907287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6764132632399631163938191 10146198948599446745907287)
            ·
              refine ⟨15219298422899170118860931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10146198948599446745907287 15219298422899170118860931)
              ·
                refine ⟨22828947634348755178291397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15219298422899170118860931 22828947634348755178291397)
                ·
                  refine ⟨4280427681440391595929637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22828947634348755178291397 4280427681440391595929637)
                  ·
                    refine ⟨802580190270073424236807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4280427681440391595929637 802580190270073424236807)
                    ·
                      rfl

theorem cell23_4689058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_4689058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689058 prefixEnd_4689058 := by exact prefixLift 4689058
  have htrace : WordTrace (prefixWord ++ tailWord_4689058) baseStart_4689058 baseEnd_4689058 := by
    simpa [prefixWord, tailWord_4689058, baseEnd_4689058] using wordTrace_append hprefix tailTrace_4689058
  have hstable : (prefixWord ++ tailWord_4689058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689058).length < 2 ^ (prefixWord ++ tailWord_4689058).sum := by decide
  have hdescent : baseEnd_4689058 < baseStart_4689058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689081 : List Nat := [1, 2, 1, 4, 1, 3, 3, 1, 1, 3, 3]
def baseStart_4689081 : Nat := 118140960795 + 4689081 * 2 ^ 59
def prefixEnd_4689081 : Nat := 4983230072969 + 3 ^ 40 * 4689081 * 2
def baseEnd_4689081 : Nat := 2407752380865273682722815

theorem tailTrace_4689081 : CollatzResearch.WordTrace tailWord_4689081 prefixEnd_4689081 2407752380865273682722815 := by
  unfold tailWord_4689081
  simp only [CollatzResearch.WordTrace]
  refine ⟨171024834325267843122475097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114016556216845228748316731 171024834325267843122475097)
  ·
    refine ⟨128268625743950882341856323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171024834325267843122475097 128268625743950882341856323)
    ·
      refine ⟨192402938615926323512784485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128268625743950882341856323 192402938615926323512784485)
      ·
        refine ⟨36075550990486185658647091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 192402938615926323512784485 36075550990486185658647091)
        ·
          refine ⟨54113326485729278487970637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36075550990486185658647091 54113326485729278487970637)
          ·
            refine ⟨20292497432148479432988989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54113326485729278487970637 20292497432148479432988989)
            ·
              refine ⟨7609686537055679787370871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20292497432148479432988989 7609686537055679787370871)
              ·
                refine ⟨11414529805583519681056307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7609686537055679787370871 11414529805583519681056307)
                ·
                  refine ⟨17121794708375279521584461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11414529805583519681056307 17121794708375279521584461)
                  ·
                    refine ⟨6420673015640729820594173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17121794708375279521584461 6420673015640729820594173)
                    ·
                      refine ⟨2407752380865273682722815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6420673015640729820594173 2407752380865273682722815)
                      ·
                        rfl

theorem cell23_4689081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_4689081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689081 prefixEnd_4689081 := by exact prefixLift 4689081
  have htrace : WordTrace (prefixWord ++ tailWord_4689081) baseStart_4689081 baseEnd_4689081 := by
    simpa [prefixWord, tailWord_4689081, baseEnd_4689081] using wordTrace_append hprefix tailTrace_4689081
  have hstable : (prefixWord ++ tailWord_4689081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689081).length < 2 ^ (prefixWord ++ tailWord_4689081).sum := by decide
  have hdescent : baseEnd_4689081 < baseStart_4689081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689088 : List Nat := [2, 1, 1, 2, 7, 1, 2, 7]
def baseStart_4689088 : Nat := 118140960795 + 4689088 * 2 ^ 59
def prefixEnd_4689088 : Nat := 4983230072969 + 3 ^ 40 * 4689088 * 2
def baseEnd_4689088 : Nat := 89176147230735376123529

theorem tailTrace_4689088 : CollatzResearch.WordTrace tailWord_4689088 prefixEnd_4689088 89176147230735376123529 := by
  unfold tailWord_4689088
  simp only [CollatzResearch.WordTrace]
  refine ⟨85512544818121241658989959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114016726424161655545319945 85512544818121241658989959)
  ·
    refine ⟨128268817227181862488484939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85512544818121241658989959 128268817227181862488484939)
    ·
      refine ⟨192403225840772793732727409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128268817227181862488484939 192403225840772793732727409)
      ·
        refine ⟨144302419380579595299545557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192403225840772793732727409 144302419380579595299545557)
        ·
          refine ⟨3382087954232334264833099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 144302419380579595299545557 3382087954232334264833099)
          ·
            refine ⟨5073131931348501397249649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3382087954232334264833099 5073131931348501397249649)
            ·
              refine ⟨3804848948511376047937237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5073131931348501397249649 3804848948511376047937237)
              ·
                refine ⟨89176147230735376123529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3804848948511376047937237 89176147230735376123529)
                ·
                  rfl

theorem cell23_4689088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 7].length) (baseStart_4689088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689088 prefixEnd_4689088 := by exact prefixLift 4689088
  have htrace : WordTrace (prefixWord ++ tailWord_4689088) baseStart_4689088 baseEnd_4689088 := by
    simpa [prefixWord, tailWord_4689088, baseEnd_4689088] using wordTrace_append hprefix tailTrace_4689088
  have hstable : (prefixWord ++ tailWord_4689088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689088).length < 2 ^ (prefixWord ++ tailWord_4689088).sum := by decide
  have hdescent : baseEnd_4689088 < baseStart_4689088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689161 : List Nat := [1, 2, 1, 1, 3, 3, 2, 5, 5]
def baseStart_4689161 : Nat := 118140960795 + 4689161 * 2 ^ 59
def prefixEnd_4689161 : Nat := 4983230072969 + 3 ^ 40 * 4689161 * 2
def baseEnd_4689161 : Nat := 267532606590848152191383

theorem tailTrace_4689161 : CollatzResearch.WordTrace tailWord_4689161 prefixEnd_4689161 267532606590848152191383 := by
  unfold tailWord_4689161
  simp only [CollatzResearch.WordTrace]
  refine ⟨171027752164978016785387337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114018501443318677856924891 171027752164978016785387337)
  ·
    refine ⟨128270814123733512589040503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171027752164978016785387337 128270814123733512589040503)
    ·
      refine ⟨192406221185600268883560755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128270814123733512589040503 192406221185600268883560755)
      ·
        refine ⟨288609331778400403325341133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192406221185600268883560755 288609331778400403325341133)
        ·
          refine ⟨108228499416900151247002925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 288609331778400403325341133 108228499416900151247002925)
          ·
            refine ⟨40585687281337556717626097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108228499416900151247002925 40585687281337556717626097)
            ·
              refine ⟨30439265461003167538219573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40585687281337556717626097 30439265461003167538219573)
              ·
                refine ⟨2853681136969046956708085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30439265461003167538219573 2853681136969046956708085)
                ·
                  refine ⟨267532606590848152191383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2853681136969046956708085 267532606590848152191383)
                  ·
                    rfl

theorem cell23_4689161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5, 5].length) (baseStart_4689161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689161 prefixEnd_4689161 := by exact prefixLift 4689161
  have htrace : WordTrace (prefixWord ++ tailWord_4689161) baseStart_4689161 baseEnd_4689161 := by
    simpa [prefixWord, tailWord_4689161, baseEnd_4689161] using wordTrace_append hprefix tailTrace_4689161
  have hstable : (prefixWord ++ tailWord_4689161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689161).length < 2 ^ (prefixWord ++ tailWord_4689161).sum := by decide
  have hdescent : baseEnd_4689161 < baseStart_4689161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689178 : List Nat := [3, 1, 1, 3, 3, 2, 1, 4, 5]
def baseStart_4689178 : Nat := 118140960795 + 4689178 * 2 ^ 59
def prefixEnd_4689178 : Nat := 4983230072969 + 3 ^ 40 * 4689178 * 2
def baseEnd_4689178 : Nat := 267533576498751089245541

theorem tailTrace_4689178 : CollatzResearch.WordTrace tailWord_4689178 prefixEnd_4689178 267533576498751089245541 := by
  unfold tailWord_4689178
  simp only [CollatzResearch.WordTrace]
  refine ⟨42757093051479107172189047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114018914803944285792504125 42757093051479107172189047)
  ·
    refine ⟨64135639577218660758283571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42757093051479107172189047 64135639577218660758283571)
    ·
      refine ⟨96203459365827991137425357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64135639577218660758283571 96203459365827991137425357)
      ·
        refine ⟨36076297262185496676534509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96203459365827991137425357 36076297262185496676534509)
        ·
          refine ⟨13528611473319561253700441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36076297262185496676534509 13528611473319561253700441)
          ·
            refine ⟨10146458604989670940275331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13528611473319561253700441 10146458604989670940275331)
            ·
              refine ⟨15219687907484506410412997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10146458604989670940275331 15219687907484506410412997)
              ·
                refine ⟨2853691482653344951952437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15219687907484506410412997 2853691482653344951952437)
                ·
                  refine ⟨267533576498751089245541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2853691482653344951952437 267533576498751089245541)
                  ·
                    rfl

theorem cell23_4689178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4, 5].length) (baseStart_4689178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689178 prefixEnd_4689178 := by exact prefixLift 4689178
  have htrace : WordTrace (prefixWord ++ tailWord_4689178) baseStart_4689178 baseEnd_4689178 := by
    simpa [prefixWord, tailWord_4689178, baseEnd_4689178] using wordTrace_append hprefix tailTrace_4689178
  have hstable : (prefixWord ++ tailWord_4689178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689178).length < 2 ^ (prefixWord ++ tailWord_4689178).sum := by decide
  have hdescent : baseEnd_4689178 < baseStart_4689178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689228 : List Nat := [2, 2, 1, 3, 2, 2, 1, 2, 2, 4, 2]
def baseStart_4689228 : Nat := 118140960795 + 4689228 * 2 ^ 59
def prefixEnd_4689228 : Nat := 4983230072969 + 3 ^ 40 * 4689228 * 2
def baseEnd_4689228 : Nat := 2407827862521484607584639

theorem tailTrace_4689228 : CollatzResearch.WordTrace tailWord_4689228 prefixEnd_4689228 2407827862521484607584639 := by
  unfold tailWord_4689228
  simp only [CollatzResearch.WordTrace]
  refine ⟨85515097927867643614038169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114020130570490191485384225 85515097927867643614038169)
  ·
    refine ⟨64136323445900732710528627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85515097927867643614038169 64136323445900732710528627)
    ·
      refine ⟨96204485168851099065792941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64136323445900732710528627 96204485168851099065792941)
      ·
        refine ⟨36076681938319162149672353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96204485168851099065792941 36076681938319162149672353)
        ·
          refine ⟨27057511453739371612254265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36076681938319162149672353 27057511453739371612254265)
          ·
            refine ⟨20293133590304528709190699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27057511453739371612254265 20293133590304528709190699)
            ·
              refine ⟨30439700385456793063786049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20293133590304528709190699 30439700385456793063786049)
              ·
                refine ⟨22829775289092594797839537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30439700385456793063786049 22829775289092594797839537)
                ·
                  refine ⟨17122331466819446098379653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22829775289092594797839537 17122331466819446098379653)
                  ·
                    refine ⟨3210437150028646143446185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17122331466819446098379653 3210437150028646143446185)
                    ·
                      refine ⟨2407827862521484607584639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3210437150028646143446185 2407827862521484607584639)
                      ·
                        rfl

theorem cell23_4689228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_4689228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689228 prefixEnd_4689228 := by exact prefixLift 4689228
  have htrace : WordTrace (prefixWord ++ tailWord_4689228) baseStart_4689228 baseEnd_4689228 := by
    simpa [prefixWord, tailWord_4689228, baseEnd_4689228] using wordTrace_append hprefix tailTrace_4689228
  have hstable : (prefixWord ++ tailWord_4689228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689228).length < 2 ^ (prefixWord ++ tailWord_4689228).sum := by decide
  have hdescent : baseEnd_4689228 < baseStart_4689228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689282 : List Nat := [3, 4, 2, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_4689282 : Nat := 118140960795 + 4689282 * 2 ^ 59
def prefixEnd_4689282 : Nat := 4983230072969 + 3 ^ 40 * 4689282 * 2
def baseEnd_4689282 : Nat := 2407855590476827396309391

theorem tailTrace_4689282 : CollatzResearch.WordTrace tailWord_4689282 prefixEnd_4689282 2407855590476827396309391 := by
  unfold tailWord_4689282
  simp only [CollatzResearch.WordTrace]
  refine ⟨42758041349384913612635525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114021443598359769633694733 42758041349384913612635525)
  ·
    refine ⟨8017132753009671302369161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42758041349384913612635525 8017132753009671302369161)
    ·
      refine ⟨6012849564757253476776871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8017132753009671302369161 6012849564757253476776871)
      ·
        refine ⟨9019274347135880215165307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6012849564757253476776871 9019274347135880215165307)
        ·
          refine ⟨13528911520703820322747961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9019274347135880215165307 13528911520703820322747961)
          ·
            refine ⟨10146683640527865242060971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13528911520703820322747961 10146683640527865242060971)
            ·
              refine ⟨15220025460791797863091457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10146683640527865242060971 15220025460791797863091457)
              ·
                refine ⟨11415019095593848397318593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15220025460791797863091457 11415019095593848397318593)
                ·
                  refine ⟨8561264321695386297988945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11415019095593848397318593 8561264321695386297988945)
                  ·
                    refine ⟨6420948241271539723491709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8561264321695386297988945 6420948241271539723491709)
                    ·
                      refine ⟨2407855590476827396309391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6420948241271539723491709 2407855590476827396309391)
                      ·
                        rfl

theorem cell23_4689282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_4689282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689282 prefixEnd_4689282 := by exact prefixLift 4689282
  have htrace : WordTrace (prefixWord ++ tailWord_4689282) baseStart_4689282 baseEnd_4689282 := by
    simpa [prefixWord, tailWord_4689282, baseEnd_4689282] using wordTrace_append hprefix tailTrace_4689282
  have hstable : (prefixWord ++ tailWord_4689282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689282).length < 2 ^ (prefixWord ++ tailWord_4689282).sum := by decide
  have hdescent : baseEnd_4689282 < baseStart_4689282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689335 : List Nat := [1, 1, 3, 1, 3, 2, 5, 1, 1, 1, 4]
def baseStart_4689335 : Nat := 118140960795 + 4689335 * 2 ^ 59
def prefixEnd_4689335 : Nat := 4983230072969 + 3 ^ 40 * 4689335 * 2
def baseEnd_4689335 : Nat := 2407882804951515688946647

theorem tailTrace_4689335 : CollatzResearch.WordTrace tailWord_4689335 prefixEnd_4689335 2407882804951515688946647 := by
  unfold tailWord_4689335
  simp only [CollatzResearch.WordTrace]
  refine ⟨171034098466347644502221459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114022732310898429668147639 171034098466347644502221459)
  ·
    refine ⟨256551147699521466753332189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171034098466347644502221459 256551147699521466753332189)
    ·
      refine ⟨96206680387320550032499571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256551147699521466753332189 96206680387320550032499571)
      ·
        refine ⟨144310020580980825048749357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96206680387320550032499571 144310020580980825048749357)
        ·
          refine ⟨54116257717867809393281009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144310020580980825048749357 54116257717867809393281009)
          ·
            refine ⟨40587193288400857044960757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54116257717867809393281009 40587193288400857044960757)
            ·
              refine ⟨3805049370787580347965071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40587193288400857044960757 3805049370787580347965071)
              ·
                refine ⟨5707574056181370521947607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3805049370787580347965071 5707574056181370521947607)
                ·
                  refine ⟨8561361084272055782921411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5707574056181370521947607 8561361084272055782921411)
                  ·
                    refine ⟨12842041626408083674382117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8561361084272055782921411 12842041626408083674382117)
                    ·
                      refine ⟨2407882804951515688946647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12842041626408083674382117 2407882804951515688946647)
                      ·
                        rfl

theorem cell23_4689335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 1, 1, 4].length) (baseStart_4689335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689335 prefixEnd_4689335 := by exact prefixLift 4689335
  have htrace : WordTrace (prefixWord ++ tailWord_4689335) baseStart_4689335 baseEnd_4689335 := by
    simpa [prefixWord, tailWord_4689335, baseEnd_4689335] using wordTrace_append hprefix tailTrace_4689335
  have hstable : (prefixWord ++ tailWord_4689335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689335).length < 2 ^ (prefixWord ++ tailWord_4689335).sum := by decide
  have hdescent : baseEnd_4689335 < baseStart_4689335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689368 : List Nat := [2, 1, 2, 2, 2, 1, 3, 3, 1, 3, 3]
def baseStart_4689368 : Nat := 118140960795 + 4689368 * 2 ^ 59
def prefixEnd_4689368 : Nat := 4983230072969 + 3 ^ 40 * 4689368 * 2
def baseEnd_4689368 : Nat := 2407899749813114059833995

theorem tailTrace_4689368 : CollatzResearch.WordTrace tailWord_4689368 prefixEnd_4689368 2407899749813114059833995 := by
  unfold tailWord_4689368
  simp only [CollatzResearch.WordTrace]
  refine ⟨85517651037614045569086379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114023534716818727425448505 85517651037614045569086379)
  ·
    refine ⟨128276476556421068353629569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85517651037614045569086379 128276476556421068353629569)
    ·
      refine ⟨96207357417315801265222177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128276476556421068353629569 96207357417315801265222177)
      ·
        refine ⟨72155518062986850948916633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96207357417315801265222177 72155518062986850948916633)
        ·
          refine ⟨54116638547240138211687475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72155518062986850948916633 54116638547240138211687475)
          ·
            refine ⟨81174957820860207317531213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54116638547240138211687475 81174957820860207317531213)
            ·
              refine ⟨30440609182822577744074205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81174957820860207317531213 30440609182822577744074205)
              ·
                refine ⟨11415228443558466654027827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30440609182822577744074205 11415228443558466654027827)
                ·
                  refine ⟨17122842665337699981041741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11415228443558466654027827 17122842665337699981041741)
                  ·
                    refine ⟨6421065999501637492890653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17122842665337699981041741 6421065999501637492890653)
                    ·
                      refine ⟨2407899749813114059833995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6421065999501637492890653 2407899749813114059833995)
                      ·
                        rfl

theorem cell23_4689368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_4689368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689368 prefixEnd_4689368 := by exact prefixLift 4689368
  have htrace : WordTrace (prefixWord ++ tailWord_4689368) baseStart_4689368 baseEnd_4689368 := by
    simpa [prefixWord, tailWord_4689368, baseEnd_4689368] using wordTrace_append hprefix tailTrace_4689368
  have hstable : (prefixWord ++ tailWord_4689368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689368).length < 2 ^ (prefixWord ++ tailWord_4689368).sum := by decide
  have hdescent : baseEnd_4689368 < baseStart_4689368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689386 : List Nat := [3, 1, 3, 1, 4, 1, 2, 3, 1, 2, 2]
def baseStart_4689386 : Nat := 118140960795 + 4689386 * 2 ^ 59
def prefixEnd_4689386 : Nat := 4983230072969 + 3 ^ 40 * 4689386 * 2
def baseEnd_4689386 : Nat := 2407908992464894989408913

theorem tailTrace_4689386 : CollatzResearch.WordTrace tailWord_4689386 prefixEnd_4689386 2407908992464894989408913 := by
  unfold tailWord_4689386
  simp only [CollatzResearch.WordTrace]
  refine ⟨42758989647290720053082003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114023972392775253474885341 42758989647290720053082003)
  ·
    refine ⟨64138484470936080079623005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42758989647290720053082003 64138484470936080079623005)
    ·
      refine ⟨24051931676601030029858627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64138484470936080079623005 24051931676601030029858627)
      ·
        refine ⟨36077897514901545044787941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24051931676601030029858627 36077897514901545044787941)
        ·
          refine ⟨6764605784044039695897739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36077897514901545044787941 6764605784044039695897739)
          ·
            refine ⟨10146908676066059543846609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6764605784044039695897739 10146908676066059543846609)
            ·
              refine ⟨7610181507049544657884957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10146908676066059543846609 7610181507049544657884957)
              ·
                refine ⟨2853818065143579246706859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7610181507049544657884957 2853818065143579246706859)
                ·
                  refine ⟨4280727097715368870060289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2853818065143579246706859 4280727097715368870060289)
                  ·
                    refine ⟨3210545323286526652545217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4280727097715368870060289 3210545323286526652545217)
                    ·
                      refine ⟨2407908992464894989408913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3210545323286526652545217 2407908992464894989408913)
                      ·
                        rfl

theorem cell23_4689386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_4689386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689386 prefixEnd_4689386 := by exact prefixLift 4689386
  have htrace : WordTrace (prefixWord ++ tailWord_4689386) baseStart_4689386 baseEnd_4689386 := by
    simpa [prefixWord, tailWord_4689386, baseEnd_4689386] using wordTrace_append hprefix tailTrace_4689386
  have hstable : (prefixWord ++ tailWord_4689386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689386).length < 2 ^ (prefixWord ++ tailWord_4689386).sum := by decide
  have hdescent : baseEnd_4689386 < baseStart_4689386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689408 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 1, 10, 2]
def baseStart_4689408 : Nat := 118140960795 + 4689408 * 2 ^ 59
def prefixEnd_4689408 : Nat := 4983230072969 + 3 ^ 40 * 4689408 * 2
def baseEnd_4689408 : Nat := 2407920289039293903333811

theorem tailTrace_4689408 : CollatzResearch.WordTrace tailWord_4689408 prefixEnd_4689408 2407920289039293903333811 := by
  unfold tailWord_4689408
  simp only [CollatzResearch.WordTrace]
  refine ⟨85518380497541588984814439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114024507330055451979752585 85518380497541588984814439)
  ·
    refine ⟨128277570746312383477221659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85518380497541588984814439 128277570746312383477221659)
    ·
      refine ⟨192416356119468575215832489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128277570746312383477221659 192416356119468575215832489)
      ·
        refine ⟨144312267089601431411874367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192416356119468575215832489 144312267089601431411874367)
        ·
          refine ⟨216468400634402147117811551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144312267089601431411874367 216468400634402147117811551)
          ·
            refine ⟨324702600951603220676717327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216468400634402147117811551 324702600951603220676717327)
            ·
              refine ⟨487053901427404831015075991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324702600951603220676717327 487053901427404831015075991)
              ·
                refine ⟨730580852141107246522613987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 487053901427404831015075991 730580852141107246522613987)
                ·
                  refine ⟨1095871278211660869783920981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 730580852141107246522613987 1095871278211660869783920981)
                  ·
                    refine ⟨3210560385385725204445081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1095871278211660869783920981 3210560385385725204445081)
                    ·
                      refine ⟨2407920289039293903333811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3210560385385725204445081 2407920289039293903333811)
                      ·
                        rfl

theorem cell23_4689408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 10, 2].length) (baseStart_4689408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689408 prefixEnd_4689408 := by exact prefixLift 4689408
  have htrace : WordTrace (prefixWord ++ tailWord_4689408) baseStart_4689408 baseEnd_4689408 := by
    simpa [prefixWord, tailWord_4689408, baseEnd_4689408] using wordTrace_append hprefix tailTrace_4689408
  have hstable : (prefixWord ++ tailWord_4689408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689408).length < 2 ^ (prefixWord ++ tailWord_4689408).sum := by decide
  have hdescent : baseEnd_4689408 < baseStart_4689408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689411 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 5]
def baseStart_4689411 : Nat := 118140960795 + 4689411 * 2 ^ 59
def prefixEnd_4689411 : Nat := 4983230072969 + 3 ^ 40 * 4689411 * 2
def baseEnd_4689411 : Nat := 2407921829481257391596297

theorem tailTrace_4689411 : CollatzResearch.WordTrace tailWord_4689411 prefixEnd_4689411 2407921829481257391596297 := by
  unfold tailWord_4689411
  simp only [CollatzResearch.WordTrace]
  refine ⟨171036870414072309481988087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114024580276048206321325391 171036870414072309481988087)
  ·
    refine ⟨256555305621108464222982131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171036870414072309481988087 256555305621108464222982131)
    ·
      refine ⟨384832958431662696334473197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256555305621108464222982131 384832958431662696334473197)
      ·
        refine ⟨144312359411873511125427449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 384832958431662696334473197 144312359411873511125427449)
        ·
          refine ⟨108234269558905133344070587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144312359411873511125427449 108234269558905133344070587)
          ·
            refine ⟨162351404338357700016105881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108234269558905133344070587 162351404338357700016105881)
            ·
              refine ⟨121763553253768275012079411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162351404338357700016105881 121763553253768275012079411)
              ·
                refine ⟨182645329880652412518119117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121763553253768275012079411 182645329880652412518119117)
                ·
                  refine ⟨68491998705244654694294669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 182645329880652412518119117 68491998705244654694294669)
                  ·
                    refine ⟨25684499514466745510360501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68491998705244654694294669 25684499514466745510360501)
                    ·
                      refine ⟨2407921829481257391596297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25684499514466745510360501 2407921829481257391596297)
                      ·
                        rfl

theorem cell23_4689411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_4689411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689411 prefixEnd_4689411 := by exact prefixLift 4689411
  have htrace : WordTrace (prefixWord ++ tailWord_4689411) baseStart_4689411 baseEnd_4689411 := by
    simpa [prefixWord, tailWord_4689411, baseEnd_4689411] using wordTrace_append hprefix tailTrace_4689411
  have hstable : (prefixWord ++ tailWord_4689411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689411).length < 2 ^ (prefixWord ++ tailWord_4689411).sum := by decide
  have hdescent : baseEnd_4689411 < baseStart_4689411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689418 : List Nat := [3, 1, 2, 2, 2, 2, 2, 1, 2, 6]
def baseStart_4689418 : Nat := 118140960795 + 4689418 * 2 ^ 59
def prefixEnd_4689418 : Nat := 4983230072969 + 3 ^ 40 * 4689418 * 2
def baseEnd_4689418 : Nat := 802641807948612954736255

theorem tailTrace_4689418 : CollatzResearch.WordTrace tailWord_4689418 prefixEnd_4689418 802641807948612954736255 := by
  unfold tailWord_4689418
  simp only [CollatzResearch.WordTrace]
  refine ⟨42759281431261737419373227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114024750483364633118328605 42759281431261737419373227)
  ·
    refine ⟨64138922146892606129059841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42759281431261737419373227 64138922146892606129059841)
    ·
      refine ⟨48104191610169454596794881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64138922146892606129059841 48104191610169454596794881)
      ·
        refine ⟨36078143707627090947596161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48104191610169454596794881 36078143707627090947596161)
        ·
          refine ⟨27058607780720318210697121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36078143707627090947596161 27058607780720318210697121)
          ·
            refine ⟨20293955835540238658022841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27058607780720318210697121 20293955835540238658022841)
            ·
              refine ⟨15220466876655178993517131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20293955835540238658022841 15220466876655178993517131)
              ·
                refine ⟨22830700314982768490275697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15220466876655178993517131 22830700314982768490275697)
                ·
                  refine ⟨17123025236237076367706773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22830700314982768490275697 17123025236237076367706773)
                  ·
                    refine ⟨802641807948612954736255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17123025236237076367706773 802641807948612954736255)
                    ·
                      rfl

theorem cell23_4689418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_4689418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689418 prefixEnd_4689418 := by exact prefixLift 4689418
  have htrace : WordTrace (prefixWord ++ tailWord_4689418) baseStart_4689418 baseEnd_4689418 := by
    simpa [prefixWord, tailWord_4689418, baseEnd_4689418] using wordTrace_append hprefix tailTrace_4689418
  have hstable : (prefixWord ++ tailWord_4689418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689418).length < 2 ^ (prefixWord ++ tailWord_4689418).sum := by decide
  have hdescent : baseEnd_4689418 < baseStart_4689418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689419 : List Nat := [1, 1, 1, 1, 8, 1, 3, 1, 2, 1, 3]
def baseStart_4689419 : Nat := 118140960795 + 4689419 * 2 ^ 59
def prefixEnd_4689419 : Nat := 4983230072969 + 3 ^ 40 * 4689419 * 2
def baseEnd_4689419 : Nat := 2407925937326493360296261

theorem tailTrace_4689419 : CollatzResearch.WordTrace tailWord_4689419 prefixEnd_4689419 2407925937326493360296261 := by
  unfold tailWord_4689419
  simp only [CollatzResearch.WordTrace]
  refine ⟨171037162198043326848279311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114024774798695551232186207 171037162198043326848279311)
  ·
    refine ⟨256555743297064990272418967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171037162198043326848279311 256555743297064990272418967)
    ·
      refine ⟨384833614945597485408628451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256555743297064990272418967 384833614945597485408628451)
      ·
        refine ⟨577250422418396228112942677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384833614945597485408628451 577250422418396228112942677)
        ·
          refine ⟨6764653387715580798198547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 577250422418396228112942677 6764653387715580798198547)
          ·
            refine ⟨10146980081573371197297821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6764653387715580798198547 10146980081573371197297821)
            ·
              refine ⟨3805117530590014198986683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10146980081573371197297821 3805117530590014198986683)
              ·
                refine ⟨5707676295885021298480025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3805117530590014198986683 5707676295885021298480025)
                ·
                  refine ⟨4280757221913765973860019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5707676295885021298480025 4280757221913765973860019)
                  ·
                    refine ⟨6421135832870648960790029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4280757221913765973860019 6421135832870648960790029)
                    ·
                      refine ⟨2407925937326493360296261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6421135832870648960790029 2407925937326493360296261)
                      ·
                        rfl

theorem cell23_4689419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 2, 1, 3].length) (baseStart_4689419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689419 prefixEnd_4689419 := by exact prefixLift 4689419
  have htrace : WordTrace (prefixWord ++ tailWord_4689419) baseStart_4689419 baseEnd_4689419 := by
    simpa [prefixWord, tailWord_4689419, baseEnd_4689419] using wordTrace_append hprefix tailTrace_4689419
  have hstable : (prefixWord ++ tailWord_4689419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689419).length < 2 ^ (prefixWord ++ tailWord_4689419).sum := by decide
  have hdescent : baseEnd_4689419 < baseStart_4689419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689442 : List Nat := [3, 3, 1, 1, 1, 1, 3, 2, 4, 2, 2]
def baseStart_4689442 : Nat := 118140960795 + 4689442 * 2 ^ 59
def prefixEnd_4689442 : Nat := 4983230072969 + 3 ^ 40 * 4689442 * 2
def baseEnd_4689442 : Nat := 2407937747381546770308655

theorem tailTrace_4689442 : CollatzResearch.WordTrace tailWord_4689442 prefixEnd_4689442 2407937747381546770308655 := by
  unfold tailWord_4689442
  simp only [CollatzResearch.WordTrace]
  refine ⟨42759500269240000444091645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114025334051306667850911053 42759500269240000444091645)
  ·
    refine ⟨16034812600965000166534367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42759500269240000444091645 16034812600965000166534367)
    ·
      refine ⟨24052218901447500249801551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16034812600965000166534367 24052218901447500249801551)
      ·
        refine ⟨36078328352171250374702327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24052218901447500249801551 36078328352171250374702327)
        ·
          refine ⟨54117492528256875562053491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36078328352171250374702327 54117492528256875562053491)
          ·
            refine ⟨81176238792385313343080237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54117492528256875562053491 81176238792385313343080237)
            ·
              refine ⟨30441089547144492503655089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81176238792385313343080237 30441089547144492503655089)
              ·
                refine ⟨22830817160358369377741317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30441089547144492503655089 22830817160358369377741317)
                ·
                  refine ⟨4280778217567194258326497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22830817160358369377741317 4280778217567194258326497)
                  ·
                    refine ⟨3210583663175395693744873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4280778217567194258326497 3210583663175395693744873)
                    ·
                      refine ⟨2407937747381546770308655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3210583663175395693744873 2407937747381546770308655)
                      ·
                        rfl

theorem cell23_4689442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_4689442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689442 prefixEnd_4689442 := by exact prefixLift 4689442
  have htrace : WordTrace (prefixWord ++ tailWord_4689442) baseStart_4689442 baseEnd_4689442 := by
    simpa [prefixWord, tailWord_4689442, baseEnd_4689442] using wordTrace_append hprefix tailTrace_4689442
  have hstable : (prefixWord ++ tailWord_4689442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689442).length < 2 ^ (prefixWord ++ tailWord_4689442).sum := by decide
  have hdescent : baseEnd_4689442 < baseStart_4689442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689451 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 6]
def baseStart_4689451 : Nat := 118140960795 + 4689451 * 2 ^ 59
def prefixEnd_4689451 : Nat := 4983230072969 + 3 ^ 40 * 4689451 * 2
def baseEnd_4689451 : Nat := 2407942368707437235096113

theorem tailTrace_4689451 : CollatzResearch.WordTrace tailWord_4689451 prefixEnd_4689451 2407942368707437235096113 := by
  unfold tailWord_4689451
  simp only [CollatzResearch.WordTrace]
  refine ⟨171038329333927396313444207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114025552889284930875629471 171038329333927396313444207)
  ·
    refine ⟨256557494000891094470166311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171038329333927396313444207 256557494000891094470166311)
    ·
      refine ⟨384836241001336641705249467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256557494000891094470166311 384836241001336641705249467)
      ·
        refine ⟨577254361502004962557874201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384836241001336641705249467 577254361502004962557874201)
        ·
          refine ⟨432940771126503721918405651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 577254361502004962557874201 432940771126503721918405651)
          ·
            refine ⟨649411156689755582877608477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432940771126503721918405651 649411156689755582877608477)
            ·
              refine ⟨243529183758658343579103179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 649411156689755582877608477 243529183758658343579103179)
              ·
                refine ⟨365293775637987515368654769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243529183758658343579103179 365293775637987515368654769)
                ·
                  refine ⟨273970331728490636526491077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 365293775637987515368654769 273970331728490636526491077)
                  ·
                    refine ⟨51369437199091994348717077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 273970331728490636526491077 51369437199091994348717077)
                    ·
                      refine ⟨2407942368707437235096113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51369437199091994348717077 2407942368707437235096113)
                      ·
                        rfl

theorem cell23_4689451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 6].length) (baseStart_4689451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689451 prefixEnd_4689451 := by exact prefixLift 4689451
  have htrace : WordTrace (prefixWord ++ tailWord_4689451) baseStart_4689451 baseEnd_4689451 := by
    simpa [prefixWord, tailWord_4689451, baseEnd_4689451] using wordTrace_append hprefix tailTrace_4689451
  have hstable : (prefixWord ++ tailWord_4689451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689451).length < 2 ^ (prefixWord ++ tailWord_4689451).sum := by decide
  have hdescent : baseEnd_4689451 < baseStart_4689451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689465 : List Nat := [1, 2, 1, 5, 1, 4, 1, 1, 7]
def baseStart_4689465 : Nat := 118140960795 + 4689465 * 2 ^ 59
def prefixEnd_4689465 : Nat := 4983230072969 + 3 ^ 40 * 4689465 * 2
def baseEnd_4689465 : Nat := 267549950826288908924561

theorem tailTrace_4689465 : CollatzResearch.WordTrace tailWord_4689465 prefixEnd_4689465 267549950826288908924561 := by
  unfold tailWord_4689465
  simp only [CollatzResearch.WordTrace]
  refine ⟨171038839955876676704453849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114025893303917784469635899 171038839955876676704453849)
  ·
    refine ⟨128279129966907507528340387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171038839955876676704453849 128279129966907507528340387)
    ·
      refine ⟨192418694950361261292510581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128279129966907507528340387 192418694950361261292510581)
      ·
        refine ⟨18039252651596368246172867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 192418694950361261292510581 18039252651596368246172867)
        ·
          refine ⟨27058878977394552369259301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18039252651596368246172867 27058878977394552369259301)
          ·
            refine ⟨5073539808261478569236119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27058878977394552369259301 5073539808261478569236119)
            ·
              refine ⟨7610309712392217853854179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5073539808261478569236119 7610309712392217853854179)
              ·
                refine ⟨11415464568588326780781269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7610309712392217853854179 11415464568588326780781269)
                ·
                  refine ⟨267549950826288908924561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11415464568588326780781269 267549950826288908924561)
                  ·
                    rfl

theorem cell23_4689465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 7].length) (baseStart_4689465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689465 prefixEnd_4689465 := by exact prefixLift 4689465
  have htrace : WordTrace (prefixWord ++ tailWord_4689465) baseStart_4689465 baseEnd_4689465 := by
    simpa [prefixWord, tailWord_4689465, baseEnd_4689465] using wordTrace_append hprefix tailTrace_4689465
  have hstable : (prefixWord ++ tailWord_4689465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689465).length < 2 ^ (prefixWord ++ tailWord_4689465).sum := by decide
  have hdescent : baseEnd_4689465 < baseStart_4689465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689495 : List Nat := [1, 1, 3, 2, 2, 4, 2, 1, 2, 5]
def baseStart_4689495 : Nat := 118140960795 + 4689495 * 2 ^ 59
def prefixEnd_4689495 : Nat := 4983230072969 + 3 ^ 40 * 4689495 * 2
def baseEnd_4689495 : Nat := 802654987285411687648637

theorem tailTrace_4689495 : CollatzResearch.WordTrace tailWord_4689495 prefixEnd_4689495 802654987285411687648637 := by
  unfold tailWord_4689495
  simp only [CollatzResearch.WordTrace]
  refine ⟨171039934145767991828045939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114026622763845327885363959 171039934145767991828045939)
  ·
    refine ⟨256559901218651987742068909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171039934145767991828045939 256559901218651987742068909)
    ·
      refine ⟨96209962956994495403275841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256559901218651987742068909 96209962956994495403275841)
      ·
        refine ⟨72157472217745871552456881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96209962956994495403275841 72157472217745871552456881)
        ·
          refine ⟨54118104163309403664342661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72157472217745871552456881 54118104163309403664342661)
          ·
            refine ⟨10147144530620513187064249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54118104163309403664342661 10147144530620513187064249)
            ·
              refine ⟨7610358397965384890298187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10147144530620513187064249 7610358397965384890298187)
              ·
                refine ⟨11415537596948077335447281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7610358397965384890298187 11415537596948077335447281)
                ·
                  refine ⟨8561653197711058001585461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11415537596948077335447281 8561653197711058001585461)
                  ·
                    refine ⟨802654987285411687648637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8561653197711058001585461 802654987285411687648637)
                    ·
                      rfl

theorem cell23_4689495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 5].length) (baseStart_4689495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689495 prefixEnd_4689495 := by exact prefixLift 4689495
  have htrace : WordTrace (prefixWord ++ tailWord_4689495) baseStart_4689495 baseEnd_4689495 := by
    simpa [prefixWord, tailWord_4689495, baseEnd_4689495] using wordTrace_append hprefix tailTrace_4689495
  have hstable : (prefixWord ++ tailWord_4689495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689495).length < 2 ^ (prefixWord ++ tailWord_4689495).sum := by decide
  have hdescent : baseEnd_4689495 < baseStart_4689495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689498 : List Nat := [3, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4]
def baseStart_4689498 : Nat := 118140960795 + 4689498 * 2 ^ 59
def prefixEnd_4689498 : Nat := 4983230072969 + 3 ^ 40 * 4689498 * 2
def baseEnd_4689498 : Nat := 2407966502298198551208397

theorem tailTrace_4689498 : CollatzResearch.WordTrace tailWord_4689498 prefixEnd_4689498 2407966502298198551208397 := by
  unfold tailWord_4689498
  simp only [CollatzResearch.WordTrace]
  refine ⟨42760010891189280835101287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114026695709838082226936765 42760010891189280835101287)
  ·
    refine ⟨64140016336783921252651931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42760010891189280835101287 64140016336783921252651931)
    ·
      refine ⟨96210024505175881878977897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64140016336783921252651931 96210024505175881878977897)
      ·
        refine ⟨72157518378881911409233423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96210024505175881878977897 72157518378881911409233423)
        ·
          refine ⟨108236277568322867113850135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72157518378881911409233423 108236277568322867113850135)
          ·
            refine ⟨162354416352484300670775203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108236277568322867113850135 162354416352484300670775203)
            ·
              refine ⟨243531624528726451006162805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162354416352484300670775203 243531624528726451006162805)
              ·
                refine ⟨22831089799568104781827763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 243531624528726451006162805 22831089799568104781827763)
                ·
                  refine ⟨34246634699352157172741645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22831089799568104781827763 34246634699352157172741645)
                  ·
                    refine ⟨12842488012257058939778117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34246634699352157172741645 12842488012257058939778117)
                    ·
                      refine ⟨2407966502298198551208397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12842488012257058939778117 2407966502298198551208397)
                      ·
                        rfl

theorem cell23_4689498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_4689498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689498 prefixEnd_4689498 := by exact prefixLift 4689498
  have htrace : WordTrace (prefixWord ++ tailWord_4689498) baseStart_4689498 baseEnd_4689498 := by
    simpa [prefixWord, tailWord_4689498, baseEnd_4689498] using wordTrace_append hprefix tailTrace_4689498
  have hstable : (prefixWord ++ tailWord_4689498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689498).length < 2 ^ (prefixWord ++ tailWord_4689498).sum := by decide
  have hdescent : baseEnd_4689498 < baseStart_4689498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689559 : List Nat := [1, 1, 3, 3, 2, 3, 2, 3, 1, 4]
def baseStart_4689559 : Nat := 118140960795 + 4689559 * 2 ^ 59
def prefixEnd_4689559 : Nat := 4983230072969 + 3 ^ 40 * 4689559 * 2
def baseEnd_4689559 : Nat := 802665941539374270848539

theorem tailTrace_4689559 : CollatzResearch.WordTrace tailWord_4689559 prefixEnd_4689559 802665941539374270848539 := by
  unfold tailWord_4689559
  simp only [CollatzResearch.WordTrace]
  refine ⟨171042268417536130758375731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114028178945024087172250487 171042268417536130758375731)
  ·
    refine ⟨256563402626304196137563597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171042268417536130758375731 256563402626304196137563597)
    ·
      refine ⟨96211275984864073551586349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256563402626304196137563597 96211275984864073551586349)
      ·
        refine ⟨36079228494324027581844881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96211275984864073551586349 36079228494324027581844881)
        ·
          refine ⟨27059421370743020686383661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36079228494324027581844881 27059421370743020686383661)
          ·
            refine ⟨10147283014028632757393873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27059421370743020686383661 10147283014028632757393873)
            ·
              refine ⟨7610462260521474568045405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10147283014028632757393873 7610462260521474568045405)
              ·
                refine ⟨2853923347695552963017027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7610462260521474568045405 2853923347695552963017027)
                ·
                  refine ⟨4280885021543329444525541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2853923347695552963017027 4280885021543329444525541)
                  ·
                    refine ⟨802665941539374270848539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4280885021543329444525541 802665941539374270848539)
                    ·
                      rfl

theorem cell23_4689559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3, 1, 4].length) (baseStart_4689559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689559 prefixEnd_4689559 := by exact prefixLift 4689559
  have htrace : WordTrace (prefixWord ++ tailWord_4689559) baseStart_4689559 baseEnd_4689559 := by
    simpa [prefixWord, tailWord_4689559, baseEnd_4689559] using wordTrace_append hprefix tailTrace_4689559
  have hstable : (prefixWord ++ tailWord_4689559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689559).length < 2 ^ (prefixWord ++ tailWord_4689559).sum := by decide
  have hdescent : baseEnd_4689559 < baseStart_4689559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689572 : List Nat := [2, 3, 1, 2, 2, 4, 1, 2, 6]
def baseStart_4689572 : Nat := 118140960795 + 4689572 * 2 ^ 59
def prefixEnd_4689572 : Nat := 4983230072969 + 3 ^ 40 * 4689572 * 2
def baseEnd_4689572 : Nat := 267556055540736806853673

theorem tailTrace_4689572 : CollatzResearch.WordTrace tailWord_4689572 prefixEnd_4689572 267556055540736806853673 := by
  unfold tailWord_4689572
  simp only [CollatzResearch.WordTrace]
  refine ⟨85521371283244516989299485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114028495044326022652399313 85521371283244516989299485)
  ·
    refine ⟨32070514231216693870987307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85521371283244516989299485 32070514231216693870987307)
    ·
      refine ⟨48105771346825040806480961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32070514231216693870987307 48105771346825040806480961)
      ·
        refine ⟨36079328510118780604860721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48105771346825040806480961 36079328510118780604860721)
        ·
          refine ⟨27059496382589085453645541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36079328510118780604860721 27059496382589085453645541)
          ·
            refine ⟨5073655571735453522558539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27059496382589085453645541 5073655571735453522558539)
            ·
              refine ⟨7610483357603180283837809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5073655571735453522558539 7610483357603180283837809)
              ·
                refine ⟨5707862518202385212878357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7610483357603180283837809 5707862518202385212878357)
                ·
                  refine ⟨267556055540736806853673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5707862518202385212878357 267556055540736806853673)
                  ·
                    rfl

theorem cell23_4689572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 6].length) (baseStart_4689572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689572 prefixEnd_4689572 := by exact prefixLift 4689572
  have htrace : WordTrace (prefixWord ++ tailWord_4689572) baseStart_4689572 baseEnd_4689572 := by
    simpa [prefixWord, tailWord_4689572, baseEnd_4689572] using wordTrace_append hprefix tailTrace_4689572
  have hstable : (prefixWord ++ tailWord_4689572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689572).length < 2 ^ (prefixWord ++ tailWord_4689572).sum := by decide
  have hdescent : baseEnd_4689572 < baseStart_4689572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689589 : List Nat := [1, 3, 3, 3, 2, 1, 3, 1, 6]
def baseStart_4689589 : Nat := 118140960795 + 4689589 * 2 ^ 59
def prefixEnd_4689589 : Nat := 4983230072969 + 3 ^ 40 * 4689589 * 2
def baseEnd_4689589 : Nat := 267557025448639743907831

theorem tailTrace_4689589 : CollatzResearch.WordTrace tailWord_4689589 prefixEnd_4689589 267557025448639743907831 := by
  unfold tailWord_4689589
  simp only [CollatzResearch.WordTrace]
  refine ⟨171043362607427445881967821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114028908404951630587978547 171043362607427445881967821)
  ·
    refine ⟨64141260977785292205737933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171043362607427445881967821 64141260977785292205737933)
    ·
      refine ⟨24052972866669484577151725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64141260977785292205737933 24052972866669484577151725)
      ·
        refine ⟨9019864825001056716431897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24052972866669484577151725 9019864825001056716431897)
        ·
          refine ⟨6764898618750792537323923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9019864825001056716431897 6764898618750792537323923)
          ·
            refine ⟨10147347928126188805985885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6764898618750792537323923 10147347928126188805985885)
            ·
              refine ⟨3805255473047320802244707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10147347928126188805985885 3805255473047320802244707)
              ·
                refine ⟨5707883209570981203367061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3805255473047320802244707 5707883209570981203367061)
                ·
                  refine ⟨267557025448639743907831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5707883209570981203367061 267557025448639743907831)
                  ·
                    rfl

theorem cell23_4689589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 6].length) (baseStart_4689589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689589 prefixEnd_4689589 := by exact prefixLift 4689589
  have htrace : WordTrace (prefixWord ++ tailWord_4689589) baseStart_4689589 baseEnd_4689589 := by
    simpa [prefixWord, tailWord_4689589, baseEnd_4689589] using wordTrace_append hprefix tailTrace_4689589
  have hstable : (prefixWord ++ tailWord_4689589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689589).length < 2 ^ (prefixWord ++ tailWord_4689589).sum := by decide
  have hdescent : baseEnd_4689589 < baseStart_4689589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689625 : List Nat := [1, 2, 1, 2, 3, 3, 1, 3, 1, 1, 5]
def baseStart_4689625 : Nat := 118140960795 + 4689625 * 2 ^ 59
def prefixEnd_4689625 : Nat := 4983230072969 + 3 ^ 40 * 4689625 * 2
def baseEnd_4689625 : Nat := 2408031714341319554320313

theorem tailTrace_4689625 : CollatzResearch.WordTrace tailWord_4689625 prefixEnd_4689625 2408031714341319554320313 := by
  unfold tailWord_4689625
  simp only [CollatzResearch.WordTrace]
  refine ⟨171044675635297024030278329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114029783756864682686852219 171044675635297024030278329)
  ·
    refine ⟨128283506726472768022708747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171044675635297024030278329 128283506726472768022708747)
    ·
      refine ⟨192425260089709152034063121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128283506726472768022708747 192425260089709152034063121)
      ·
        refine ⟨144318945067281864025547341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192425260089709152034063121 144318945067281864025547341)
        ·
          refine ⟨54119604400230699009580253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144318945067281864025547341 54119604400230699009580253)
          ·
            refine ⟨20294851650086512128592595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54119604400230699009580253 20294851650086512128592595)
            ·
              refine ⟨30442277475129768192888893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20294851650086512128592595 30442277475129768192888893)
              ·
                refine ⟨11415854053173663072333335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30442277475129768192888893 11415854053173663072333335)
                ·
                  refine ⟨17123781079760494608500003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11415854053173663072333335 17123781079760494608500003)
                  ·
                    refine ⟨25685671619640741912750005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17123781079760494608500003 25685671619640741912750005)
                    ·
                      refine ⟨2408031714341319554320313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25685671619640741912750005 2408031714341319554320313)
                      ·
                        rfl

theorem cell23_4689625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_4689625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689625 prefixEnd_4689625 := by exact prefixLift 4689625
  have htrace : WordTrace (prefixWord ++ tailWord_4689625) baseStart_4689625 baseEnd_4689625 := by
    simpa [prefixWord, tailWord_4689625, baseEnd_4689625] using wordTrace_append hprefix tailTrace_4689625
  have hstable : (prefixWord ++ tailWord_4689625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689625).length < 2 ^ (prefixWord ++ tailWord_4689625).sum := by decide
  have hdescent : baseEnd_4689625 < baseStart_4689625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689633 : List Nat := [1, 2, 3, 1, 5, 1, 3, 2, 1, 1, 3]
def baseStart_4689633 : Nat := 118140960795 + 4689633 * 2 ^ 59
def prefixEnd_4689633 : Nat := 4983230072969 + 3 ^ 40 * 4689633 * 2
def baseEnd_4689633 : Nat := 2408035822186555523020277

theorem tailTrace_4689633 : CollatzResearch.WordTrace tailWord_4689633 prefixEnd_4689633 2408035822186555523020277 := by
  unfold tailWord_4689633
  simp only [CollatzResearch.WordTrace]
  refine ⟨171044967419268041396569553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114029978279512027597713035 171044967419268041396569553)
  ·
    refine ⟨128283725564451031047427165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171044967419268041396569553 128283725564451031047427165)
    ·
      refine ⟨48106397086669136642785187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128283725564451031047427165 48106397086669136642785187)
      ·
        refine ⟨72159595630003704964177781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48106397086669136642785187 72159595630003704964177781)
        ·
          refine ⟨6764962090312847340391667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72159595630003704964177781 6764962090312847340391667)
          ·
            refine ⟨10147443135469271010587501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6764962090312847340391667 10147443135469271010587501)
            ·
              refine ⟨3805291175800976628970313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10147443135469271010587501 3805291175800976628970313)
              ·
                refine ⟨2853968381850732471727735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3805291175800976628970313 2853968381850732471727735)
                ·
                  refine ⟨4280952572776098707591603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2853968381850732471727735 4280952572776098707591603)
                  ·
                    refine ⟨6421428859164148061387405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4280952572776098707591603 6421428859164148061387405)
                    ·
                      refine ⟨2408035822186555523020277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6421428859164148061387405 2408035822186555523020277)
                      ·
                        rfl

theorem cell23_4689633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2, 1, 1, 3].length) (baseStart_4689633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689633 prefixEnd_4689633 := by exact prefixLift 4689633
  have htrace : WordTrace (prefixWord ++ tailWord_4689633) baseStart_4689633 baseEnd_4689633 := by
    simpa [prefixWord, tailWord_4689633, baseEnd_4689633] using wordTrace_append hprefix tailTrace_4689633
  have hstable : (prefixWord ++ tailWord_4689633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689633).length < 2 ^ (prefixWord ++ tailWord_4689633).sum := by decide
  have hdescent : baseEnd_4689633 < baseStart_4689633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689645 : List Nat := [1, 5, 1, 2, 1, 2, 1, 10]
def baseStart_4689645 : Nat := 118140960795 + 4689645 * 2 ^ 59
def prefixEnd_4689645 : Nat := 4983230072969 + 3 ^ 40 * 4689645 * 2
def baseEnd_4689645 : Nat := 89186740146459610224823

theorem tailTrace_4689645 : CollatzResearch.WordTrace tailWord_4689645 prefixEnd_4689645 89186740146459610224823 := by
  unfold tailWord_4689645
  simp only [CollatzResearch.WordTrace]
  refine ⟨171045405095224567446006389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114030270063483044964004259 171045405095224567446006389)
  ·
    refine ⟨16035506727677303198063099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 171045405095224567446006389 16035506727677303198063099)
    ·
      refine ⟨24053260091515954797094649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16035506727677303198063099 24053260091515954797094649)
      ·
        refine ⟨18039945068636966097820987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24053260091515954797094649 18039945068636966097820987)
        ·
          refine ⟨27059917602955449146731481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18039945068636966097820987 27059917602955449146731481)
          ·
            refine ⟨20294938202216586860048611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27059917602955449146731481 20294938202216586860048611)
            ·
              refine ⟨30442407303324880290072917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20294938202216586860048611 30442407303324880290072917)
              ·
                refine ⟨89186740146459610224823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30442407303324880290072917 89186740146459610224823)
                ·
                  rfl

theorem cell23_4689645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 10].length) (baseStart_4689645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689645 prefixEnd_4689645 := by exact prefixLift 4689645
  have htrace : WordTrace (prefixWord ++ tailWord_4689645) baseStart_4689645 baseEnd_4689645 := by
    simpa [prefixWord, tailWord_4689645, baseEnd_4689645] using wordTrace_append hprefix tailTrace_4689645
  have hstable : (prefixWord ++ tailWord_4689645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689645).length < 2 ^ (prefixWord ++ tailWord_4689645).sum := by decide
  have hdescent : baseEnd_4689645 < baseStart_4689645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689649 : List Nat := [1, 2, 2, 2, 2, 3, 4, 1, 2, 4]
def baseStart_4689649 : Nat := 118140960795 + 4689649 * 2 ^ 59
def prefixEnd_4689649 : Nat := 4983230072969 + 3 ^ 40 * 4689649 * 2
def baseEnd_4689649 : Nat := 802681345959009153473401

theorem tailTrace_4689649 : CollatzResearch.WordTrace tailWord_4689649 prefixEnd_4689649 802681345959009153473401 := by
  unfold tailWord_4689649
  simp only [CollatzResearch.WordTrace]
  refine ⟨171045550987210076129152001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114030367324806717419434667 171045550987210076129152001)
  ·
    refine ⟨128284163240407557096864001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171045550987210076129152001 128284163240407557096864001)
    ·
      refine ⟨96213122430305667822648001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128284163240407557096864001 96213122430305667822648001)
      ·
        refine ⟨72159841822729250866986001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96213122430305667822648001 72159841822729250866986001)
        ·
          refine ⟨54119881367046938150239501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72159841822729250866986001 54119881367046938150239501)
          ·
            refine ⟨20294955512642601806339813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54119881367046938150239501 20294955512642601806339813)
            ·
              refine ⟨3805304158620487838688715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20294955512642601806339813 3805304158620487838688715)
              ·
                refine ⟨5707956237930731758033073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3805304158620487838688715 5707956237930731758033073)
                ·
                  refine ⟨4280967178448048818524805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5707956237930731758033073 4280967178448048818524805)
                  ·
                    refine ⟨802681345959009153473401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4280967178448048818524805 802681345959009153473401)
                    ·
                      rfl

theorem cell23_4689649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 2, 4].length) (baseStart_4689649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689649 prefixEnd_4689649 := by exact prefixLift 4689649
  have htrace : WordTrace (prefixWord ++ tailWord_4689649) baseStart_4689649 baseEnd_4689649 := by
    simpa [prefixWord, tailWord_4689649, baseEnd_4689649] using wordTrace_append hprefix tailTrace_4689649
  have hstable : (prefixWord ++ tailWord_4689649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689649).length < 2 ^ (prefixWord ++ tailWord_4689649).sum := by decide
  have hdescent : baseEnd_4689649 < baseStart_4689649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689672 : List Nat := [2, 1, 3, 2, 2, 1, 3, 2, 1, 3, 3]
def baseStart_4689672 : Nat := 118140960795 + 4689672 * 2 ^ 59
def prefixEnd_4689672 : Nat := 4983230072969 + 3 ^ 40 * 4689672 * 2
def baseEnd_4689672 : Nat := 2408055847932080870432597

theorem tailTrace_4689672 : CollatzResearch.WordTrace tailWord_4689672 prefixEnd_4689672 2408055847932080870432597 := by
  unfold tailWord_4689672
  simp only [CollatzResearch.WordTrace]
  refine ⟨85523194933063375528619635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114030926577417834038159513 85523194933063375528619635)
  ·
    refine ⟨128284792399595063292929453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85523194933063375528619635 128284792399595063292929453)
    ·
      refine ⟨48106797149848148734848545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128284792399595063292929453 48106797149848148734848545)
      ·
        refine ⟨36080097862386111551136409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48106797149848148734848545 36080097862386111551136409)
        ·
          refine ⟨27060073396789583663352307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36080097862386111551136409 27060073396789583663352307)
          ·
            refine ⟨40590110095184375495028461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27060073396789583663352307 40590110095184375495028461)
            ·
              refine ⟨15221291285694140810635673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40590110095184375495028461 15221291285694140810635673)
              ·
                refine ⟨11415968464270605607976755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15221291285694140810635673 11415968464270605607976755)
                ·
                  refine ⟨17123952696405908411965133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11415968464270605607976755 17123952696405908411965133)
                  ·
                    refine ⟨6421482261152215654486925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17123952696405908411965133 6421482261152215654486925)
                    ·
                      refine ⟨2408055847932080870432597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6421482261152215654486925 2408055847932080870432597)
                      ·
                        rfl

theorem cell23_4689672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_4689672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689672 prefixEnd_4689672 := by exact prefixLift 4689672
  have htrace : WordTrace (prefixWord ++ tailWord_4689672) baseStart_4689672 baseEnd_4689672 := by
    simpa [prefixWord, tailWord_4689672, baseEnd_4689672] using wordTrace_append hprefix tailTrace_4689672
  have hstable : (prefixWord ++ tailWord_4689672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689672).length < 2 ^ (prefixWord ++ tailWord_4689672).sum := by decide
  have hdescent : baseEnd_4689672 < baseStart_4689672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689684 : List Nat := [2, 4, 4, 1, 1, 2, 2, 2, 1, 1, 3]
def baseStart_4689684 : Nat := 118140960795 + 4689684 * 2 ^ 59
def prefixEnd_4689684 : Nat := 4983230072969 + 3 ^ 40 * 4689684 * 2
def baseEnd_4689684 : Nat := 2408062009699934823482543

theorem tailTrace_4689684 : CollatzResearch.WordTrace tailWord_4689684 prefixEnd_4689684 2408062009699934823482543 := by
  unfold tailWord_4689684
  simp only [CollatzResearch.WordTrace]
  refine ⟨85523413771041638553338053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114031218361388851404450737 85523413771041638553338053)
  ·
    refine ⟨16035640082070307228750885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85523413771041638553338053 16035640082070307228750885)
    ·
      refine ⟨3006682515388182605390791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16035640082070307228750885 3006682515388182605390791)
      ·
        refine ⟨4510023773082273908086187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3006682515388182605390791 4510023773082273908086187)
        ·
          refine ⟨6765035659623410862129281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4510023773082273908086187 6765035659623410862129281)
          ·
            refine ⟨5073776744717558146596961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6765035659623410862129281 5073776744717558146596961)
            ·
              refine ⟨3805332558538168609947721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5073776744717558146596961 3805332558538168609947721)
              ·
                refine ⟨2853999418903626457460791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3805332558538168609947721 2853999418903626457460791)
                ·
                  refine ⟨4280999128355439686191187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2853999418903626457460791 4280999128355439686191187)
                  ·
                    refine ⟨6421498692533159529286781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4280999128355439686191187 6421498692533159529286781)
                    ·
                      refine ⟨2408062009699934823482543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6421498692533159529286781 2408062009699934823482543)
                      ·
                        rfl

theorem cell23_4689684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_4689684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689684 prefixEnd_4689684 := by exact prefixLift 4689684
  have htrace : WordTrace (prefixWord ++ tailWord_4689684) baseStart_4689684 baseEnd_4689684 := by
    simpa [prefixWord, tailWord_4689684, baseEnd_4689684] using wordTrace_append hprefix tailTrace_4689684
  have hstable : (prefixWord ++ tailWord_4689684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689684).length < 2 ^ (prefixWord ++ tailWord_4689684).sum := by decide
  have hdescent : baseEnd_4689684 < baseStart_4689684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689690 : List Nat := [3, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2]
def baseStart_4689690 : Nat := 118140960795 + 4689690 * 2 ^ 59
def prefixEnd_4689690 : Nat := 4983230072969 + 3 ^ 40 * 4689690 * 2
def baseEnd_4689690 : Nat := 2408065090583861800007515

theorem tailTrace_4689690 : CollatzResearch.WordTrace tailWord_4689690 prefixEnd_4689690 2408065090583861800007515 := by
  unfold tailWord_4689690
  simp only [CollatzResearch.WordTrace]
  refine ⟨42761761595015385032848631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114031364253374360087596349 42761761595015385032848631)
  ·
    refine ⟨64142642392523077549272947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42761761595015385032848631 64142642392523077549272947)
    ·
      refine ⟨96213963588784616323909421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64142642392523077549272947 96213963588784616323909421)
      ·
        refine ⟨36080236345794231121466033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96213963588784616323909421 36080236345794231121466033)
        ·
          refine ⟨27060177259345673341099525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36080236345794231121466033 27060177259345673341099525)
          ·
            refine ⟨5073783236127313751456161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27060177259345673341099525 5073783236127313751456161)
            ·
              refine ⟨3805337427095485313592121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5073783236127313751456161 3805337427095485313592121)
              ·
                refine ⟨2854003070321613985194091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3805337427095485313592121 2854003070321613985194091)
                ·
                  refine ⟨4281004605482420977791137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2854003070321613985194091 4281004605482420977791137)
                  ·
                    refine ⟨3210753454111815733343353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4281004605482420977791137 3210753454111815733343353)
                    ·
                      refine ⟨2408065090583861800007515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3210753454111815733343353 2408065090583861800007515)
                      ·
                        rfl

theorem cell23_4689690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_4689690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689690 prefixEnd_4689690 := by exact prefixLift 4689690
  have htrace : WordTrace (prefixWord ++ tailWord_4689690) baseStart_4689690 baseEnd_4689690 := by
    simpa [prefixWord, tailWord_4689690, baseEnd_4689690] using wordTrace_append hprefix tailTrace_4689690
  have hstable : (prefixWord ++ tailWord_4689690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689690).length < 2 ^ (prefixWord ++ tailWord_4689690).sum := by decide
  have hdescent : baseEnd_4689690 < baseStart_4689690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689695 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 4]
def baseStart_4689695 : Nat := 118140960795 + 4689695 * 2 ^ 59
def prefixEnd_4689695 : Nat := 4983230072969 + 3 ^ 40 * 4689695 * 2
def baseEnd_4689695 : Nat := 2408067657987134280444991

theorem tailTrace_4689695 : CollatzResearch.WordTrace tailWord_4689695 prefixEnd_4689695 2408067657987134280444991 := by
  unfold tailWord_4689695
  simp only [CollatzResearch.WordTrace]
  refine ⟨171047228745043425985326539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114031485830028950656884359 171047228745043425985326539)
  ·
    refine ⟨256570843117565138977989809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171047228745043425985326539 256570843117565138977989809)
    ·
      refine ⟨192428132338173854233492357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256570843117565138977989809 192428132338173854233492357)
      ·
        refine ⟨36080274813407597668779817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 192428132338173854233492357 36080274813407597668779817)
        ·
          refine ⟨27060206110055698251584863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36080274813407597668779817 27060206110055698251584863)
          ·
            refine ⟨40590309165083547377377295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27060206110055698251584863 40590309165083547377377295)
            ·
              refine ⟨60885463747625321066065943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40590309165083547377377295 60885463747625321066065943)
              ·
                refine ⟨91328195621437981599098915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60885463747625321066065943 91328195621437981599098915)
                ·
                  refine ⟨136992293432156972398648373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91328195621437981599098915 136992293432156972398648373)
                  ·
                    refine ⟨12843027509264716162373285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 136992293432156972398648373 12843027509264716162373285)
                    ·
                      refine ⟨2408067657987134280444991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12843027509264716162373285 2408067657987134280444991)
                      ·
                        rfl

theorem cell23_4689695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_4689695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689695 prefixEnd_4689695 := by exact prefixLift 4689695
  have htrace : WordTrace (prefixWord ++ tailWord_4689695) baseStart_4689695 baseEnd_4689695 := by
    simpa [prefixWord, tailWord_4689695, baseEnd_4689695] using wordTrace_append hprefix tailTrace_4689695
  have hstable : (prefixWord ++ tailWord_4689695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689695).length < 2 ^ (prefixWord ++ tailWord_4689695).sum := by decide
  have hdescent : baseEnd_4689695 < baseStart_4689695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689716 : List Nat := [2, 5, 1, 1, 2, 1, 2, 1, 3, 3, 2]
def baseStart_4689716 : Nat := 118140960795 + 4689716 * 2 ^ 59
def prefixEnd_4689716 : Nat := 4983230072969 + 3 ^ 40 * 4689716 * 2
def baseEnd_4689716 : Nat := 2408078441080878698282395

theorem tailTrace_4689716 : CollatzResearch.WordTrace tailWord_4689716 prefixEnd_4689716 2408078441080878698282395 := by
  unfold tailWord_4689716
  simp only [CollatzResearch.WordTrace]
  refine ⟨85523997338983673285920501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114031996451978231047894001 85523997338983673285920501)
  ·
    refine ⟨8017874750529719370555047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85523997338983673285920501 8017874750529719370555047)
    ·
      refine ⟨12026812125794579055832571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8017874750529719370555047 12026812125794579055832571)
      ·
        refine ⟨18040218188691868583748857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12026812125794579055832571 18040218188691868583748857)
        ·
          refine ⟨13530163641518901437811643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18040218188691868583748857 13530163641518901437811643)
          ·
            refine ⟨20295245462278352156717465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13530163641518901437811643 20295245462278352156717465)
            ·
              refine ⟨15221434096708764117538099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20295245462278352156717465 15221434096708764117538099)
              ·
                refine ⟨22832151145063146176307149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15221434096708764117538099 22832151145063146176307149)
                ·
                  refine ⟨8562056679398679816115181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22832151145063146176307149 8562056679398679816115181)
                  ·
                    refine ⟨3210771254774504931043193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8562056679398679816115181 3210771254774504931043193)
                    ·
                      refine ⟨2408078441080878698282395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3210771254774504931043193 2408078441080878698282395)
                      ·
                        rfl

theorem cell23_4689716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_4689716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689716 prefixEnd_4689716 := by exact prefixLift 4689716
  have htrace : WordTrace (prefixWord ++ tailWord_4689716) baseStart_4689716 baseEnd_4689716 := by
    simpa [prefixWord, tailWord_4689716, baseEnd_4689716] using wordTrace_append hprefix tailTrace_4689716
  have hstable : (prefixWord ++ tailWord_4689716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689716).length < 2 ^ (prefixWord ++ tailWord_4689716).sum := by decide
  have hdescent : baseEnd_4689716 < baseStart_4689716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689746 : List Nat := [3, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2]
def baseStart_4689746 : Nat := 118140960795 + 4689746 * 2 ^ 59
def prefixEnd_4689746 : Nat := 4983230072969 + 3 ^ 40 * 4689746 * 2
def baseEnd_4689746 : Nat := 2408093845500513580907257

theorem tailTrace_4689746 : CollatzResearch.WordTrace tailWord_4689746 prefixEnd_4689746 2408093845500513580907257 := by
  unfold tailWord_4689746
  simp only [CollatzResearch.WordTrace]
  refine ⟨42762272216964665423858273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114032725911905774463622061 42762272216964665423858273)
  ·
    refine ⟨32071704162723499067893705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42762272216964665423858273 32071704162723499067893705)
    ·
      refine ⟨24053778122042624300920279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32071704162723499067893705 24053778122042624300920279)
      ·
        refine ⟨36080667183063936451380419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24053778122042624300920279 36080667183063936451380419)
        ·
          refine ⟨54121000774595904677070629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36080667183063936451380419 54121000774595904677070629)
          ·
            refine ⟨10147687645236732126950743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54121000774595904677070629 10147687645236732126950743)
            ·
              refine ⟨15221531467855098190426115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10147687645236732126950743 15221531467855098190426115)
              ·
                refine ⟨22832297201782647285639173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15221531467855098190426115 22832297201782647285639173)
                ·
                  refine ⟨4281055725334246366057345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22832297201782647285639173 4281055725334246366057345)
                  ·
                    refine ⟨3210791794000684774543009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4281055725334246366057345 3210791794000684774543009)
                    ·
                      refine ⟨2408093845500513580907257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3210791794000684774543009 2408093845500513580907257)
                      ·
                        rfl

theorem cell23_4689746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_4689746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689746 prefixEnd_4689746 := by exact prefixLift 4689746
  have htrace : WordTrace (prefixWord ++ tailWord_4689746) baseStart_4689746 baseEnd_4689746 := by
    simpa [prefixWord, tailWord_4689746, baseEnd_4689746] using wordTrace_append hprefix tailTrace_4689746
  have hstable : (prefixWord ++ tailWord_4689746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689746).length < 2 ^ (prefixWord ++ tailWord_4689746).sum := by decide
  have hdescent : baseEnd_4689746 < baseStart_4689746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689763 : List Nat := [1, 1, 1, 5, 5, 1, 1, 1, 1, 4, 2]
def baseStart_4689763 : Nat := 118140960795 + 4689763 * 2 ^ 59
def prefixEnd_4689763 : Nat := 4983230072969 + 3 ^ 40 * 4689763 * 2
def baseEnd_4689763 : Nat := 2408102574671640014394679

theorem tailTrace_4689763 : CollatzResearch.WordTrace tailWord_4689763 prefixEnd_4689763 2408102574671640014394679 := by
  unfold tailWord_4689763
  simp only [CollatzResearch.WordTrace]
  refine ⟨171049708908797073598801943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114033139272531382399201295 171049708908797073598801943)
  ·
    refine ⟨256574563363195610398202915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171049708908797073598801943 256574563363195610398202915)
    ·
      refine ⟨384861845044793415597304373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256574563363195610398202915 384861845044793415597304373)
      ·
        refine ⟨36080797972949382712247285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 384861845044793415597304373 36080797972949382712247285)
        ·
          refine ⟨3382574809964004629273183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36080797972949382712247285 3382574809964004629273183)
          ·
            refine ⟨5073862214946006943909775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3382574809964004629273183 5073862214946006943909775)
            ·
              refine ⟨7610793322419010415864663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5073862214946006943909775 7610793322419010415864663)
              ·
                refine ⟨11416189983628515623796995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7610793322419010415864663 11416189983628515623796995)
                ·
                  refine ⟨17124284975442773435695493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11416189983628515623796995 17124284975442773435695493)
                  ·
                    refine ⟨3210803432895520019192905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17124284975442773435695493 3210803432895520019192905)
                    ·
                      refine ⟨2408102574671640014394679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3210803432895520019192905 2408102574671640014394679)
                      ·
                        rfl

theorem cell23_4689763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_4689763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689763 prefixEnd_4689763 := by exact prefixLift 4689763
  have htrace : WordTrace (prefixWord ++ tailWord_4689763) baseStart_4689763 baseEnd_4689763 := by
    simpa [prefixWord, tailWord_4689763, baseEnd_4689763] using wordTrace_append hprefix tailTrace_4689763
  have hstable : (prefixWord ++ tailWord_4689763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689763).length < 2 ^ (prefixWord ++ tailWord_4689763).sum := by decide
  have hdescent : baseEnd_4689763 < baseStart_4689763 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689775 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 5]
def baseStart_4689775 : Nat := 118140960795 + 4689775 * 2 ^ 59
def prefixEnd_4689775 : Nat := 4983230072969 + 3 ^ 40 * 4689775 * 2
def baseEnd_4689775 : Nat := 2408108736439493967444623

theorem tailTrace_4689775 : CollatzResearch.WordTrace tailWord_4689775 prefixEnd_4689775 2408108736439493967444623 := by
  unfold tailWord_4689775
  simp only [CollatzResearch.WordTrace]
  refine ⟨171050146584753599648238779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114033431056502399765492519 171050146584753599648238779)
  ·
    refine ⟨256575219877130399472358169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171050146584753599648238779 256575219877130399472358169)
    ·
      refine ⟨192431414907847799604268627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256575219877130399472358169 192431414907847799604268627)
      ·
        refine ⟨288647122361771699406402941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192431414907847799604268627 288647122361771699406402941)
        ·
          refine ⟨108242670885664387277401103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 288647122361771699406402941 108242670885664387277401103)
          ·
            refine ⟨162364006328496580916101655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108242670885664387277401103 162364006328496580916101655)
            ·
              refine ⟨243546009492744871374152483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162364006328496580916101655 243546009492744871374152483)
              ·
                refine ⟨365319014239117307061228725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243546009492744871374152483 365319014239117307061228725)
                ·
                  refine ⟨34248657584917247536990193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 365319014239117307061228725 34248657584917247536990193)
                  ·
                    refine ⟨25686493188687935652742645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34248657584917247536990193 25686493188687935652742645)
                    ·
                      refine ⟨2408108736439493967444623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25686493188687935652742645 2408108736439493967444623)
                      ·
                        rfl

theorem cell23_4689775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 5].length) (baseStart_4689775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689775 prefixEnd_4689775 := by exact prefixLift 4689775
  have htrace : WordTrace (prefixWord ++ tailWord_4689775) baseStart_4689775 baseEnd_4689775 := by
    simpa [prefixWord, tailWord_4689775, baseEnd_4689775] using wordTrace_append hprefix tailTrace_4689775
  have hstable : (prefixWord ++ tailWord_4689775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689775).length < 2 ^ (prefixWord ++ tailWord_4689775).sum := by decide
  have hdescent : baseEnd_4689775 < baseStart_4689775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689799 : List Nat := [1, 1, 4, 2, 4, 1, 1, 2, 2, 5]
def baseStart_4689799 : Nat := 118140960795 + 4689799 * 2 ^ 59
def prefixEnd_4689799 : Nat := 4983230072969 + 3 ^ 40 * 4689799 * 2
def baseEnd_4689799 : Nat := 802707019991733957848171

theorem tailTrace_4689799 : CollatzResearch.WordTrace tailWord_4689799 prefixEnd_4689799 802707019991733957848171 := by
  unfold tailWord_4689799
  simp only [CollatzResearch.WordTrace]
  refine ⟨171051021936666651747112451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114034014624444434498074967 171051021936666651747112451)
  ·
    refine ⟨256576532904999977620668677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171051021936666651747112451 256576532904999977620668677)
    ·
      refine ⟨48108099919687495803875377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 256576532904999977620668677 48108099919687495803875377)
      ·
        refine ⟨36081074939765621852906533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48108099919687495803875377 36081074939765621852906533)
        ·
          refine ⟨6765201551206054097419975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36081074939765621852906533 6765201551206054097419975)
          ·
            refine ⟨10147802326809081146129963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6765201551206054097419975 10147802326809081146129963)
            ·
              refine ⟨15221703490213621719194945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10147802326809081146129963 15221703490213621719194945)
              ·
                refine ⟨11416277617660216289396209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15221703490213621719194945 11416277617660216289396209)
                ·
                  refine ⟨8562208213245162217047157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11416277617660216289396209 8562208213245162217047157)
                  ·
                    refine ⟨802707019991733957848171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8562208213245162217047157 802707019991733957848171)
                    ·
                      rfl

theorem cell23_4689799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_4689799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689799 prefixEnd_4689799 := by exact prefixLift 4689799
  have htrace : WordTrace (prefixWord ++ tailWord_4689799) baseStart_4689799 baseEnd_4689799 := by
    simpa [prefixWord, tailWord_4689799, baseEnd_4689799] using wordTrace_append hprefix tailTrace_4689799
  have hstable : (prefixWord ++ tailWord_4689799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689799).length < 2 ^ (prefixWord ++ tailWord_4689799).sum := by decide
  have hdescent : baseEnd_4689799 < baseStart_4689799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689835 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 9]
def baseStart_4689835 : Nat := 118140960795 + 4689835 * 2 ^ 59
def prefixEnd_4689835 : Nat := 4983230072969 + 3 ^ 40 * 4689835 * 2
def baseEnd_4689835 : Nat := 2408139545278763732694347

theorem tailTrace_4689835 : CollatzResearch.WordTrace tailWord_4689835 prefixEnd_4689835 2408139545278763732694347 := by
  unfold tailWord_4689835
  simp only [CollatzResearch.WordTrace]
  refine ⟨171052334964536229895422959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114034889976357486596948639 171052334964536229895422959)
  ·
    refine ⟨256578502446804344843134439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171052334964536229895422959 256578502446804344843134439)
    ·
      refine ⟨384867753670206517264701659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256578502446804344843134439 384867753670206517264701659)
      ·
        refine ⟨577301630505309775897052489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384867753670206517264701659 577301630505309775897052489)
        ·
          refine ⟨432976222878982331922789367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 577301630505309775897052489 432976222878982331922789367)
          ·
            refine ⟨649464334318473497884184051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432976222878982331922789367 649464334318473497884184051)
            ·
              refine ⟨974196501477710246826276077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 649464334318473497884184051 974196501477710246826276077)
              ·
                refine ⟨365323688054141342559853529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 974196501477710246826276077 365323688054141342559853529)
                ·
                  refine ⟨273992766040606006919890147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 365323688054141342559853529 273992766040606006919890147)
                  ·
                    refine ⟨410989149060909010379835221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 273992766040606006919890147 410989149060909010379835221)
                    ·
                      refine ⟨2408139545278763732694347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 410989149060909010379835221 2408139545278763732694347)
                      ·
                        rfl

theorem cell23_4689835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 9].length) (baseStart_4689835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689835 prefixEnd_4689835 := by exact prefixLift 4689835
  have htrace : WordTrace (prefixWord ++ tailWord_4689835) baseStart_4689835 baseEnd_4689835 := by
    simpa [prefixWord, tailWord_4689835, baseEnd_4689835] using wordTrace_append hprefix tailTrace_4689835
  have hstable : (prefixWord ++ tailWord_4689835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689835).length < 2 ^ (prefixWord ++ tailWord_4689835).sum := by decide
  have hdescent : baseEnd_4689835 < baseStart_4689835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689839 : List Nat := [1, 1, 2, 1, 2, 2, 6, 1, 2, 2, 3]
def baseStart_4689839 : Nat := 118140960795 + 4689839 * 2 ^ 59
def prefixEnd_4689839 : Nat := 4983230072969 + 3 ^ 40 * 4689839 * 2
def baseEnd_4689839 : Nat := 2408141599201381717044329

theorem tailTrace_4689839 : CollatzResearch.WordTrace tailWord_4689839 prefixEnd_4689839 2408141599201381717044329 := by
  unfold tailWord_4689839
  simp only [CollatzResearch.WordTrace]
  refine ⟨171052480856521738578568571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114034987237681159052379047 171052480856521738578568571)
  ·
    refine ⟨256578721284782607867852857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171052480856521738578568571 256578721284782607867852857)
    ·
      refine ⟨192434040963586955900889643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256578721284782607867852857 192434040963586955900889643)
      ·
        refine ⟨288651061445380433851334465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192434040963586955900889643 288651061445380433851334465)
        ·
          refine ⟨216488296084035325388500849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288651061445380433851334465 216488296084035325388500849)
          ·
            refine ⟨162366222063026494041375637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216488296084035325388500849 162366222063026494041375637)
            ·
              refine ⟨7610916659204366908189483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 162366222063026494041375637 7610916659204366908189483)
              ·
                refine ⟨11416374988806550362284225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7610916659204366908189483 11416374988806550362284225)
                ·
                  refine ⟨8562281241604912771713169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11416374988806550362284225 8562281241604912771713169)
                  ·
                    refine ⟨6421710931203684578784877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8562281241604912771713169 6421710931203684578784877)
                    ·
                      refine ⟨2408141599201381717044329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6421710931203684578784877 2408141599201381717044329)
                      ·
                        rfl

theorem cell23_4689839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2, 3].length) (baseStart_4689839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689839 prefixEnd_4689839 := by exact prefixLift 4689839
  have htrace : WordTrace (prefixWord ++ tailWord_4689839) baseStart_4689839 baseEnd_4689839 := by
    simpa [prefixWord, tailWord_4689839, baseEnd_4689839] using wordTrace_append hprefix tailTrace_4689839
  have hstable : (prefixWord ++ tailWord_4689839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689839).length < 2 ^ (prefixWord ++ tailWord_4689839).sum := by decide
  have hdescent : baseEnd_4689839 < baseStart_4689839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689872 : List Nat := [2, 1, 1, 1, 1, 2, 5, 2, 3, 5]
def baseStart_4689872 : Nat := 118140960795 + 4689872 * 2 ^ 59
def prefixEnd_4689872 : Nat := 4983230072969 + 3 ^ 40 * 4689872 * 2
def baseEnd_4689872 : Nat := 802719514687660029310559

theorem tailTrace_4689872 : CollatzResearch.WordTrace tailWord_4689872 prefixEnd_4689872 802719514687660029310559 := by
  unfold tailWord_4689872
  simp only [CollatzResearch.WordTrace]
  refine ⟨85526842232701092607259935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114035789643601456809679913 85526842232701092607259935)
  ·
    refine ⟨128290263349051638910889903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85526842232701092607259935 128290263349051638910889903)
    ·
      refine ⟨192435395023577458366334855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128290263349051638910889903 192435395023577458366334855)
      ·
        refine ⟨288653092535366187549502283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192435395023577458366334855 288653092535366187549502283)
        ·
          refine ⟨432979638803049281324253425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288653092535366187549502283 432979638803049281324253425)
          ·
            refine ⟨324734729102286960993190069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 432979638803049281324253425 324734729102286960993190069)
            ·
              refine ⟨30443880853339402593111569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 324734729102286960993190069 30443880853339402593111569)
              ·
                refine ⟨22832910640004551944833677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30443880853339402593111569 22832910640004551944833677)
                ·
                  refine ⟨8562341490001706979312629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22832910640004551944833677 8562341490001706979312629)
                  ·
                    refine ⟨802719514687660029310559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8562341490001706979312629 802719514687660029310559)
                    ·
                      rfl

theorem cell23_4689872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 3, 5].length) (baseStart_4689872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689872 prefixEnd_4689872 := by exact prefixLift 4689872
  have htrace : WordTrace (prefixWord ++ tailWord_4689872) baseStart_4689872 baseEnd_4689872 := by
    simpa [prefixWord, tailWord_4689872, baseEnd_4689872] using wordTrace_append hprefix tailTrace_4689872
  have hstable : (prefixWord ++ tailWord_4689872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689872).length < 2 ^ (prefixWord ++ tailWord_4689872).sum := by decide
  have hdescent : baseEnd_4689872 < baseStart_4689872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689879 : List Nat := [1, 1, 3, 2, 1, 1, 4, 2, 1, 5, 2]
def baseStart_4689879 : Nat := 118140960795 + 4689879 * 2 ^ 59
def prefixEnd_4689879 : Nat := 4983230072969 + 3 ^ 40 * 4689879 * 2
def baseEnd_4689879 : Nat := 2408162138427561560544145

theorem tailTrace_4689879 : CollatzResearch.WordTrace tailWord_4689879 prefixEnd_4689879 2408162138427561560544145 := by
  unfold tailWord_4689879
  simp only [CollatzResearch.WordTrace]
  refine ⟨171053939776376825410024691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114035959850917883606683127 171053939776376825410024691)
  ·
    refine ⟨256580909664565238115037037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171053939776376825410024691 256580909664565238115037037)
    ·
      refine ⟨96217841124211964293138889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256580909664565238115037037 96217841124211964293138889)
      ·
        refine ⟨72163380843158973219854167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96217841124211964293138889 72163380843158973219854167)
        ·
          refine ⟨108245071264738459829781251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72163380843158973219854167 108245071264738459829781251)
          ·
            refine ⟨162367606897107689744671877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108245071264738459829781251 162367606897107689744671877)
            ·
              refine ⟨30443926293207691827125977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 162367606897107689744671877 30443926293207691827125977)
              ·
                refine ⟨22832944719905768870344483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30443926293207691827125977 22832944719905768870344483)
                ·
                  refine ⟨34249417079858653305516725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22832944719905768870344483 34249417079858653305516725)
                  ·
                    refine ⟨3210882851236748747392193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34249417079858653305516725 3210882851236748747392193)
                    ·
                      refine ⟨2408162138427561560544145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3210882851236748747392193 2408162138427561560544145)
                      ·
                        rfl

theorem cell23_4689879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 5, 2].length) (baseStart_4689879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689879 prefixEnd_4689879 := by exact prefixLift 4689879
  have htrace : WordTrace (prefixWord ++ tailWord_4689879) baseStart_4689879 baseEnd_4689879 := by
    simpa [prefixWord, tailWord_4689879, baseEnd_4689879] using wordTrace_append hprefix tailTrace_4689879
  have hstable : (prefixWord ++ tailWord_4689879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689879).length < 2 ^ (prefixWord ++ tailWord_4689879).sum := by decide
  have hdescent : baseEnd_4689879 < baseStart_4689879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689890 : List Nat := [3, 3, 3, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_4689890 : Nat := 118140960795 + 4689890 * 2 ^ 59
def prefixEnd_4689890 : Nat := 4983230072969 + 3 ^ 40 * 4689890 * 2
def baseEnd_4689890 : Nat := 2408167786714761017506595

theorem tailTrace_4689890 : CollatzResearch.WordTrace tailWord_4689890 prefixEnd_4689890 2408167786714761017506595 := by
  unfold tailWord_4689890
  simp only [CollatzResearch.WordTrace]
  refine ⟨42763585244834243572168781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114036227319557982859116749 42763585244834243572168781)
  ·
    refine ⟨16036344466812841339563293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42763585244834243572168781 16036344466812841339563293)
    ·
      refine ⟨6013629175054815502336235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16036344466812841339563293 6013629175054815502336235)
      ·
        refine ⟨9020443762582223253504353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6013629175054815502336235 9020443762582223253504353)
        ·
          refine ⟨6765332821936667440128265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9020443762582223253504353 6765332821936667440128265)
          ·
            refine ⟨5073999616452500580096199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6765332821936667440128265 5073999616452500580096199)
            ·
              refine ⟨7610999424678750870144299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5073999616452500580096199 7610999424678750870144299)
              ·
                refine ⟨11416499137018126305216449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7610999424678750870144299 11416499137018126305216449)
                ·
                  refine ⟨8562374352763594728912337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11416499137018126305216449 8562374352763594728912337)
                  ·
                    refine ⟨6421780764572696046684253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8562374352763594728912337 6421780764572696046684253)
                    ·
                      refine ⟨2408167786714761017506595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6421780764572696046684253 2408167786714761017506595)
                      ·
                        rfl

theorem cell23_4689890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_4689890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689890 prefixEnd_4689890 := by exact prefixLift 4689890
  have htrace : WordTrace (prefixWord ++ tailWord_4689890) baseStart_4689890 baseEnd_4689890 := by
    simpa [prefixWord, tailWord_4689890, baseEnd_4689890] using wordTrace_append hprefix tailTrace_4689890
  have hstable : (prefixWord ++ tailWord_4689890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689890).length < 2 ^ (prefixWord ++ tailWord_4689890).sum := by decide
  have hdescent : baseEnd_4689890 < baseStart_4689890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689903 : List Nat := [1, 1, 2, 1, 4, 2, 4, 3, 1, 1, 3]
def baseStart_4689903 : Nat := 118140960795 + 4689903 * 2 ^ 59
def prefixEnd_4689903 : Nat := 4983230072969 + 3 ^ 40 * 4689903 * 2
def baseEnd_4689903 : Nat := 2408174461963269466644035

theorem tailTrace_4689903 : CollatzResearch.WordTrace tailWord_4689903 prefixEnd_4689903 2408174461963269466644035 := by
  unfold tailWord_4689903
  simp only [CollatzResearch.WordTrace]
  refine ⟨171054815128289877508898363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114036543418859918339265575 171054815128289877508898363)
  ·
    refine ⟨256582222692434816263347545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171054815128289877508898363 256582222692434816263347545)
    ·
      refine ⟨192436667019326112197510659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256582222692434816263347545 192436667019326112197510659)
      ·
        refine ⟨288655000528989168296265989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192436667019326112197510659 288655000528989168296265989)
        ·
          refine ⟨54122812599185469055549873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 288655000528989168296265989 54122812599185469055549873)
          ·
            refine ⟨40592109449389101791662405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54122812599185469055549873 40592109449389101791662405)
            ·
              refine ⟨7611020521760456585936701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40592109449389101791662405 7611020521760456585936701)
              ·
                refine ⟨2854132695660171219726263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7611020521760456585936701 2854132695660171219726263)
                ·
                  refine ⟨4281199043490256829589395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2854132695660171219726263 4281199043490256829589395)
                  ·
                    refine ⟨6421798565235385244384093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4281199043490256829589395 6421798565235385244384093)
                    ·
                      refine ⟨2408174461963269466644035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6421798565235385244384093 2408174461963269466644035)
                      ·
                        rfl

theorem cell23_4689903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3, 1, 1, 3].length) (baseStart_4689903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689903 prefixEnd_4689903 := by exact prefixLift 4689903
  have htrace : WordTrace (prefixWord ++ tailWord_4689903) baseStart_4689903 baseEnd_4689903 := by
    simpa [prefixWord, tailWord_4689903, baseEnd_4689903] using wordTrace_append hprefix tailTrace_4689903
  have hstable : (prefixWord ++ tailWord_4689903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689903).length < 2 ^ (prefixWord ++ tailWord_4689903).sum := by decide
  have hdescent : baseEnd_4689903 < baseStart_4689903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689932 : List Nat := [2, 2, 1, 2, 3, 1, 2, 10]
def baseStart_4689932 : Nat := 118140960795 + 4689932 * 2 ^ 59
def prefixEnd_4689932 : Nat := 4983230072969 + 3 ^ 40 * 4689932 * 2
def baseEnd_4689932 : Nat := 89192198255638883451163

theorem tailTrace_4689932 : CollatzResearch.WordTrace tailWord_4689932 prefixEnd_4689932 89192198255638883451163 := by
  unfold tailWord_4689932
  simp only [CollatzResearch.WordTrace]
  refine ⟨85527936422592407730852025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114037248563456543641136033 85527936422592407730852025)
  ·
    refine ⟨64145952316944305798139019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85527936422592407730852025 64145952316944305798139019)
    ·
      refine ⟨96218928475416458697208529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64145952316944305798139019 96218928475416458697208529)
      ·
        refine ⟨72164196356562344022906397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96218928475416458697208529 72164196356562344022906397)
        ·
          refine ⟨27061573633710879008589899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72164196356562344022906397 27061573633710879008589899)
          ·
            refine ⟨40592360450566318512884849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27061573633710879008589899 40592360450566318512884849)
            ·
              refine ⟨30444270337924738884663637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40592360450566318512884849 30444270337924738884663637)
              ·
                refine ⟨89192198255638883451163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30444270337924738884663637 89192198255638883451163)
                ·
                  rfl

theorem cell23_4689932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 10].length) (baseStart_4689932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689932 prefixEnd_4689932 := by exact prefixLift 4689932
  have htrace : WordTrace (prefixWord ++ tailWord_4689932) baseStart_4689932 baseEnd_4689932 := by
    simpa [prefixWord, tailWord_4689932, baseEnd_4689932] using wordTrace_append hprefix tailTrace_4689932
  have hstable : (prefixWord ++ tailWord_4689932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689932).length < 2 ^ (prefixWord ++ tailWord_4689932).sum := by decide
  have hdescent : baseEnd_4689932 < baseStart_4689932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689939 : List Nat := [1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 4]
def baseStart_4689939 : Nat := 118140960795 + 4689939 * 2 ^ 59
def prefixEnd_4689939 : Nat := 4983230072969 + 3 ^ 40 * 4689939 * 2
def baseEnd_4689939 : Nat := 2408192947266831325793869

theorem tailTrace_4689939 : CollatzResearch.WordTrace tailWord_4689939 prefixEnd_4689939 2408192947266831325793869 := by
  unfold tailWord_4689939
  simp only [CollatzResearch.WordTrace]
  refine ⟨171056128156159455657208871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114037418770772970438139247 171056128156159455657208871)
  ·
    refine ⟨256584192234239183485813307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171056128156159455657208871 256584192234239183485813307)
    ·
      refine ⟨384876288351358775228719961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256584192234239183485813307 384876288351358775228719961)
      ·
        refine ⟨288657216263519081421539971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 384876288351358775228719961 288657216263519081421539971)
        ·
          refine ⟨432985824395278622132309957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288657216263519081421539971 432985824395278622132309957)
          ·
            refine ⟨81184842074114741649808117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 432985824395278622132309957 81184842074114741649808117)
            ·
              refine ⟨7611078944448257029669511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81184842074114741649808117 7611078944448257029669511)
              ·
                refine ⟨11416618416672385544504267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7611078944448257029669511 11416618416672385544504267)
                ·
                  refine ⟨17124927625008578316756401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11416618416672385544504267 17124927625008578316756401)
                  ·
                    refine ⟨12843695718756433737567301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17124927625008578316756401 12843695718756433737567301)
                    ·
                      refine ⟨2408192947266831325793869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12843695718756433737567301 2408192947266831325793869)
                      ·
                        rfl

theorem cell23_4689939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 4].length) (baseStart_4689939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689939 prefixEnd_4689939 := by exact prefixLift 4689939
  have htrace : WordTrace (prefixWord ++ tailWord_4689939) baseStart_4689939 baseEnd_4689939 := by
    simpa [prefixWord, tailWord_4689939, baseEnd_4689939] using wordTrace_append hprefix tailTrace_4689939
  have hstable : (prefixWord ++ tailWord_4689939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689939).length < 2 ^ (prefixWord ++ tailWord_4689939).sum := by decide
  have hdescent : baseEnd_4689939 < baseStart_4689939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689940 : List Nat := [2, 4, 3, 2, 1, 1, 2, 2, 1, 5]
def baseStart_4689940 : Nat := 118140960795 + 4689940 * 2 ^ 59
def prefixEnd_4689940 : Nat := 4983230072969 + 3 ^ 40 * 4689940 * 2
def baseEnd_4689940 : Nat := 802731153582495273960455

theorem tailTrace_4689940 : CollatzResearch.WordTrace tailWord_4689940 prefixEnd_4689940 802731153582495273960455 := by
  unfold tailWord_4689940
  simp only [CollatzResearch.WordTrace]
  refine ⟨85528082314577916413997637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114037443086103888551996849 85528082314577916413997637)
  ·
    refine ⟨16036515433983359327624557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85528082314577916413997637 16036515433983359327624557)
    ·
      refine ⟨6013693287743759747859209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16036515433983359327624557 6013693287743759747859209)
      ·
        refine ⟨4510269965807819810894407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6013693287743759747859209 4510269965807819810894407)
        ·
          refine ⟨6765404948711729716341611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4510269965807819810894407 6765404948711729716341611)
          ·
            refine ⟨10148107423067594574512417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6765404948711729716341611 10148107423067594574512417)
            ·
              refine ⟨7611080567300695930884313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10148107423067594574512417 7611080567300695930884313)
              ·
                refine ⟨5708310425475521948163235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7611080567300695930884313 5708310425475521948163235)
                ·
                  refine ⟨8562465638213282922244853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5708310425475521948163235 8562465638213282922244853)
                  ·
                    refine ⟨802731153582495273960455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8562465638213282922244853 802731153582495273960455)
                    ·
                      rfl

theorem cell23_4689940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_4689940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689940 prefixEnd_4689940 := by exact prefixLift 4689940
  have htrace : WordTrace (prefixWord ++ tailWord_4689940) baseStart_4689940 baseEnd_4689940 := by
    simpa [prefixWord, tailWord_4689940, baseEnd_4689940] using wordTrace_append hprefix tailTrace_4689940
  have hstable : (prefixWord ++ tailWord_4689940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689940).length < 2 ^ (prefixWord ++ tailWord_4689940).sum := by decide
  have hdescent : baseEnd_4689940 < baseStart_4689940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689943 : List Nat := [1, 1, 3, 5, 2, 1, 2, 2, 1, 1, 4]
def baseStart_4689943 : Nat := 118140960795 + 4689943 * 2 ^ 59
def prefixEnd_4689943 : Nat := 4983230072969 + 3 ^ 40 * 4689943 * 2
def baseEnd_4689943 : Nat := 2408195001189449310143851

theorem tailTrace_4689943 : CollatzResearch.WordTrace tailWord_4689943 prefixEnd_4689943 2408195001189449310143851 := by
  unfold tailWord_4689943
  simp only [CollatzResearch.WordTrace]
  refine ⟨171056274048144964340354483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114037516032096642893569655 171056274048144964340354483)
  ·
    refine ⟨256584411072217446510531725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171056274048144964340354483 256584411072217446510531725)
    ·
      refine ⟨96219154152081542441449397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256584411072217446510531725 96219154152081542441449397)
      ·
        refine ⟨9020545701757644603885881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96219154152081542441449397 9020545701757644603885881)
        ·
          refine ⟨6765409276318233452914411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9020545701757644603885881 6765409276318233452914411)
          ·
            refine ⟨10148113914477350179371617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6765409276318233452914411 10148113914477350179371617)
            ·
              refine ⟨7611085435858012634528713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10148113914477350179371617 7611085435858012634528713)
              ·
                refine ⟨5708314076893509475896535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7611085435858012634528713 5708314076893509475896535)
                ·
                  refine ⟨8562471115340264213844803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5708314076893509475896535 8562471115340264213844803)
                  ·
                    refine ⟨12843706673010396320767205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8562471115340264213844803 12843706673010396320767205)
                    ·
                      refine ⟨2408195001189449310143851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12843706673010396320767205 2408195001189449310143851)
                      ·
                        rfl

theorem cell23_4689943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_4689943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689943 prefixEnd_4689943 := by exact prefixLift 4689943
  have htrace : WordTrace (prefixWord ++ tailWord_4689943) baseStart_4689943 baseEnd_4689943 := by
    simpa [prefixWord, tailWord_4689943, baseEnd_4689943] using wordTrace_append hprefix tailTrace_4689943
  have hstable : (prefixWord ++ tailWord_4689943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689943).length < 2 ^ (prefixWord ++ tailWord_4689943).sum := by decide
  have hdescent : baseEnd_4689943 < baseStart_4689943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689946 : List Nat := [3, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3]
def baseStart_4689946 : Nat := 118140960795 + 4689946 * 2 ^ 59
def prefixEnd_4689946 : Nat := 4983230072969 + 3 ^ 40 * 4689946 * 2
def baseEnd_4689946 : Nat := 2408196541631412798406337

theorem tailTrace_4689946 : CollatzResearch.WordTrace tailWord_4689946 prefixEnd_4689946 2408196541631412798406337 := by
  unfold tailWord_4689946
  simp only [CollatzResearch.WordTrace]
  refine ⟨42764095866783523963178423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114037588978089397235142461 42764095866783523963178423)
  ·
    refine ⟨64146143800175285944767635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42764095866783523963178423 64146143800175285944767635)
    ·
      refine ⟨96219215700262928917151453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64146143800175285944767635 96219215700262928917151453)
      ·
        refine ⟨36082205887598598343931795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96219215700262928917151453 36082205887598598343931795)
        ·
          refine ⟨54123308831397897515897693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36082205887598598343931795 54123308831397897515897693)
          ·
            refine ⟨20296240811774211568461635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54123308831397897515897693 20296240811774211568461635)
            ·
              refine ⟨30444361217661317352692453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20296240811774211568461635 30444361217661317352692453)
              ·
                refine ⟨5708317728311497003629835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30444361217661317352692453 5708317728311497003629835)
                ·
                  refine ⟨8562476592467245505444753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5708317728311497003629835 8562476592467245505444753)
                  ·
                    refine ⟨6421857444350434129083565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8562476592467245505444753 6421857444350434129083565)
                    ·
                      refine ⟨2408196541631412798406337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6421857444350434129083565 2408196541631412798406337)
                      ·
                        rfl

theorem cell23_4689946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_4689946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689946 prefixEnd_4689946 := by exact prefixLift 4689946
  have htrace : WordTrace (prefixWord ++ tailWord_4689946) baseStart_4689946 baseEnd_4689946 := by
    simpa [prefixWord, tailWord_4689946, baseEnd_4689946] using wordTrace_append hprefix tailTrace_4689946
  have hstable : (prefixWord ++ tailWord_4689946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689946).length < 2 ^ (prefixWord ++ tailWord_4689946).sum := by decide
  have hdescent : baseEnd_4689946 < baseStart_4689946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689949 : List Nat := [1, 4, 2, 2, 2, 2, 1, 9]
def baseStart_4689949 : Nat := 118140960795 + 4689949 * 2 ^ 59
def prefixEnd_4689949 : Nat := 4983230072969 + 3 ^ 40 * 4689949 * 2
def baseEnd_4689949 : Nat := 89192521558273195802549

theorem tailTrace_4689949 : CollatzResearch.WordTrace tailWord_4689949 prefixEnd_4689949 89192521558273195802549 := by
  unfold tailWord_4689949
  simp only [CollatzResearch.WordTrace]
  refine ⟨171056492886123227365072901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114037661924082151576715267 171056492886123227365072901)
  ·
    refine ⟨32073092416148105130951169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171056492886123227365072901 32073092416148105130951169)
    ·
      refine ⟨24054819312111078848213377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32073092416148105130951169 24054819312111078848213377)
      ·
        refine ⟨18041114484083309136160033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24054819312111078848213377 18041114484083309136160033)
        ·
          refine ⟨13530835863062481852120025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18041114484083309136160033 13530835863062481852120025)
          ·
            refine ⟨10148126897296861389090019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13530835863062481852120025 10148126897296861389090019)
            ·
              refine ⟨15222190345945292083635029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10148126897296861389090019 15222190345945292083635029)
              ·
                refine ⟨89192521558273195802549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15222190345945292083635029 89192521558273195802549)
                ·
                  rfl

theorem cell23_4689949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 9].length) (baseStart_4689949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689949 prefixEnd_4689949 := by exact prefixLift 4689949
  have htrace : WordTrace (prefixWord ++ tailWord_4689949) baseStart_4689949 baseEnd_4689949 := by
    simpa [prefixWord, tailWord_4689949, baseEnd_4689949] using wordTrace_append hprefix tailTrace_4689949
  have hstable : (prefixWord ++ tailWord_4689949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689949).length < 2 ^ (prefixWord ++ tailWord_4689949).sum := by decide
  have hdescent : baseEnd_4689949 < baseStart_4689949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4689977 : List Nat := [1, 2, 1, 5, 4, 1, 1, 1, 3, 2, 2]
def baseStart_4689977 : Nat := 118140960795 + 4689977 * 2 ^ 59
def prefixEnd_4689977 : Nat := 4983230072969 + 3 ^ 40 * 4689977 * 2
def baseEnd_4689977 : Nat := 2408212459531702177118695

theorem tailTrace_4689977 : CollatzResearch.WordTrace tailWord_4689977 prefixEnd_4689977 2408212459531702177118695 := by
  unfold tailWord_4689977
  simp only [CollatzResearch.WordTrace]
  refine ⟨171057514130021788147092185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114038342753347858764728123 171057514130021788147092185)
  ·
    refine ⟨128293135597516341110319139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171057514130021788147092185 128293135597516341110319139)
    ·
      refine ⟨192439703396274511665478709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128293135597516341110319139 192439703396274511665478709)
      ·
        refine ⟨18041222193400735468638629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 192439703396274511665478709 18041222193400735468638629)
        ·
          refine ⟨3382729161262637900369743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18041222193400735468638629 3382729161262637900369743)
          ·
            refine ⟨5074093741893956850554615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3382729161262637900369743 5074093741893956850554615)
            ·
              refine ⟨7611140612840935275831923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5074093741893956850554615 7611140612840935275831923)
              ·
                refine ⟨11416710919261402913747885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7611140612840935275831923 11416710919261402913747885)
                ·
                  refine ⟨4281266594723026092655457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11416710919261402913747885 4281266594723026092655457)
                  ·
                    refine ⟨3210949946042269569491593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4281266594723026092655457 3210949946042269569491593)
                    ·
                      refine ⟨2408212459531702177118695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3210949946042269569491593 2408212459531702177118695)
                      ·
                        rfl

theorem cell23_4689977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_4689977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4689977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4689977 prefixEnd_4689977 := by exact prefixLift 4689977
  have htrace : WordTrace (prefixWord ++ tailWord_4689977) baseStart_4689977 baseEnd_4689977 := by
    simpa [prefixWord, tailWord_4689977, baseEnd_4689977] using wordTrace_append hprefix tailTrace_4689977
  have hstable : (prefixWord ++ tailWord_4689977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4689977).length < 2 ^ (prefixWord ++ tailWord_4689977).sum := by decide
  have hdescent : baseEnd_4689977 < baseStart_4689977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4689977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690014 : List Nat := [4, 4, 1, 1, 2, 1, 3, 1, 1, 2, 3]
def baseStart_4690014 : Nat := 118140960795 + 4690014 * 2 ^ 59
def prefixEnd_4690014 : Nat := 4983230072969 + 3 ^ 40 * 4690014 * 2
def baseEnd_4690014 : Nat := 2408231458315918532356025

theorem tailTrace_4690014 : CollatzResearch.WordTrace tailWord_4690014 prefixEnd_4690014 2408231458315918532356025 := by
  unfold tailWord_4690014
  simp only [CollatzResearch.WordTrace]
  refine ⟨21382357953860967933273637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114039242420591828977459397 21382357953860967933273637)
  ·
    refine ⟨4009192116348931487488807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21382357953860967933273637 4009192116348931487488807)
    ·
      refine ⟨6013788174523397231233211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4009192116348931487488807 6013788174523397231233211)
      ·
        refine ⟨9020682261785095846849817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6013788174523397231233211 9020682261785095846849817)
        ·
          refine ⟨6765511696338821885137363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9020682261785095846849817 6765511696338821885137363)
          ·
            refine ⟨10148267544508232827706045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6765511696338821885137363 10148267544508232827706045)
            ·
              refine ⟨3805600329190587310389767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10148267544508232827706045 3805600329190587310389767)
              ·
                refine ⟨5708400493785880965584651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3805600329190587310389767 5708400493785880965584651)
                ·
                  refine ⟨8562600740678821448376977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5708400493785880965584651 8562600740678821448376977)
                  ·
                    refine ⟨6421950555509116086282733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8562600740678821448376977 6421950555509116086282733)
                    ·
                      refine ⟨2408231458315918532356025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6421950555509116086282733 2408231458315918532356025)
                      ·
                        rfl

theorem cell23_4690014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_4690014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690014 prefixEnd_4690014 := by exact prefixLift 4690014
  have htrace : WordTrace (prefixWord ++ tailWord_4690014) baseStart_4690014 baseEnd_4690014 := by
    simpa [prefixWord, tailWord_4690014, baseEnd_4690014] using wordTrace_append hprefix tailTrace_4690014
  have hstable : (prefixWord ++ tailWord_4690014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690014).length < 2 ^ (prefixWord ++ tailWord_4690014).sum := by decide
  have hdescent : baseEnd_4690014 < baseStart_4690014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690016 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 3, 4, 2]
def baseStart_4690016 : Nat := 118140960795 + 4690016 * 2 ^ 59
def prefixEnd_4690016 : Nat := 4983230072969 + 3 ^ 40 * 4690016 * 2
def baseEnd_4690016 : Nat := 2408232485277227524531015

theorem tailTrace_4690016 : CollatzResearch.WordTrace tailWord_4690016 prefixEnd_4690016 2408232485277227524531015 := by
  unfold tailWord_4690016
  simp only [CollatzResearch.WordTrace]
  refine ⟨85529468288440248903880951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114039291051253665205174601 85529468288440248903880951)
  ·
    refine ⟨128294202432660373355821427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85529468288440248903880951 128294202432660373355821427)
    ·
      refine ⟨192441303648990560033732141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128294202432660373355821427 192441303648990560033732141)
      ·
        refine ⟨72165488868371460012649553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192441303648990560033732141 72165488868371460012649553)
        ·
          refine ⟨54124116651278595009487165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72165488868371460012649553 54124116651278595009487165)
          ·
            refine ⟨20296543744229473128557687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54124116651278595009487165 20296543744229473128557687)
            ·
              refine ⟨30444815616344209692836531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20296543744229473128557687 30444815616344209692836531)
              ·
                refine ⟨45667223424516314539254797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30444815616344209692836531 45667223424516314539254797)
                ·
                  refine ⟨17125208784193617952220549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45667223424516314539254797 17125208784193617952220549)
                  ·
                    refine ⟨3210976647036303366041353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17125208784193617952220549 3210976647036303366041353)
                    ·
                      refine ⟨2408232485277227524531015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3210976647036303366041353 2408232485277227524531015)
                      ·
                        rfl

theorem cell23_4690016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 3, 4, 2].length) (baseStart_4690016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690016 prefixEnd_4690016 := by exact prefixLift 4690016
  have htrace : WordTrace (prefixWord ++ tailWord_4690016) baseStart_4690016 baseEnd_4690016 := by
    simpa [prefixWord, tailWord_4690016, baseEnd_4690016] using wordTrace_append hprefix tailTrace_4690016
  have hstable : (prefixWord ++ tailWord_4690016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690016).length < 2 ^ (prefixWord ++ tailWord_4690016).sum := by decide
  have hdescent : baseEnd_4690016 < baseStart_4690016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690019 : List Nat := [1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 5]
def baseStart_4690019 : Nat := 118140960795 + 4690019 * 2 ^ 59
def prefixEnd_4690019 : Nat := 4983230072969 + 3 ^ 40 * 4690019 * 2
def baseEnd_4690019 : Nat := 2408234025719191012793501

theorem tailTrace_4690019 : CollatzResearch.WordTrace tailWord_4690019 prefixEnd_4690019 2408234025719191012793501 := by
  unfold tailWord_4690019
  simp only [CollatzResearch.WordTrace]
  refine ⟨171059045995869629320121111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114039363997246419546747407 171059045995869629320121111)
  ·
    refine ⟨256588568993804443980181667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171059045995869629320121111 256588568993804443980181667)
    ·
      refine ⟨384882853490706665970272501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256588568993804443980181667 384882853490706665970272501)
      ·
        refine ⟨36082767514753749934713047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 384882853490706665970272501 36082767514753749934713047)
        ·
          refine ⟨54124151272130624902069571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36082767514753749934713047 54124151272130624902069571)
          ·
            refine ⟨81186226908195937353104357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54124151272130624902069571 81186226908195937353104357)
            ·
              refine ⟨15222417545286738253707067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81186226908195937353104357 15222417545286738253707067)
              ·
                refine ⟨22833626317930107380560601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15222417545286738253707067 22833626317930107380560601)
                ·
                  refine ⟨17125219738447580535420451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22833626317930107380560601 17125219738447580535420451)
                  ·
                    refine ⟨25687829607671370803130677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17125219738447580535420451 25687829607671370803130677)
                    ·
                      refine ⟨2408234025719191012793501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25687829607671370803130677 2408234025719191012793501)
                      ·
                        rfl

theorem cell23_4690019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_4690019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690019 prefixEnd_4690019 := by exact prefixLift 4690019
  have htrace : WordTrace (prefixWord ++ tailWord_4690019) baseStart_4690019 baseEnd_4690019 := by
    simpa [prefixWord, tailWord_4690019, baseEnd_4690019] using wordTrace_append hprefix tailTrace_4690019
  have hstable : (prefixWord ++ tailWord_4690019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690019).length < 2 ^ (prefixWord ++ tailWord_4690019).sum := by decide
  have hdescent : baseEnd_4690019 < baseStart_4690019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690056 : List Nat := [2, 1, 3, 4, 1, 2, 1, 2, 7]
def baseStart_4690056 : Nat := 118140960795 + 4690056 * 2 ^ 59
def prefixEnd_4690056 : Nat := 4983230072969 + 3 ^ 40 * 4690056 * 2
def baseEnd_4690056 : Nat := 267583669389267485336759

theorem tailTrace_4690056 : CollatzResearch.WordTrace tailWord_4690056 prefixEnd_4690056 267583669389267485336759 := by
  unfold tailWord_4690056
  simp only [CollatzResearch.WordTrace]
  refine ⟨85530197748367792319609011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114040263664490389759478681 85530197748367792319609011)
  ·
    refine ⟨128295296622551688479413517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85530197748367792319609011 128295296622551688479413517)
    ·
      refine ⟨48110736233456883179780069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128295296622551688479413517 48110736233456883179780069)
      ·
        refine ⟨9020763043773165596208763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48110736233456883179780069 9020763043773165596208763)
        ·
          refine ⟨13531144565659748394313145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9020763043773165596208763 13531144565659748394313145)
          ·
            refine ⟨10148358424244811295734859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13531144565659748394313145 10148358424244811295734859)
            ·
              refine ⟨15222537636367216943602289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10148358424244811295734859 15222537636367216943602289)
              ·
                refine ⟨11416903227275412707701717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15222537636367216943602289 11416903227275412707701717)
                ·
                  refine ⟨267583669389267485336759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11416903227275412707701717 267583669389267485336759)
                  ·
                    rfl

theorem cell23_4690056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 7].length) (baseStart_4690056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690056 prefixEnd_4690056 := by exact prefixLift 4690056
  have htrace : WordTrace (prefixWord ++ tailWord_4690056) baseStart_4690056 baseEnd_4690056 := by
    simpa [prefixWord, tailWord_4690056, baseEnd_4690056] using wordTrace_append hprefix tailTrace_4690056
  have hstable : (prefixWord ++ tailWord_4690056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690056).length < 2 ^ (prefixWord ++ tailWord_4690056).sum := by decide
  have hdescent : baseEnd_4690056 < baseStart_4690056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690066 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_4690066 : Nat := 118140960795 + 4690066 * 2 ^ 59
def prefixEnd_4690066 : Nat := 4983230072969 + 3 ^ 40 * 4690066 * 2
def baseEnd_4690066 : Nat := 2408258159309952328905785

theorem tailTrace_4690066 : CollatzResearch.WordTrace tailWord_4690066 prefixEnd_4690066 2408258159309952328905785 := by
  unfold tailWord_4690066
  simp only [CollatzResearch.WordTrace]
  refine ⟨42765190056674839086770513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114040506817799570898054701 42765190056674839086770513)
  ·
    refine ⟨32073892542506129315077885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42765190056674839086770513 32073892542506129315077885)
    ·
      refine ⟨12027709703439798493154207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32073892542506129315077885 12027709703439798493154207)
      ·
        refine ⟨18041564555159697739731311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12027709703439798493154207 18041564555159697739731311)
        ·
          refine ⟨27062346832739546609596967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18041564555159697739731311 27062346832739546609596967)
          ·
            refine ⟨40593520249109319914395451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27062346832739546609596967 40593520249109319914395451)
            ·
              refine ⟨60890280373663979871593177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40593520249109319914395451 60890280373663979871593177)
              ·
                refine ⟨45667710280247984903694883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60890280373663979871593177 45667710280247984903694883)
                ·
                  refine ⟨68501565420371977355542325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45667710280247984903694883 68501565420371977355542325)
                  ·
                    refine ⟨6422021758159872877082093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68501565420371977355542325 6422021758159872877082093)
                    ·
                      refine ⟨2408258159309952328905785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6422021758159872877082093 2408258159309952328905785)
                      ·
                        rfl

theorem cell23_4690066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_4690066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690066 prefixEnd_4690066 := by exact prefixLift 4690066
  have htrace : WordTrace (prefixWord ++ tailWord_4690066) baseStart_4690066 baseEnd_4690066 := by
    simpa [prefixWord, tailWord_4690066, baseEnd_4690066] using wordTrace_append hprefix tailTrace_4690066
  have hstable : (prefixWord ++ tailWord_4690066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690066).length < 2 ^ (prefixWord ++ tailWord_4690066).sum := by decide
  have hdescent : baseEnd_4690066 < baseStart_4690066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690069 : List Nat := [1, 3, 2, 1, 1, 1, 5, 1, 1, 7]
def baseStart_4690069 : Nat := 118140960795 + 4690069 * 2 ^ 59
def prefixEnd_4690069 : Nat := 4983230072969 + 3 ^ 40 * 4690069 * 2
def baseEnd_4690069 : Nat := 802753233250638605722757

theorem tailTrace_4690069 : CollatzResearch.WordTrace tailWord_4690069 prefixEnd_4690069 802753233250638605722757 := by
  unfold tailWord_4690069
  simp only [CollatzResearch.WordTrace]
  refine ⟨171060869645688487859441261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114040579763792325239627507 171060869645688487859441261)
  ·
    refine ⟨64147826117133182947290473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171060869645688487859441261 64147826117133182947290473)
    ·
      refine ⟨48110869587849887210467855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64147826117133182947290473 48110869587849887210467855)
      ·
        refine ⟨72166304381774830815701783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48110869587849887210467855 72166304381774830815701783)
        ·
          refine ⟨108249456572662246223552675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72166304381774830815701783 108249456572662246223552675)
          ·
            refine ⟨162374184858993369335329013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108249456572662246223552675 162374184858993369335329013)
            ·
              refine ⟨15222579830530628375187095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 162374184858993369335329013 15222579830530628375187095)
              ·
                refine ⟨22833869745795942562780643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15222579830530628375187095 22833869745795942562780643)
                ·
                  refine ⟨34250804618693913844170965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22833869745795942562780643 34250804618693913844170965)
                  ·
                    refine ⟨802753233250638605722757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34250804618693913844170965 802753233250638605722757)
                    ·
                      rfl

theorem cell23_4690069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_4690069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690069 prefixEnd_4690069 := by exact prefixLift 4690069
  have htrace : WordTrace (prefixWord ++ tailWord_4690069) baseStart_4690069 baseEnd_4690069 := by
    simpa [prefixWord, tailWord_4690069, baseEnd_4690069] using wordTrace_append hprefix tailTrace_4690069
  have hstable : (prefixWord ++ tailWord_4690069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690069).length < 2 ^ (prefixWord ++ tailWord_4690069).sum := by decide
  have hdescent : baseEnd_4690069 < baseStart_4690069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690084 : List Nat := [2, 3, 1, 2, 5, 1, 1, 2, 2, 2, 2]
def baseStart_4690084 : Nat := 118140960795 + 4690084 * 2 ^ 59
def prefixEnd_4690084 : Nat := 4983230072969 + 3 ^ 40 * 4690084 * 2
def baseEnd_4690084 : Nat := 2408267401961733258480703

theorem tailTrace_4690084 : CollatzResearch.WordTrace tailWord_4690084 prefixEnd_4690084 2408267401961733258480703 := by
  unfold tailWord_4690084
  simp only [CollatzResearch.WordTrace]
  refine ⟨85530708370317072710618653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114040944493756096947491537 85530708370317072710618653)
  ·
    refine ⟨32074015638868902266481995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85530708370317072710618653 32074015638868902266481995)
    ·
      refine ⟨48111023458303353399722993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32074015638868902266481995 48111023458303353399722993)
      ·
        refine ⟨36083267593727515049792245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48111023458303353399722993 36083267593727515049792245)
        ·
          refine ⟨3382806336911954535918023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36083267593727515049792245 3382806336911954535918023)
          ·
            refine ⟨5074209505367931803877035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3382806336911954535918023 5074209505367931803877035)
            ·
              refine ⟨7611314258051897705815553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5074209505367931803877035 7611314258051897705815553)
              ·
                refine ⟨5708485693538923279361665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7611314258051897705815553 5708485693538923279361665)
                ·
                  refine ⟨4281364270154192459521249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5708485693538923279361665 4281364270154192459521249)
                  ·
                    refine ⟨3211023202615644344640937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4281364270154192459521249 3211023202615644344640937)
                    ·
                      refine ⟨2408267401961733258480703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3211023202615644344640937 2408267401961733258480703)
                      ·
                        rfl

theorem cell23_4690084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_4690084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690084 prefixEnd_4690084 := by exact prefixLift 4690084
  have htrace : WordTrace (prefixWord ++ tailWord_4690084) baseStart_4690084 baseEnd_4690084 := by
    simpa [prefixWord, tailWord_4690084, baseEnd_4690084] using wordTrace_append hprefix tailTrace_4690084
  have hstable : (prefixWord ++ tailWord_4690084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690084).length < 2 ^ (prefixWord ++ tailWord_4690084).sum := by decide
  have hdescent : baseEnd_4690084 < baseStart_4690084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690129 : List Nat := [1, 2, 2, 1, 2, 2, 3, 2, 8]
def baseStart_4690129 : Nat := 118140960795 + 4690129 * 2 ^ 59
def prefixEnd_4690129 : Nat := 4983230072969 + 3 ^ 40 * 4690129 * 2
def baseEnd_4690129 : Nat := 267587834287909509157555

theorem tailTrace_4690129 : CollatzResearch.WordTrace tailWord_4690129 prefixEnd_4690129 267587834287909509157555 := by
  unfold tailWord_4690129
  simp only [CollatzResearch.WordTrace]
  refine ⟨171063058025471118106625441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114042038683647412071083627 171063058025471118106625441)
  ·
    refine ⟨128297293519103338579969081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171063058025471118106625441 128297293519103338579969081)
    ·
      refine ⟨96222970139327503934976811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128297293519103338579969081 96222970139327503934976811)
      ·
        refine ⟨144334455208991255902465217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96222970139327503934976811 144334455208991255902465217)
        ·
          refine ⟨108250841406743441926848913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144334455208991255902465217 108250841406743441926848913)
          ·
            refine ⟨81188131055057581445136685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108250841406743441926848913 81188131055057581445136685)
            ·
              refine ⟨30445549145646593041926257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81188131055057581445136685 30445549145646593041926257)
              ·
                refine ⟨22834161859234944781444693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30445549145646593041926257 22834161859234944781444693)
                ·
                  refine ⟨267587834287909509157555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22834161859234944781444693 267587834287909509157555)
                  ·
                    rfl

theorem cell23_4690129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 8].length) (baseStart_4690129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690129 prefixEnd_4690129 := by exact prefixLift 4690129
  have htrace : WordTrace (prefixWord ++ tailWord_4690129) baseStart_4690129 baseEnd_4690129 := by
    simpa [prefixWord, tailWord_4690129, baseEnd_4690129] using wordTrace_append hprefix tailTrace_4690129
  have hstable : (prefixWord ++ tailWord_4690129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690129).length < 2 ^ (prefixWord ++ tailWord_4690129).sum := by decide
  have hdescent : baseEnd_4690129 < baseStart_4690129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690166 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_4690166 : Nat := 118140960795 + 4690166 * 2 ^ 59
def prefixEnd_4690166 : Nat := 4983230072969 + 3 ^ 40 * 4690166 * 2
def baseEnd_4690166 : Nat := 2408309507375401937655325

theorem tailTrace_4690166 : CollatzResearch.WordTrace tailWord_4690166 prefixEnd_4690166 2408309507375401937655325 := by
  unfold tailWord_4690166
  simp only [CollatzResearch.WordTrace]
  refine ⟨10691525470396067089107647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114042938350891382283814901 10691525470396067089107647)
  ·
    refine ⟨16037288205594100633661471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10691525470396067089107647 16037288205594100633661471)
    ·
      refine ⟨24055932308391150950492207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16037288205594100633661471 24055932308391150950492207)
      ·
        refine ⟨36083898462586726425738311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24055932308391150950492207 36083898462586726425738311)
        ·
          refine ⟨54125847693880089638607467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36083898462586726425738311 54125847693880089638607467)
          ·
            refine ⟨81188771540820134457911201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54125847693880089638607467 81188771540820134457911201)
            ·
              refine ⟨60891578655615100843433401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81188771540820134457911201 60891578655615100843433401)
              ·
                refine ⟨45668683991711325632575051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60891578655615100843433401 45668683991711325632575051)
                ·
                  refine ⟨68503025987566988448862577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45668683991711325632575051 68503025987566988448862577)
                  ·
                    refine ⟨51377269490675241336646933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68503025987566988448862577 51377269490675241336646933)
                    ·
                      refine ⟨2408309507375401937655325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51377269490675241336646933 2408309507375401937655325)
                      ·
                        rfl

theorem cell23_4690166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_4690166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690166 prefixEnd_4690166 := by exact prefixLift 4690166
  have htrace : WordTrace (prefixWord ++ tailWord_4690166) baseStart_4690166 baseEnd_4690166 := by
    simpa [prefixWord, tailWord_4690166, baseEnd_4690166] using wordTrace_append hprefix tailTrace_4690166
  have hstable : (prefixWord ++ tailWord_4690166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690166).length < 2 ^ (prefixWord ++ tailWord_4690166).sum := by decide
  have hdescent : baseEnd_4690166 < baseStart_4690166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
