import V185TrunkScan23Chunk0256

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1520444 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 3, 1, 7]
def baseStart_1520444 : Nat := 118140960795 + 1520444 * 2 ^ 59
def prefixEnd_1520444 : Nat := 4983230072969 + 3 ^ 40 * 1520444 * 2
def baseEnd_1520444 : Nat := 780718580244754489557611

theorem tailTrace_1520444 : CollatzResearch.WordTrace tailWord_1520444 prefixEnd_1520444 780718580244754489557611 := by
  unfold tailWord_1520444
  simp only [CollatzResearch.WordTrace]
  refine ⟨27727574251849267003416193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36970099002465689337888257 27727574251849267003416193)
  ·
    refine ⟨20795680688886950252562145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27727574251849267003416193 20795680688886950252562145)
    ·
      refine ⟨15596760516665212689421609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20795680688886950252562145 15596760516665212689421609)
      ·
        refine ⟨11697570387498909517066207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15596760516665212689421609 11697570387498909517066207)
        ·
          refine ⟨17546355581248364275599311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11697570387498909517066207 17546355581248364275599311)
          ·
            refine ⟨26319533371872546413398967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17546355581248364275599311 26319533371872546413398967)
            ·
              refine ⟨39479300057808819620098451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26319533371872546413398967 39479300057808819620098451)
              ·
                refine ⟨59218950086713229430147677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39479300057808819620098451 59218950086713229430147677)
                ·
                  refine ⟨22207106282517461036305379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59218950086713229430147677 22207106282517461036305379)
                  ·
                    refine ⟨33310659423776191554458069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22207106282517461036305379 33310659423776191554458069)
                    ·
                      refine ⟨780718580244754489557611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 33310659423776191554458069 780718580244754489557611)
                      ·
                        rfl

theorem cell23_1520444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_1520444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520444 prefixEnd_1520444 := by exact prefixLift 1520444
  have htrace : WordTrace (prefixWord ++ tailWord_1520444) baseStart_1520444 baseEnd_1520444 := by
    simpa [prefixWord, tailWord_1520444, baseEnd_1520444] using wordTrace_append hprefix tailTrace_1520444
  have hstable : (prefixWord ++ tailWord_1520444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520444).length < 2 ^ (prefixWord ++ tailWord_1520444).sum := by decide
  have hdescent : baseEnd_1520444 < baseStart_1520444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520451 : List Nat := [1, 1, 1, 3, 1, 4, 4, 1, 2, 5]
def baseStart_1520451 : Nat := 118140960795 + 1520451 * 2 ^ 59
def prefixEnd_1520451 : Nat := 4983230072969 + 3 ^ 40 * 1520451 * 2
def baseEnd_1520451 : Nat := 260240724869778654056693

theorem tailTrace_1520451 : CollatzResearch.WordTrace tailWord_1520451 prefixEnd_1520451 260240724869778654056693 := by
  unfold tailWord_1520451
  simp only [CollatzResearch.WordTrace]
  refine ⟨55455403814673174202337207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36970269209782116134891471 55455403814673174202337207)
  ·
    refine ⟨83183105722009761303505811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55455403814673174202337207 83183105722009761303505811)
    ·
      refine ⟨124774658583014641955258717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83183105722009761303505811 124774658583014641955258717)
      ·
        refine ⟨46790496968630490733222019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124774658583014641955258717 46790496968630490733222019)
        ·
          refine ⟨70185745452945736099833029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46790496968630490733222019 70185745452945736099833029)
          ·
            refine ⟨13159827272427325518718693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70185745452945736099833029 13159827272427325518718693)
            ·
              refine ⟨2467467613580123534759755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13159827272427325518718693 2467467613580123534759755)
              ·
                refine ⟨3701201420370185302139633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2467467613580123534759755 3701201420370185302139633)
                ·
                  refine ⟨2775901065277638976604725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3701201420370185302139633 2775901065277638976604725)
                  ·
                    refine ⟨260240724869778654056693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2775901065277638976604725 260240724869778654056693)
                    ·
                      rfl

theorem cell23_1520451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 5].length) (baseStart_1520451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520451 prefixEnd_1520451 := by exact prefixLift 1520451
  have htrace : WordTrace (prefixWord ++ tailWord_1520451) baseStart_1520451 baseEnd_1520451 := by
    simpa [prefixWord, tailWord_1520451, baseEnd_1520451] using wordTrace_append hprefix tailTrace_1520451
  have hstable : (prefixWord ++ tailWord_1520451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520451).length < 2 ^ (prefixWord ++ tailWord_1520451).sum := by decide
  have hdescent : baseEnd_1520451 < baseStart_1520451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520488 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 1, 6, 2]
def baseStart_1520488 : Nat := 118140960795 + 1520488 * 2 ^ 59
def prefixEnd_1520488 : Nat := 4983230072969 + 3 ^ 40 * 1520488 * 2
def baseEnd_1520488 : Nat := 780741173393552317407409

theorem tailTrace_1520488 : CollatzResearch.WordTrace tailWord_1520488 prefixEnd_1520488 780741173393552317407409 := by
  unfold tailWord_1520488
  simp only [CollatzResearch.WordTrace]
  refine ⟨27728376657769564760717059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36971168877026086347622745 27728376657769564760717059)
  ·
    refine ⟨41592564986654347141075589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27728376657769564760717059 41592564986654347141075589)
    ·
      refine ⟨7798605934997690088951673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41592564986654347141075589 7798605934997690088951673)
      ·
        refine ⟨5848954451248267566713755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7798605934997690088951673 5848954451248267566713755)
        ·
          refine ⟨8773431676872401350070633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5848954451248267566713755 8773431676872401350070633)
          ·
            refine ⟨6580073757654301012552975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8773431676872401350070633 6580073757654301012552975)
            ·
              refine ⟨9870110636481451518829463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6580073757654301012552975 9870110636481451518829463)
              ·
                refine ⟨14805165954722177278244195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9870110636481451518829463 14805165954722177278244195)
                ·
                  refine ⟨22207748932083265917366293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14805165954722177278244195 22207748932083265917366293)
                  ·
                    refine ⟨1040988231191403089876545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22207748932083265917366293 1040988231191403089876545)
                    ·
                      refine ⟨780741173393552317407409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1040988231191403089876545 780741173393552317407409)
                      ·
                        rfl

theorem cell23_1520488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_1520488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520488 prefixEnd_1520488 := by exact prefixLift 1520488
  have htrace : WordTrace (prefixWord ++ tailWord_1520488) baseStart_1520488 baseEnd_1520488 := by
    simpa [prefixWord, tailWord_1520488, baseEnd_1520488] using wordTrace_append hprefix tailTrace_1520488
  have hstable : (prefixWord ++ tailWord_1520488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520488).length < 2 ^ (prefixWord ++ tailWord_1520488).sum := by decide
  have hdescent : baseEnd_1520488 < baseStart_1520488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520491 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 4, 2, 3]
def baseStart_1520491 : Nat := 118140960795 + 1520491 * 2 ^ 59
def prefixEnd_1520491 : Nat := 4983230072969 + 3 ^ 40 * 1520491 * 2
def baseEnd_1520491 : Nat := 780742713835515805669895

theorem tailTrace_1520491 : CollatzResearch.WordTrace tailWord_1520491 prefixEnd_1520491 780742713835515805669895 := by
  unfold tailWord_1520491
  simp only [CollatzResearch.WordTrace]
  refine ⟨55456862734528261033793327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36971241823018840689195551 55456862734528261033793327)
  ·
    refine ⟨83185294101792391550689991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55456862734528261033793327 83185294101792391550689991)
    ·
      refine ⟨124777941152688587326034987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83185294101792391550689991 124777941152688587326034987)
      ·
        refine ⟨187166911729032880989052481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124777941152688587326034987 187166911729032880989052481)
        ·
          refine ⟨140375183796774660741789361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187166911729032880989052481 140375183796774660741789361)
          ·
            refine ⟨105281387847580995556342021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140375183796774660741789361 105281387847580995556342021)
            ·
              refine ⟨19740260221421436666814129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105281387847580995556342021 19740260221421436666814129)
              ·
                refine ⟨14805195166066077500110597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19740260221421436666814129 14805195166066077500110597)
                ·
                  refine ⟨2775974093637389531270737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14805195166066077500110597 2775974093637389531270737)
                  ·
                    refine ⟨2081980570228042148453053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2775974093637389531270737 2081980570228042148453053)
                    ·
                      refine ⟨780742713835515805669895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2081980570228042148453053 780742713835515805669895)
                      ·
                        rfl

theorem cell23_1520491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2, 3].length) (baseStart_1520491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520491 prefixEnd_1520491 := by exact prefixLift 1520491
  have htrace : WordTrace (prefixWord ++ tailWord_1520491) baseStart_1520491 baseEnd_1520491 := by
    simpa [prefixWord, tailWord_1520491, baseEnd_1520491] using wordTrace_append hprefix tailTrace_1520491
  have hstable : (prefixWord ++ tailWord_1520491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520491).length < 2 ^ (prefixWord ++ tailWord_1520491).sum := by decide
  have hdescent : baseEnd_1520491 < baseStart_1520491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520515 : List Nat := [1, 1, 1, 3, 4, 1, 4, 3, 1, 4]
def baseStart_1520515 : Nat := 118140960795 + 1520515 * 2 ^ 59
def prefixEnd_1520515 : Nat := 4983230072969 + 3 ^ 40 * 1520515 * 2
def baseEnd_1520515 : Nat := 260251679123741237256595

theorem tailTrace_1520515 : CollatzResearch.WordTrace tailWord_1520515 prefixEnd_1520515 260251679123741237256595 := by
  unfold tailWord_1520515
  simp only [CollatzResearch.WordTrace]
  refine ⟨55457738086441313132666999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36971825390960875421777999 55457738086441313132666999)
  ·
    refine ⟨83186607129661969699000499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55457738086441313132666999 83186607129661969699000499)
    ·
      refine ⟨124779910694492954548500749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83186607129661969699000499 124779910694492954548500749)
      ·
        refine ⟨46792466510434857955687781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124779910694492954548500749 46792466510434857955687781)
        ·
          refine ⟨8773587470706535866691459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46792466510434857955687781 8773587470706535866691459)
          ·
            refine ⟨13160381206059803800037189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8773587470706535866691459 13160381206059803800037189)
            ·
              refine ⟨2467571476136213212506973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13160381206059803800037189 2467571476136213212506973)
              ·
                refine ⟨925339303551079954690115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2467571476136213212506973 925339303551079954690115)
                ·
                  refine ⟨1388008955326619932035173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 925339303551079954690115 1388008955326619932035173)
                  ·
                    refine ⟨260251679123741237256595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1388008955326619932035173 260251679123741237256595)
                    ·
                      rfl

theorem cell23_1520515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3, 1, 4].length) (baseStart_1520515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520515 prefixEnd_1520515 := by exact prefixLift 1520515
  have htrace : WordTrace (prefixWord ++ tailWord_1520515) baseStart_1520515 baseEnd_1520515 := by
    simpa [prefixWord, tailWord_1520515, baseEnd_1520515] using wordTrace_append hprefix tailTrace_1520515
  have hstable : (prefixWord ++ tailWord_1520515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520515).length < 2 ^ (prefixWord ++ tailWord_1520515).sum := by decide
  have hdescent : baseEnd_1520515 < baseStart_1520515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520545 : List Nat := [1, 2, 3, 4, 1, 2, 3, 1, 6]
def baseStart_1520545 : Nat := 118140960795 + 1520545 * 2 ^ 59
def prefixEnd_1520545 : Nat := 4983230072969 + 3 ^ 40 * 1520545 * 2
def baseEnd_1520545 : Nat := 86752271310095399377183

theorem tailTrace_1520545 : CollatzResearch.WordTrace tailWord_1520545 prefixEnd_1520545 86752271310095399377183 := by
  unfold tailWord_1520545
  simp only [CollatzResearch.WordTrace]
  refine ⟨55458832276332628256259089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36972554850888418837506059 55458832276332628256259089)
  ·
    refine ⟨41594124207249471192194317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55458832276332628256259089 41594124207249471192194317)
    ·
      refine ⟨15597796577718551697072869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41594124207249471192194317 15597796577718551697072869)
      ·
        refine ⟨2924586858322228443201163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15597796577718551697072869 2924586858322228443201163)
        ·
          refine ⟨4386880287483342664801745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2924586858322228443201163 4386880287483342664801745)
          ·
            refine ⟨3290160215612506998601309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4386880287483342664801745 3290160215612506998601309)
            ·
              refine ⟨1233810080854690124475491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3290160215612506998601309 1233810080854690124475491)
              ·
                refine ⟨1850715121282035186713237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1233810080854690124475491 1850715121282035186713237)
                ·
                  refine ⟨86752271310095399377183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1850715121282035186713237 86752271310095399377183)
                  ·
                    rfl

theorem cell23_1520545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 6].length) (baseStart_1520545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520545 prefixEnd_1520545 := by exact prefixLift 1520545
  have htrace : WordTrace (prefixWord ++ tailWord_1520545) baseStart_1520545 baseEnd_1520545 := by
    simpa [prefixWord, tailWord_1520545, baseEnd_1520545] using wordTrace_append hprefix tailTrace_1520545
  have hstable : (prefixWord ++ tailWord_1520545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520545).length < 2 ^ (prefixWord ++ tailWord_1520545).sum := by decide
  have hdescent : baseEnd_1520545 < baseStart_1520545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520548 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 3, 5, 2]
def baseStart_1520548 : Nat := 118140960795 + 1520548 * 2 ^ 59
def prefixEnd_1520548 : Nat := 4983230072969 + 3 ^ 40 * 1520548 * 2
def baseEnd_1520548 : Nat := 780771982232822082657133

theorem tailTrace_1520548 : CollatzResearch.WordTrace tailWord_1520548 prefixEnd_1520548 780771982232822082657133 := by
  unfold tailWord_1520548
  simp only [CollatzResearch.WordTrace]
  refine ⟨27729470847660879884309149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36972627796881173179078865 27729470847660879884309149)
  ·
    refine ⟨10398551567872829956615931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27729470847660879884309149 10398551567872829956615931)
    ·
      refine ⟨15597827351809244934923897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10398551567872829956615931 15597827351809244934923897)
      ·
        refine ⟨11698370513856933701192923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15597827351809244934923897 11698370513856933701192923)
        ·
          refine ⟨17547555770785400551789385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11698370513856933701192923 17547555770785400551789385)
          ·
            refine ⟨13160666828089050413842039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17547555770785400551789385 13160666828089050413842039)
            ·
              refine ⟨19741000242133575620763059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13160666828089050413842039 19741000242133575620763059)
              ·
                refine ⟨29611500363200363431144589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19741000242133575620763059 29611500363200363431144589)
                ·
                  refine ⟨11104312636200136286679221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29611500363200363431144589 11104312636200136286679221)
                  ·
                    refine ⟨1041029309643762776876177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11104312636200136286679221 1041029309643762776876177)
                    ·
                      refine ⟨780771982232822082657133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1041029309643762776876177 780771982232822082657133)
                      ·
                        rfl

theorem cell23_1520548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_1520548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520548 prefixEnd_1520548 := by exact prefixLift 1520548
  have htrace : WordTrace (prefixWord ++ tailWord_1520548) baseStart_1520548 baseEnd_1520548 := by
    simpa [prefixWord, tailWord_1520548, baseEnd_1520548] using wordTrace_append hprefix tailTrace_1520548
  have hstable : (prefixWord ++ tailWord_1520548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520548).length < 2 ^ (prefixWord ++ tailWord_1520548).sum := by decide
  have hdescent : baseEnd_1520548 < baseStart_1520548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520565 : List Nat := [1, 3, 3, 2, 1, 1, 2, 3, 2, 3, 2]
def baseStart_1520565 : Nat := 118140960795 + 1520565 * 2 ^ 59
def prefixEnd_1520565 : Nat := 4983230072969 + 3 ^ 40 * 1520565 * 2
def baseEnd_1520565 : Nat := 780780711403948516144555

theorem tailTrace_1520565 : CollatzResearch.WordTrace tailWord_1520565 prefixEnd_1520565 780780711403948516144555 := by
  unfold tailWord_1520565
  simp only [CollatzResearch.WordTrace]
  refine ⟨55459561736260171671987149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36973041157506781114658099 55459561736260171671987149)
  ·
    refine ⟨20797335651097564376995181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55459561736260171671987149 20797335651097564376995181)
    ·
      refine ⟨7799000869161586641373193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20797335651097564376995181 7799000869161586641373193)
      ·
        refine ⟨5849250651871189981029895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7799000869161586641373193 5849250651871189981029895)
        ·
          refine ⟨8773875977806784971544843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5849250651871189981029895 8773875977806784971544843)
          ·
            refine ⟨13160813966710177457317265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8773875977806784971544843 13160813966710177457317265)
            ·
              refine ⟨9870610475032633092987949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13160813966710177457317265 9870610475032633092987949)
              ·
                refine ⟨3701478928137237409870481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9870610475032633092987949 3701478928137237409870481)
                ·
                  refine ⟨2776109196102928057402861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3701478928137237409870481 2776109196102928057402861)
                  ·
                    refine ⟨1041040948538598021526073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2776109196102928057402861 1041040948538598021526073)
                    ·
                      refine ⟨780780711403948516144555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1041040948538598021526073 780780711403948516144555)
                      ·
                        rfl

theorem cell23_1520565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_1520565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520565 prefixEnd_1520565 := by exact prefixLift 1520565
  have htrace : WordTrace (prefixWord ++ tailWord_1520565) baseStart_1520565 baseEnd_1520565 := by
    simpa [prefixWord, tailWord_1520565, baseEnd_1520565] using wordTrace_append hprefix tailTrace_1520565
  have hstable : (prefixWord ++ tailWord_1520565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520565).length < 2 ^ (prefixWord ++ tailWord_1520565).sum := by decide
  have hdescent : baseEnd_1520565 < baseStart_1520565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520581 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 1, 8, 3]
def baseStart_1520581 : Nat := 118140960795 + 1520581 * 2 ^ 59
def prefixEnd_1520581 : Nat := 4983230072969 + 3 ^ 40 * 1520581 * 2
def baseEnd_1520581 : Nat := 780788927094420453544481

theorem tailTrace_1520581 : CollatzResearch.WordTrace tailWord_1520581 prefixEnd_1520581 780788927094420453544481 := by
  unfold tailWord_1520581
  simp only [CollatzResearch.WordTrace]
  refine ⟨55460145304202206404569597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36973430202801470936379731 55460145304202206404569597)
  ·
    refine ⟨20797554489075827401713599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55460145304202206404569597 20797554489075827401713599)
    ·
      refine ⟨31196331733613741102570399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20797554489075827401713599 31196331733613741102570399)
      ·
        refine ⟨46794497600420611653855599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31196331733613741102570399 46794497600420611653855599)
        ·
          refine ⟨70191746400630917480783399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46794497600420611653855599 70191746400630917480783399)
          ·
            refine ⟨105287619600946376221175099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70191746400630917480783399 105287619600946376221175099)
            ·
              refine ⟨157931429401419564331762649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105287619600946376221175099 157931429401419564331762649)
              ·
                refine ⟨118448572051064673248821987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157931429401419564331762649 118448572051064673248821987)
                ·
                  refine ⟨177672858076597009873232981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118448572051064673248821987 177672858076597009873232981)
                  ·
                    refine ⟨2082103805585121209451949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 177672858076597009873232981 2082103805585121209451949)
                    ·
                      refine ⟨780788927094420453544481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2082103805585121209451949 780788927094420453544481)
                      ·
                        rfl

theorem cell23_1520581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 8, 3].length) (baseStart_1520581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520581 prefixEnd_1520581 := by exact prefixLift 1520581
  have htrace : WordTrace (prefixWord ++ tailWord_1520581) baseStart_1520581 baseEnd_1520581 := by
    simpa [prefixWord, tailWord_1520581, baseEnd_1520581] using wordTrace_append hprefix tailTrace_1520581
  have hstable : (prefixWord ++ tailWord_1520581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520581).length < 2 ^ (prefixWord ++ tailWord_1520581).sum := by decide
  have hdescent : baseEnd_1520581 < baseStart_1520581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520588 : List Nat := [2, 2, 1, 4, 1, 1, 1, 3, 4, 4]
def baseStart_1520588 : Nat := 118140960795 + 1520588 * 2 ^ 59
def prefixEnd_1520588 : Nat := 4983230072969 + 3 ^ 40 * 1520588 * 2
def baseEnd_1520588 : Nat := 260264173819667308718983

theorem tailTrace_1520588 : CollatzResearch.WordTrace tailWord_1520588 prefixEnd_1520588 260264173819667308718983 := by
  unfold tailWord_1520588
  simp only [CollatzResearch.WordTrace]
  refine ⟨27730200307588423300037209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36973600410117897733382945 27730200307588423300037209)
  ·
    refine ⟨20797650230691317475027907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27730200307588423300037209 20797650230691317475027907)
    ·
      refine ⟨31196475346036976212541861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20797650230691317475027907 31196475346036976212541861)
      ·
        refine ⟨5849339127381933039851599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31196475346036976212541861 5849339127381933039851599)
        ·
          refine ⟨8774008691072899559777399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5849339127381933039851599 8774008691072899559777399)
          ·
            refine ⟨13161013036609349339666099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8774008691072899559777399 13161013036609349339666099)
            ·
              refine ⟨19741519554914024009499149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13161013036609349339666099 19741519554914024009499149)
              ·
                refine ⟨7403069833092759003562181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19741519554914024009499149 7403069833092759003562181)
                ·
                  refine ⟨1388075593704892313167909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7403069833092759003562181 1388075593704892313167909)
                  ·
                    refine ⟨260264173819667308718983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1388075593704892313167909 260264173819667308718983)
                    ·
                      rfl

theorem cell23_1520588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 4, 4].length) (baseStart_1520588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520588 prefixEnd_1520588 := by exact prefixLift 1520588
  have htrace : WordTrace (prefixWord ++ tailWord_1520588) baseStart_1520588 baseEnd_1520588 := by
    simpa [prefixWord, tailWord_1520588, baseEnd_1520588] using wordTrace_append hprefix tailTrace_1520588
  have hstable : (prefixWord ++ tailWord_1520588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520588).length < 2 ^ (prefixWord ++ tailWord_1520588).sum := by decide
  have hdescent : baseEnd_1520588 < baseStart_1520588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520591 : List Nat := [1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 6]
def baseStart_1520591 : Nat := 118140960795 + 1520591 * 2 ^ 59
def prefixEnd_1520591 : Nat := 4983230072969 + 3 ^ 40 * 1520591 * 2
def baseEnd_1520591 : Nat := 780794061900965414419435

theorem tailTrace_1520591 : CollatzResearch.WordTrace tailWord_1520591 prefixEnd_1520591 780794061900965414419435 := by
  unfold tailWord_1520591
  simp only [CollatzResearch.WordTrace]
  refine ⟨55460510034165978112433627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36973673356110652074955751 55460510034165978112433627)
  ·
    refine ⟨83190765051248967168650441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55460510034165978112433627 83190765051248967168650441)
    ·
      refine ⟨62393073788436725376487831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83190765051248967168650441 62393073788436725376487831)
      ·
        refine ⟨93589610682655088064731747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62393073788436725376487831 93589610682655088064731747)
        ·
          refine ⟨140384416023982632097097621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93589610682655088064731747 140384416023982632097097621)
          ·
            refine ⟨6580519501124185879551451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 140384416023982632097097621 6580519501124185879551451)
            ·
              refine ⟨9870779251686278819327177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6580519501124185879551451 9870779251686278819327177)
              ·
                refine ⟨7403084438764709114495383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9870779251686278819327177 7403084438764709114495383)
                ·
                  refine ⟨11104626658147063671743075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7403084438764709114495383 11104626658147063671743075)
                  ·
                    refine ⟨16656939987220595507614613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11104626658147063671743075 16656939987220595507614613)
                    ·
                      refine ⟨780794061900965414419435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16656939987220595507614613 780794061900965414419435)
                      ·
                        rfl

theorem cell23_1520591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 6].length) (baseStart_1520591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520591 prefixEnd_1520591 := by exact prefixLift 1520591
  have htrace : WordTrace (prefixWord ++ tailWord_1520591) baseStart_1520591 baseEnd_1520591 := by
    simpa [prefixWord, tailWord_1520591, baseEnd_1520591] using wordTrace_append hprefix tailTrace_1520591
  have hstable : (prefixWord ++ tailWord_1520591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520591).length < 2 ^ (prefixWord ++ tailWord_1520591).sum := by decide
  have hdescent : baseEnd_1520591 < baseStart_1520591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520601 : List Nat := [1, 2, 1, 2, 5, 1, 1, 10]
def baseStart_1520601 : Nat := 118140960795 + 1520601 * 2 ^ 59
def prefixEnd_1520601 : Nat := 4983230072969 + 3 ^ 40 * 1520601 * 2
def baseEnd_1520601 : Nat := 28918488766944828714607

theorem tailTrace_1520601 : CollatzResearch.WordTrace tailWord_1520601 prefixEnd_1520601 28918488766944828714607 := by
  unfold tailWord_1520601
  simp only [CollatzResearch.WordTrace]
  refine ⟨55460874764129749820297657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36973916509419833213531771 55460874764129749820297657)
  ·
    refine ⟨41595656073097312365223243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55460874764129749820297657 41595656073097312365223243)
    ·
      refine ⟨62393484109645968547834865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41595656073097312365223243 62393484109645968547834865)
      ·
        refine ⟨46795113082234476410876149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62393484109645968547834865 46795113082234476410876149)
        ·
          refine ⟨4387041851459482163519639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46795113082234476410876149 4387041851459482163519639)
          ·
            refine ⟨6580562777189223245279459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4387041851459482163519639 6580562777189223245279459)
            ·
              refine ⟨9870844165783834867919189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6580562777189223245279459 9870844165783834867919189)
              ·
                refine ⟨28918488766944828714607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9870844165783834867919189 28918488766944828714607)
                ·
                  rfl

theorem cell23_1520601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 10].length) (baseStart_1520601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520601 prefixEnd_1520601 := by exact prefixLift 1520601
  have htrace : WordTrace (prefixWord ++ tailWord_1520601) baseStart_1520601 baseEnd_1520601 := by
    simpa [prefixWord, tailWord_1520601, baseEnd_1520601] using wordTrace_append hprefix tailTrace_1520601
  have hstable : (prefixWord ++ tailWord_1520601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520601).length < 2 ^ (prefixWord ++ tailWord_1520601).sum := by decide
  have hdescent : baseEnd_1520601 < baseStart_1520601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520615 : List Nat := [1, 1, 5, 2, 2, 2, 1, 1, 3, 2, 3]
def baseStart_1520615 : Nat := 118140960795 + 1520615 * 2 ^ 59
def prefixEnd_1520615 : Nat := 4983230072969 + 3 ^ 40 * 1520615 * 2
def baseEnd_1520615 : Nat := 780806385436673320519325

theorem tailTrace_1520615 : CollatzResearch.WordTrace tailWord_1520615 prefixEnd_1520615 780806385436673320519325 := by
  unfold tailWord_1520615
  simp only [CollatzResearch.WordTrace]
  refine ⟨55461385386079030211307299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36974256924052686807538199 55461385386079030211307299)
  ·
    refine ⟨83192078079118545316960949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55461385386079030211307299 83192078079118545316960949)
    ·
      refine ⟨7799257319917363623465089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83192078079118545316960949 7799257319917363623465089)
      ·
        refine ⟨5849442989938022717598817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7799257319917363623465089 5849442989938022717598817)
        ·
          refine ⟨4387082242453517038199113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5849442989938022717598817 4387082242453517038199113)
          ·
            refine ⟨3290311681840137778649335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4387082242453517038199113 3290311681840137778649335)
            ·
              refine ⟨4935467522760206667974003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3290311681840137778649335 4935467522760206667974003)
              ·
                refine ⟨7403201284140310001961005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4935467522760206667974003 7403201284140310001961005)
                ·
                  refine ⟨2776200481552616250735377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7403201284140310001961005 2776200481552616250735377)
                  ·
                    refine ⟨2082150361164462188051533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2776200481552616250735377 2082150361164462188051533)
                    ·
                      refine ⟨780806385436673320519325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2082150361164462188051533 780806385436673320519325)
                      ·
                        rfl

theorem cell23_1520615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_1520615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520615 prefixEnd_1520615 := by exact prefixLift 1520615
  have htrace : WordTrace (prefixWord ++ tailWord_1520615) baseStart_1520615 baseEnd_1520615 := by
    simpa [prefixWord, tailWord_1520615, baseEnd_1520615] using wordTrace_append hprefix tailTrace_1520615
  have hstable : (prefixWord ++ tailWord_1520615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520615).length < 2 ^ (prefixWord ++ tailWord_1520615).sum := by decide
  have hdescent : baseEnd_1520615 < baseStart_1520615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520691 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 11]
def baseStart_1520691 : Nat := 118140960795 + 1520691 * 2 ^ 59
def prefixEnd_1520691 : Nat := 4983230072969 + 3 ^ 40 * 1520691 * 2
def baseEnd_1520691 : Nat := 86760601107379447018775

theorem tailTrace_1520691 : CollatzResearch.WordTrace tailWord_1520691 prefixEnd_1520691 86760601107379447018775 := by
  unfold tailWord_1520691
  simp only [CollatzResearch.WordTrace]
  refine ⟨55464157333803695191073927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36976104889202463460715951 55464157333803695191073927)
  ·
    refine ⟨83196236000705542786610891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55464157333803695191073927 83196236000705542786610891)
    ·
      refine ⟨124794354001058314179916337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83196236000705542786610891 124794354001058314179916337)
      ·
        refine ⟨93595765500793735634937253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124794354001058314179916337 93595765500793735634937253)
        ·
          refine ⟨17549206031398825431550735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93595765500793735634937253 17549206031398825431550735)
          ·
            refine ⟨26323809047098238147326103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17549206031398825431550735 26323809047098238147326103)
            ·
              refine ⟨39485713570647357220989155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26323809047098238147326103 39485713570647357220989155)
              ·
                refine ⟨59228570355971035831483733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39485713570647357220989155 59228570355971035831483733)
                ·
                  refine ⟨86760601107379447018775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 59228570355971035831483733 86760601107379447018775)
                  ·
                    rfl

theorem cell23_1520691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 11].length) (baseStart_1520691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520691 prefixEnd_1520691 := by exact prefixLift 1520691
  have htrace : WordTrace (prefixWord ++ tailWord_1520691) baseStart_1520691 baseEnd_1520691 := by
    simpa [prefixWord, tailWord_1520691, baseEnd_1520691] using wordTrace_append hprefix tailTrace_1520691
  have hstable : (prefixWord ++ tailWord_1520691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520691).length < 2 ^ (prefixWord ++ tailWord_1520691).sum := by decide
  have hdescent : baseEnd_1520691 < baseStart_1520691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520698 : List Nat := [3, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4]
def baseStart_1520698 : Nat := 118140960795 + 1520698 * 2 ^ 59
def prefixEnd_1520698 : Nat := 4983230072969 + 3 ^ 40 * 1520698 * 2
def baseEnd_1520698 : Nat := 780849004330996495781443

theorem tailTrace_1520698 : CollatzResearch.WordTrace tailWord_1520698 prefixEnd_1520698 780849004330996495781443 := by
  unfold tailWord_1520698
  simp only [CollatzResearch.WordTrace]
  refine ⟨13866103161194583846644687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36976275096518890257719165 13866103161194583846644687)
  ·
    refine ⟨20799154741791875769967031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13866103161194583846644687 20799154741791875769967031)
    ·
      refine ⟨31198732112687813654950547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20799154741791875769967031 31198732112687813654950547)
      ·
        refine ⟨46798098169031720482425821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31198732112687813654950547 46798098169031720482425821)
        ·
          refine ⟨17549286813386895180909683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46798098169031720482425821 17549286813386895180909683)
          ·
            refine ⟨26323930220080342771364525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17549286813386895180909683 26323930220080342771364525)
            ·
              refine ⟨9871473832530128539261697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26323930220080342771364525 9871473832530128539261697)
              ·
                refine ⟨7403605374397596404446273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9871473832530128539261697 7403605374397596404446273)
                ·
                  refine ⟨5552704030798197303334705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7403605374397596404446273 5552704030798197303334705)
                  ·
                    refine ⟨4164528023098647977501029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5552704030798197303334705 4164528023098647977501029)
                    ·
                      refine ⟨780849004330996495781443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4164528023098647977501029 780849004330996495781443)
                      ·
                        rfl

theorem cell23_1520698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_1520698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520698 prefixEnd_1520698 := by exact prefixLift 1520698
  have htrace : WordTrace (prefixWord ++ tailWord_1520698) baseStart_1520698 baseEnd_1520698 := by
    simpa [prefixWord, tailWord_1520698, baseEnd_1520698] using wordTrace_append hprefix tailTrace_1520698
  have hstable : (prefixWord ++ tailWord_1520698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520698).length < 2 ^ (prefixWord ++ tailWord_1520698).sum := by decide
  have hdescent : baseEnd_1520698 < baseStart_1520698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520748 : List Nat := [2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 5]
def baseStart_1520748 : Nat := 118140960795 + 1520748 * 2 ^ 59
def prefixEnd_1520748 : Nat := 4983230072969 + 3 ^ 40 * 1520748 * 2
def baseEnd_1520748 : Nat := 780874678363721300156213

theorem tailTrace_1520748 : CollatzResearch.WordTrace tailWord_1520748 prefixEnd_1520748 780874678363721300156213 := by
  unfold tailWord_1520748
  simp only [CollatzResearch.WordTrace]
  refine ⟨27733118147298596962949449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36977490863064795950599265 27733118147298596962949449)
  ·
    refine ⟨20799838610473947722212087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27733118147298596962949449 20799838610473947722212087)
    ·
      refine ⟨31199757915710921583318131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20799838610473947722212087 31199757915710921583318131)
      ·
        refine ⟨46799636873566382374977197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31199757915710921583318131 46799636873566382374977197)
        ·
          refine ⟨17549863827587393390616449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46799636873566382374977197 17549863827587393390616449)
          ·
            refine ⟨13162397870690545042962337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17549863827587393390616449 13162397870690545042962337)
            ·
              refine ⟨9871798403017908782221753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13162397870690545042962337 9871798403017908782221753)
              ·
                refine ⟨7403848802263431586666315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9871798403017908782221753 7403848802263431586666315)
                ·
                  refine ⟨11105773203395147379999473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7403848802263431586666315 11105773203395147379999473)
                  ·
                    refine ⟨8329329902546360534999605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11105773203395147379999473 8329329902546360534999605)
                    ·
                      refine ⟨780874678363721300156213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8329329902546360534999605 780874678363721300156213)
                      ·
                        rfl

theorem cell23_1520748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_1520748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520748 prefixEnd_1520748 := by exact prefixLift 1520748
  have htrace : WordTrace (prefixWord ++ tailWord_1520748) baseStart_1520748 baseEnd_1520748 := by
    simpa [prefixWord, tailWord_1520748, baseEnd_1520748] using wordTrace_append hprefix tailTrace_1520748
  have hstable : (prefixWord ++ tailWord_1520748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520748).length < 2 ^ (prefixWord ++ tailWord_1520748).sum := by decide
  have hdescent : baseEnd_1520748 < baseStart_1520748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520775 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 1, 6, 2]
def baseStart_1520775 : Nat := 118140960795 + 1520775 * 2 ^ 59
def prefixEnd_1520775 : Nat := 4983230072969 + 3 ^ 40 * 1520775 * 2
def baseEnd_1520775 : Nat := 780888542341392694518589

theorem tailTrace_1520775 : CollatzResearch.WordTrace tailWord_1520775 prefixEnd_1520775 780888542341392694518589 := by
  unfold tailWord_1520775
  simp only [CollatzResearch.WordTrace]
  refine ⟨55467221065499377537131779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36978147376999585024754519 55467221065499377537131779)
  ·
    refine ⟨83200831598249066305697669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55467221065499377537131779 83200831598249066305697669)
    ·
      refine ⟨15600155924671699932318313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83200831598249066305697669 15600155924671699932318313)
      ·
        refine ⟨11700116943503774949238735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15600155924671699932318313 11700116943503774949238735)
        ·
          refine ⟨17550175415255662423858103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11700116943503774949238735 17550175415255662423858103)
          ·
            refine ⟨26325263122883493635787155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17550175415255662423858103 26325263122883493635787155)
            ·
              refine ⟨39487894684325240453680733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26325263122883493635787155 39487894684325240453680733)
              ·
                refine ⟨14807960506621965170130275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39487894684325240453680733 14807960506621965170130275)
                ·
                  refine ⟨22211940759932947755195413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14807960506621965170130275 22211940759932947755195413)
                  ·
                    refine ⟨1041184723121856926024785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22211940759932947755195413 1041184723121856926024785)
                    ·
                      refine ⟨780888542341392694518589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1041184723121856926024785 780888542341392694518589)
                      ·
                        rfl

theorem cell23_1520775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_1520775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520775 prefixEnd_1520775 := by exact prefixLift 1520775
  have htrace : WordTrace (prefixWord ++ tailWord_1520775) baseStart_1520775 baseEnd_1520775 := by
    simpa [prefixWord, tailWord_1520775, baseEnd_1520775] using wordTrace_append hprefix tailTrace_1520775
  have hstable : (prefixWord ++ tailWord_1520775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520775).length < 2 ^ (prefixWord ++ tailWord_1520775).sum := by decide
  have hdescent : baseEnd_1520775 < baseStart_1520775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520792 : List Nat := [2, 1, 2, 4, 2, 2, 2, 1, 2, 1, 4]
def baseStart_1520792 : Nat := 118140960795 + 1520792 * 2 ^ 59
def prefixEnd_1520792 : Nat := 4983230072969 + 3 ^ 40 * 1520792 * 2
def baseEnd_1520792 : Nat := 780897271512519128006011

theorem tailTrace_1520792 : CollatzResearch.WordTrace tailWord_1520792 prefixEnd_1520792 780897271512519128006011 := by
  unfold tailWord_1520792
  simp only [CollatzResearch.WordTrace]
  refine ⟨27733920553218894720250315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36978560737625192960333753 27733920553218894720250315)
  ·
    refine ⟨41600880829828342080375473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27733920553218894720250315 41600880829828342080375473)
    ·
      refine ⟨31200660622371256560281605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41600880829828342080375473 31200660622371256560281605)
      ·
        refine ⟨5850123866694610605052801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31200660622371256560281605 5850123866694610605052801)
        ·
          refine ⟨4387592900020957953789601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5850123866694610605052801 4387592900020957953789601)
          ·
            refine ⟨3290694675015718465342201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4387592900020957953789601 3290694675015718465342201)
            ·
              refine ⟨2468021006261788849006651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3290694675015718465342201 2468021006261788849006651)
              ·
                refine ⟨3702031509392683273509977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2468021006261788849006651 3702031509392683273509977)
                ·
                  refine ⟨2776523632044512455132483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3702031509392683273509977 2776523632044512455132483)
                  ·
                    refine ⟨4164785448066768682698725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2776523632044512455132483 4164785448066768682698725)
                    ·
                      refine ⟨780897271512519128006011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4164785448066768682698725 780897271512519128006011)
                      ·
                        rfl

theorem cell23_1520792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_1520792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520792 prefixEnd_1520792 := by exact prefixLift 1520792
  have htrace : WordTrace (prefixWord ++ tailWord_1520792) baseStart_1520792 baseEnd_1520792 := by
    simpa [prefixWord, tailWord_1520792, baseEnd_1520792] using wordTrace_append hprefix tailTrace_1520792
  have hstable : (prefixWord ++ tailWord_1520792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520792).length < 2 ^ (prefixWord ++ tailWord_1520792).sum := by decide
  have hdescent : baseEnd_1520792 < baseStart_1520792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520819 : List Nat := [1, 1, 1, 2, 3, 2, 6, 2, 1, 4]
def baseStart_1520819 : Nat := 118140960795 + 1520819 * 2 ^ 59
def prefixEnd_1520819 : Nat := 4983230072969 + 3 ^ 40 * 1520819 * 2
def baseEnd_1520819 : Nat := 260303711830063507456129

theorem tailTrace_1520819 : CollatzResearch.WordTrace tailWord_1520819 prefixEnd_1520819 260303711830063507456129 := by
  unfold tailWord_1520819
  simp only [CollatzResearch.WordTrace]
  refine ⟨55468825877339973051733511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36979217251559982034489007 55468825877339973051733511)
  ·
    refine ⟨83203238816009959577600267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55468825877339973051733511 83203238816009959577600267)
    ·
      refine ⟨124804858224014939366400401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83203238816009959577600267 124804858224014939366400401)
      ·
        refine ⟨93603643668011204524800301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124804858224014939366400401 93603643668011204524800301)
        ·
          refine ⟨35101366375504201696800113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93603643668011204524800301 35101366375504201696800113)
          ·
            refine ⟨26326024781628151272600085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35101366375504201696800113 26326024781628151272600085)
            ·
              refine ⟨1234032411638819590903129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26326024781628151272600085 1234032411638819590903129)
              ·
                refine ⟨925524308729114693177347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1234032411638819590903129 925524308729114693177347)
                ·
                  refine ⟨1388286463093672039766021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 925524308729114693177347 1388286463093672039766021)
                  ·
                    refine ⟨260303711830063507456129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1388286463093672039766021 260303711830063507456129)
                    ·
                      rfl

theorem cell23_1520819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2, 1, 4].length) (baseStart_1520819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520819 prefixEnd_1520819 := by exact prefixLift 1520819
  have htrace : WordTrace (prefixWord ++ tailWord_1520819) baseStart_1520819 baseEnd_1520819 := by
    simpa [prefixWord, tailWord_1520819, baseEnd_1520819] using wordTrace_append hprefix tailTrace_1520819
  have hstable : (prefixWord ++ tailWord_1520819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520819).length < 2 ^ (prefixWord ++ tailWord_1520819).sum := by decide
  have hdescent : baseEnd_1520819 < baseStart_1520819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520842 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 5, 1, 3]
def baseStart_1520842 : Nat := 118140960795 + 1520842 * 2 ^ 59
def prefixEnd_1520842 : Nat := 4983230072969 + 3 ^ 40 * 1520842 * 2
def baseEnd_1520842 : Nat := 780922945545243932380781

theorem tailTrace_1520842 : CollatzResearch.WordTrace tailWord_1520842 prefixEnd_1520842 780922945545243932380781 := by
  unfold tailWord_1520842
  simp only [CollatzResearch.WordTrace]
  refine ⟨13867416189064161994955195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36979776504171098653213853 13867416189064161994955195)
  ·
    refine ⟨20801124283596242992432793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13867416189064161994955195 20801124283596242992432793)
    ·
      refine ⟨15600843212697182244324595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20801124283596242992432793 15600843212697182244324595)
      ·
        refine ⟨23401264819045773366486893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15600843212697182244324595 23401264819045773366486893)
        ·
          refine ⟨8775474307142165012432585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23401264819045773366486893 8775474307142165012432585)
          ·
            refine ⟨6581605730356623759324439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8775474307142165012432585 6581605730356623759324439)
            ·
              refine ⟨9872408595534935638986659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6581605730356623759324439 9872408595534935638986659)
              ·
                refine ⟨14808612893302403458479989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9872408595534935638986659 14808612893302403458479989)
                ·
                  refine ⟨1388307458747100324232499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14808612893302403458479989 1388307458747100324232499)
                  ·
                    refine ⟨2082461188120650486348749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1388307458747100324232499 2082461188120650486348749)
                    ·
                      refine ⟨780922945545243932380781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2082461188120650486348749 780922945545243932380781)
                      ·
                        rfl

theorem cell23_1520842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_1520842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520842 prefixEnd_1520842 := by exact prefixLift 1520842
  have htrace : WordTrace (prefixWord ++ tailWord_1520842) baseStart_1520842 baseEnd_1520842 := by
    simpa [prefixWord, tailWord_1520842, baseEnd_1520842] using wordTrace_append hprefix tailTrace_1520842
  have hstable : (prefixWord ++ tailWord_1520842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520842).length < 2 ^ (prefixWord ++ tailWord_1520842).sum := by decide
  have hdescent : baseEnd_1520842 < baseStart_1520842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520846 : List Nat := [4, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3]
def baseStart_1520846 : Nat := 118140960795 + 1520846 * 2 ^ 59
def prefixEnd_1520846 : Nat := 4983230072969 + 3 ^ 40 * 1520846 * 2
def baseEnd_1520846 : Nat := 780924999467861916730763

theorem tailTrace_1520846 : CollatzResearch.WordTrace tailWord_1520846 prefixEnd_1520846 780924999467861916730763 := by
  unfold tailWord_1520846
  simp only [CollatzResearch.WordTrace]
  refine ⟨6933726331030269582870799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36979873765494771108644261 6933726331030269582870799)
  ·
    refine ⟨10400589496545404374306199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6933726331030269582870799 10400589496545404374306199)
    ·
      refine ⟨15600884244818106561459299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10400589496545404374306199 15600884244818106561459299)
      ·
        refine ⟨23401326367227159842188949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15600884244818106561459299 23401326367227159842188949)
        ·
          refine ⟨1096937173463773117602607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23401326367227159842188949 1096937173463773117602607)
          ·
            refine ⟨1645405760195659676403911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096937173463773117602607 1645405760195659676403911)
            ·
              refine ⟨2468108640293489514605867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1645405760195659676403911 2468108640293489514605867)
              ·
                refine ⟨3702162960440234271908801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2468108640293489514605867 3702162960440234271908801)
                ·
                  refine ⟨2776622220330175703931601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3702162960440234271908801 2776622220330175703931601)
                  ·
                    refine ⟨2082466665247631777948701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2776622220330175703931601 2082466665247631777948701)
                    ·
                      refine ⟨780924999467861916730763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2082466665247631777948701 780924999467861916730763)
                      ·
                        rfl

theorem cell23_1520846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3].length) (baseStart_1520846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520846 prefixEnd_1520846 := by exact prefixLift 1520846
  have htrace : WordTrace (prefixWord ++ tailWord_1520846) baseStart_1520846 baseEnd_1520846 := by
    simpa [prefixWord, tailWord_1520846, baseEnd_1520846] using wordTrace_append hprefix tailTrace_1520846
  have hstable : (prefixWord ++ tailWord_1520846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520846).length < 2 ^ (prefixWord ++ tailWord_1520846).sum := by decide
  have hdescent : baseEnd_1520846 < baseStart_1520846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520895 : List Nat := [1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 6]
def baseStart_1520895 : Nat := 118140960795 + 1520895 * 2 ^ 59
def prefixEnd_1520895 : Nat := 4983230072969 + 3 ^ 40 * 1520895 * 2
def baseEnd_1520895 : Nat := 780950160019932225018037

theorem tailTrace_1520895 : CollatzResearch.WordTrace tailWord_1520895 prefixEnd_1520895 780950160019932225018037 := by
  unfold tailWord_1520895
  simp only [CollatzResearch.WordTrace]
  refine ⟨55471597825064638031500139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36981065216709758687666759 55471597825064638031500139)
  ·
    refine ⟨83207396737596957047250209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55471597825064638031500139 83207396737596957047250209)
    ·
      refine ⟨62405547553197717785437657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83207396737596957047250209 62405547553197717785437657)
      ·
        refine ⟨46804160664898288339078243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62405547553197717785437657 46804160664898288339078243)
        ·
          refine ⟨70206240997347432508617365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46804160664898288339078243 70206240997347432508617365)
          ·
            refine ⟨3290917546750660898841439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 70206240997347432508617365 3290917546750660898841439)
            ·
              refine ⟨4936376320125991348262159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3290917546750660898841439 4936376320125991348262159)
              ·
                refine ⟨7404564480188987022393239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4936376320125991348262159 7404564480188987022393239)
                ·
                  refine ⟨11106846720283480533589859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7404564480188987022393239 11106846720283480533589859)
                  ·
                    refine ⟨16660270080425220800384789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11106846720283480533589859 16660270080425220800384789)
                    ·
                      refine ⟨780950160019932225018037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16660270080425220800384789 780950160019932225018037)
                      ·
                        rfl

theorem cell23_1520895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_1520895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520895 prefixEnd_1520895 := by exact prefixLift 1520895
  have htrace : WordTrace (prefixWord ++ tailWord_1520895) baseStart_1520895 baseEnd_1520895 := by
    simpa [prefixWord, tailWord_1520895, baseEnd_1520895] using wordTrace_append hprefix tailTrace_1520895
  have hstable : (prefixWord ++ tailWord_1520895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520895).length < 2 ^ (prefixWord ++ tailWord_1520895).sum := by decide
  have hdescent : baseEnd_1520895 < baseStart_1520895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520899 : List Nat := [1, 1, 1, 3, 2, 4, 2, 2, 3, 2, 2]
def baseStart_1520899 : Nat := 118140960795 + 1520899 * 2 ^ 59
def prefixEnd_1520899 : Nat := 4983230072969 + 3 ^ 40 * 1520899 * 2
def baseEnd_1520899 : Nat := 780952213942550209368019

theorem tailTrace_1520899 : CollatzResearch.WordTrace tailWord_1520899 prefixEnd_1520899 780952213942550209368019 := by
  unfold tailWord_1520899
  simp only [CollatzResearch.WordTrace]
  refine ⟨55471743717050146714645751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36981162478033431143097167 55471743717050146714645751)
  ·
    refine ⟨83207615575575220071968627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55471743717050146714645751 83207615575575220071968627)
    ·
      refine ⟨124811423363362830107952941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83207615575575220071968627 124811423363362830107952941)
      ·
        refine ⟨46804283761261061290482353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124811423363362830107952941 46804283761261061290482353)
        ·
          refine ⟨35103212820945795967861765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46804283761261061290482353 35103212820945795967861765)
          ·
            refine ⟨6581852403927336743974081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35103212820945795967861765 6581852403927336743974081)
            ·
              refine ⟨4936389302945502557980561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6581852403927336743974081 4936389302945502557980561)
              ·
                refine ⟨3702291977209126918485421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4936389302945502557980561 3702291977209126918485421)
                ·
                  refine ⟨1388359491453422594432033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3702291977209126918485421 1388359491453422594432033)
                  ·
                    refine ⟨1041269618590066945824025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1388359491453422594432033 1041269618590066945824025)
                    ·
                      refine ⟨780952213942550209368019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1041269618590066945824025 780952213942550209368019)
                      ·
                        rfl

theorem cell23_1520899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3, 2, 2].length) (baseStart_1520899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520899 prefixEnd_1520899 := by exact prefixLift 1520899
  have htrace : WordTrace (prefixWord ++ tailWord_1520899) baseStart_1520899 baseEnd_1520899 := by
    simpa [prefixWord, tailWord_1520899, baseEnd_1520899] using wordTrace_append hprefix tailTrace_1520899
  have hstable : (prefixWord ++ tailWord_1520899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520899).length < 2 ^ (prefixWord ++ tailWord_1520899).sum := by decide
  have hdescent : baseEnd_1520899 < baseStart_1520899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520950 : List Nat := [5, 1, 2, 3, 2, 1, 1, 2, 1, 1, 4]
def baseStart_1520950 : Nat := 118140960795 + 1520950 * 2 ^ 59
def prefixEnd_1520950 : Nat := 4983230072969 + 3 ^ 40 * 1520950 * 2
def baseEnd_1520950 : Nat := 780978401455929509830285

theorem tailTrace_1520950 : CollatzResearch.WordTrace tailWord_1520950 prefixEnd_1520950 780978401455929509830285 := by
  unfold tailWord_1520950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3467100239991586401547019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36982402559910254949834869 3467100239991586401547019)
  ·
    refine ⟨5200650359987379602320529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3467100239991586401547019 5200650359987379602320529)
    ·
      refine ⟨3900487769990534701740397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5200650359987379602320529 3900487769990534701740397)
      ·
        refine ⟨1462682913746450513152649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3900487769990534701740397 1462682913746450513152649)
        ·
          refine ⟨1097012185309837884864487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1462682913746450513152649 1097012185309837884864487)
          ·
            refine ⟨1645518277964756827296731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1097012185309837884864487 1645518277964756827296731)
            ·
              refine ⟨2468277416947135240945097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1645518277964756827296731 2468277416947135240945097)
              ·
                refine ⟨1851208062710351430708823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2468277416947135240945097 1851208062710351430708823)
                ·
                  refine ⟨2776812094065527146063235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1851208062710351430708823 2776812094065527146063235)
                  ·
                    refine ⟨4165218141098290719094853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2776812094065527146063235 4165218141098290719094853)
                    ·
                      refine ⟨780978401455929509830285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4165218141098290719094853 780978401455929509830285)
                      ·
                        rfl

theorem cell23_1520950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_1520950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520950 prefixEnd_1520950 := by exact prefixLift 1520950
  have htrace : WordTrace (prefixWord ++ tailWord_1520950) baseStart_1520950 baseEnd_1520950 := by
    simpa [prefixWord, tailWord_1520950, baseEnd_1520950] using wordTrace_append hprefix tailTrace_1520950
  have hstable : (prefixWord ++ tailWord_1520950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520950).length < 2 ^ (prefixWord ++ tailWord_1520950).sum := by decide
  have hdescent : baseEnd_1520950 < baseStart_1520950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520953 : List Nat := [1, 2, 1, 6, 3, 1, 1, 2, 1, 2, 3]
def baseStart_1520953 : Nat := 118140960795 + 1520953 * 2 ^ 59
def prefixEnd_1520953 : Nat := 4983230072969 + 3 ^ 40 * 1520953 * 2
def baseEnd_1520953 : Nat := 780979941897892998092771

theorem tailTrace_1520953 : CollatzResearch.WordTrace tailWord_1520953 prefixEnd_1520953 780979941897892998092771 := by
  unfold tailWord_1520953
  simp only [CollatzResearch.WordTrace]
  refine ⟨55473713258854513937111513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36982475505903009291407675 55473713258854513937111513)
  ·
    refine ⟨41605284944140885452833635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55473713258854513937111513 41605284944140885452833635)
    ·
      refine ⟨62407927416211328179250453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41605284944140885452833635 62407927416211328179250453)
      ·
        refine ⟨2925371597634906008402365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 62407927416211328179250453 2925371597634906008402365)
        ·
          refine ⟨1097014349113089753150887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2925371597634906008402365 1097014349113089753150887)
          ·
            refine ⟨1645521523669634629726331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1097014349113089753150887 1645521523669634629726331)
            ·
              refine ⟨2468282285504451944589497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1645521523669634629726331 2468282285504451944589497)
              ·
                refine ⟨1851211714128338958442123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2468282285504451944589497 1851211714128338958442123)
                ·
                  refine ⟨2776817571192508437663185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1851211714128338958442123 2776817571192508437663185)
                  ·
                    refine ⟨2082613178394381328247389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2776817571192508437663185 2082613178394381328247389)
                    ·
                      refine ⟨780979941897892998092771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2082613178394381328247389 780979941897892998092771)
                      ·
                        rfl

theorem cell23_1520953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_1520953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520953 prefixEnd_1520953 := by exact prefixLift 1520953
  have htrace : WordTrace (prefixWord ++ tailWord_1520953) baseStart_1520953 baseEnd_1520953 := by
    simpa [prefixWord, tailWord_1520953, baseEnd_1520953] using wordTrace_append hprefix tailTrace_1520953
  have hstable : (prefixWord ++ tailWord_1520953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520953).length < 2 ^ (prefixWord ++ tailWord_1520953).sum := by decide
  have hdescent : baseEnd_1520953 < baseStart_1520953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520959 : List Nat := [1, 1, 2, 2, 4, 3, 1, 1, 3, 3, 2]
def baseStart_1520959 : Nat := 118140960795 + 1520959 * 2 ^ 59
def prefixEnd_1520959 : Nat := 4983230072969 + 3 ^ 40 * 1520959 * 2
def baseEnd_1520959 : Nat := 780983022781819974617743

theorem tailTrace_1520959 : CollatzResearch.WordTrace tailWord_1520959 prefixEnd_1520959 780983022781819974617743 := by
  unfold tailWord_1520959
  simp only [CollatzResearch.WordTrace]
  refine ⟨55473932096832776961829931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36982621397888517974553287 55473932096832776961829931)
  ·
    refine ⟨83210898145249165442744897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55473932096832776961829931 83210898145249165442744897)
    ·
      refine ⟨62408173608936874082058673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83210898145249165442744897 62408173608936874082058673)
      ·
        refine ⟨46806130206702655561544005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62408173608936874082058673 46806130206702655561544005)
        ·
          refine ⟨8776149413756747917789501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46806130206702655561544005 8776149413756747917789501)
          ·
            refine ⟨3291056030158780469171063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8776149413756747917789501 3291056030158780469171063)
            ·
              refine ⟨4936584045238170703756595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3291056030158780469171063 4936584045238170703756595)
              ·
                refine ⟨7404876067857256055634893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4936584045238170703756595 7404876067857256055634893)
                ·
                  refine ⟨2776828525446471020863085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7404876067857256055634893 2776828525446471020863085)
                  ·
                    refine ⟨1041310697042426632823657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2776828525446471020863085 1041310697042426632823657)
                    ·
                      refine ⟨780983022781819974617743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1041310697042426632823657 780983022781819974617743)
                      ·
                        rfl

theorem cell23_1520959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 3, 2].length) (baseStart_1520959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520959 prefixEnd_1520959 := by exact prefixLift 1520959
  have htrace : WordTrace (prefixWord ++ tailWord_1520959) baseStart_1520959 baseEnd_1520959 := by
    simpa [prefixWord, tailWord_1520959, baseEnd_1520959] using wordTrace_append hprefix tailTrace_1520959
  have hstable : (prefixWord ++ tailWord_1520959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520959).length < 2 ^ (prefixWord ++ tailWord_1520959).sum := by decide
  have hdescent : baseEnd_1520959 < baseStart_1520959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520976 : List Nat := [2, 1, 1, 1, 1, 5, 5, 1, 1, 3, 2]
def baseStart_1520976 : Nat := 118140960795 + 1520976 * 2 ^ 59
def prefixEnd_1520976 : Nat := 4983230072969 + 3 ^ 40 * 1520976 * 2
def baseEnd_1520976 : Nat := 780991751952946408105165

theorem tailTrace_1520976 : CollatzResearch.WordTrace tailWord_1520976 prefixEnd_1520976 780991751952946408105165 := by
  unfold tailWord_1520976
  simp only [CollatzResearch.WordTrace]
  refine ⟨27737276068885594432599391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36983034758514125910132521 27737276068885594432599391)
  ·
    refine ⟨41605914103328391648899087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27737276068885594432599391 41605914103328391648899087)
    ·
      refine ⟨62408871154992587473348631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41605914103328391648899087 62408871154992587473348631)
      ·
        refine ⟨93613306732488881210022947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62408871154992587473348631 93613306732488881210022947)
        ·
          refine ⟨140419960098733321815034421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93613306732488881210022947 140419960098733321815034421)
          ·
            refine ⟨13164371259256248920159477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140419960098733321815034421 13164371259256248920159477)
            ·
              refine ⟨1234159805555273336264951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13164371259256248920159477 1234159805555273336264951)
              ·
                refine ⟨1851239708332910004397427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1234159805555273336264951 1851239708332910004397427)
                ·
                  refine ⟨2776859562499365006596141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1851239708332910004397427 2776859562499365006596141)
                  ·
                    refine ⟨1041322335937261877473553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2776859562499365006596141 1041322335937261877473553)
                    ·
                      refine ⟨780991751952946408105165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1041322335937261877473553 780991751952946408105165)
                      ·
                        rfl

theorem cell23_1520976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 1, 3, 2].length) (baseStart_1520976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520976 prefixEnd_1520976 := by exact prefixLift 1520976
  have htrace : WordTrace (prefixWord ++ tailWord_1520976) baseStart_1520976 baseEnd_1520976 := by
    simpa [prefixWord, tailWord_1520976, baseEnd_1520976] using wordTrace_append hprefix tailTrace_1520976
  have hstable : (prefixWord ++ tailWord_1520976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520976).length < 2 ^ (prefixWord ++ tailWord_1520976).sum := by decide
  have hdescent : baseEnd_1520976 < baseStart_1520976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520992 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 3]
def baseStart_1520992 : Nat := 118140960795 + 1520992 * 2 ^ 59
def prefixEnd_1520992 : Nat := 4983230072969 + 3 ^ 40 * 1520992 * 2
def baseEnd_1520992 : Nat := 780999967643418345505091

theorem tailTrace_1520992 : CollatzResearch.WordTrace tailWord_1520992 prefixEnd_1520992 780999967643418345505091 := by
  unfold tailWord_1520992
  simp only [CollatzResearch.WordTrace]
  refine ⟨27737567852856611798890615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36983423803808815731854153 27737567852856611798890615)
  ·
    refine ⟨41606351779284917698335923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27737567852856611798890615 41606351779284917698335923)
    ·
      refine ⟨62409527668927376547503885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41606351779284917698335923 62409527668927376547503885)
      ·
        refine ⟨23403572875847766205313957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62409527668927376547503885 23403572875847766205313957)
        ·
          refine ⟨4388169914221456163496367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23403572875847766205313957 4388169914221456163496367)
          ·
            refine ⟨6582254871332184245244551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4388169914221456163496367 6582254871332184245244551)
            ·
              refine ⟨9873382306998276367866827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6582254871332184245244551 9873382306998276367866827)
              ·
                refine ⟨14810073460497414551800241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9873382306998276367866827 14810073460497414551800241)
                ·
                  refine ⟨11107555095373060913850181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14810073460497414551800241 11107555095373060913850181)
                  ·
                    refine ⟨2082666580382448921346909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11107555095373060913850181 2082666580382448921346909)
                    ·
                      refine ⟨780999967643418345505091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2082666580382448921346909 780999967643418345505091)
                      ·
                        rfl

theorem cell23_1520992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_1520992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520992 prefixEnd_1520992 := by exact prefixLift 1520992
  have htrace : WordTrace (prefixWord ++ tailWord_1520992) baseStart_1520992 baseEnd_1520992 := by
    simpa [prefixWord, tailWord_1520992, baseEnd_1520992] using wordTrace_append hprefix tailTrace_1520992
  have hstable : (prefixWord ++ tailWord_1520992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520992).length < 2 ^ (prefixWord ++ tailWord_1520992).sum := by decide
  have hdescent : baseEnd_1520992 < baseStart_1520992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521072 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 5, 4]
def baseStart_1521072 : Nat := 118140960795 + 1521072 * 2 ^ 59
def prefixEnd_1521072 : Nat := 4983230072969 + 3 ^ 40 * 1521072 * 2
def baseEnd_1521072 : Nat := 260347015365259344168241

theorem tailTrace_1521072 : CollatzResearch.WordTrace tailWord_1521072 prefixEnd_1521072 260347015365259344168241 := by
  unfold tailWord_1521072
  simp only [CollatzResearch.WordTrace]
  refine ⟨27739026772711698630346735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36985369030282264840462313 27739026772711698630346735)
  ·
    refine ⟨41608540159067547945520103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27739026772711698630346735 41608540159067547945520103)
    ·
      refine ⟨62412810238601321918280155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41608540159067547945520103 62412810238601321918280155)
      ·
        refine ⟨93619215357901982877420233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62412810238601321918280155 93619215357901982877420233)
        ·
          refine ⟨70214411518426487158065175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93619215357901982877420233 70214411518426487158065175)
          ·
            refine ⟨105321617277639730737097763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70214411518426487158065175 105321617277639730737097763)
            ·
              refine ⟨157982425916459596105646645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105321617277639730737097763 157982425916459596105646645)
              ·
                refine ⟨14810852429668087134904373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157982425916459596105646645 14810852429668087134904373)
                ·
                  refine ⟨1388517415281383168897285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14810852429668087134904373 1388517415281383168897285)
                  ·
                    refine ⟨260347015365259344168241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1388517415281383168897285 260347015365259344168241)
                    ·
                      rfl

theorem cell23_1521072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 5, 4].length) (baseStart_1521072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521072 prefixEnd_1521072 := by exact prefixLift 1521072
  have htrace : WordTrace (prefixWord ++ tailWord_1521072) baseStart_1521072 baseEnd_1521072 := by
    simpa [prefixWord, tailWord_1521072, baseEnd_1521072] using wordTrace_append hprefix tailTrace_1521072
  have hstable : (prefixWord ++ tailWord_1521072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521072).length < 2 ^ (prefixWord ++ tailWord_1521072).sum := by decide
  have hdescent : baseEnd_1521072 < baseStart_1521072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521102 : List Nat := [4, 1, 1, 1, 2, 1, 4, 1, 8]
def baseStart_1521102 : Nat := 118140960795 + 1521102 * 2 ^ 59
def prefixEnd_1521102 : Nat := 4983230072969 + 3 ^ 40 * 1521102 * 2
def baseEnd_1521102 : Nat := 86784050057268101681065

theorem tailTrace_1521102 : CollatzResearch.WordTrace tailWord_1521102 prefixEnd_1521102 86784050057268101681065 := by
  unfold tailWord_1521102
  simp only [CollatzResearch.WordTrace]
  refine ⟨6934893466914339048035695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36986098490209808256190373 6934893466914339048035695)
  ·
    refine ⟨10402340200371508572053543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6934893466914339048035695 10402340200371508572053543)
    ·
      refine ⟨15603510300557262858080315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10402340200371508572053543 15603510300557262858080315)
      ·
        refine ⟨23405265450835894287120473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15603510300557262858080315 23405265450835894287120473)
        ·
          refine ⟨17553949088126920715340355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23405265450835894287120473 17553949088126920715340355)
          ·
            refine ⟨26330923632190381073010533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17553949088126920715340355 26330923632190381073010533)
            ·
              refine ⟨4937048181035696451189475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26330923632190381073010533 4937048181035696451189475)
              ·
                refine ⟨7405572271553544676784213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4937048181035696451189475 7405572271553544676784213)
                ·
                  refine ⟨86784050057268101681065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7405572271553544676784213 86784050057268101681065)
                  ·
                    rfl

theorem cell23_1521102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 8].length) (baseStart_1521102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521102 prefixEnd_1521102 := by exact prefixLift 1521102
  have htrace : WordTrace (prefixWord ++ tailWord_1521102) baseStart_1521102 baseEnd_1521102 := by
    simpa [prefixWord, tailWord_1521102, baseEnd_1521102] using wordTrace_append hprefix tailTrace_1521102
  have hstable : (prefixWord ++ tailWord_1521102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521102).length < 2 ^ (prefixWord ++ tailWord_1521102).sum := by decide
  have hdescent : baseEnd_1521102 < baseStart_1521102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521133 : List Nat := [1, 5, 1, 3, 2, 1, 2, 1, 2, 2, 3]
def baseStart_1521133 : Nat := 118140960795 + 1521133 * 2 ^ 59
def prefixEnd_1521133 : Nat := 4983230072969 + 3 ^ 40 * 1521133 * 2
def baseEnd_1521133 : Nat := 781072368415702293841943

theorem tailTrace_1521133 : CollatzResearch.WordTrace tailWord_1521133 prefixEnd_1521133 781072368415702293841943 := by
  unfold tailWord_1521133
  simp only [CollatzResearch.WordTrace]
  refine ⟨55480278398202404678664053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36986852265468269785776035 55480278398202404678664053)
  ·
    refine ⟨5201276099831475438624755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55480278398202404678664053 5201276099831475438624755)
    ·
      refine ⟨7801914149747213157937133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5201276099831475438624755 7801914149747213157937133)
      ·
        refine ⟨2925717806155204934226425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7801914149747213157937133 2925717806155204934226425)
        ·
          refine ⟨2194288354616403700669819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2925717806155204934226425 2194288354616403700669819)
          ·
            refine ⟨3291432531924605551004729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2194288354616403700669819 3291432531924605551004729)
            ·
              refine ⟨2468574398943454163253547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3291432531924605551004729 2468574398943454163253547)
              ·
                refine ⟨3702861598415181244880321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2468574398943454163253547 3702861598415181244880321)
                ·
                  refine ⟨2777146198811385933660241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3702861598415181244880321 2777146198811385933660241)
                  ·
                    refine ⟨2082859649108539450245181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2777146198811385933660241 2082859649108539450245181)
                    ·
                      refine ⟨781072368415702293841943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2082859649108539450245181 781072368415702293841943)
                      ·
                        rfl

theorem cell23_1521133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_1521133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521133 prefixEnd_1521133 := by exact prefixLift 1521133
  have htrace : WordTrace (prefixWord ++ tailWord_1521133) baseStart_1521133 baseEnd_1521133 := by
    simpa [prefixWord, tailWord_1521133, baseEnd_1521133] using wordTrace_append hprefix tailTrace_1521133
  have hstable : (prefixWord ++ tailWord_1521133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521133).length < 2 ^ (prefixWord ++ tailWord_1521133).sum := by decide
  have hdescent : baseEnd_1521133 < baseStart_1521133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521203 : List Nat := [1, 1, 1, 2, 4, 5, 2, 1, 1, 1, 4]
def baseStart_1521203 : Nat := 118140960795 + 1521203 * 2 ^ 59
def prefixEnd_1521203 : Nat := 4983230072969 + 3 ^ 40 * 1521203 * 2
def baseEnd_1521203 : Nat := 781108312061517019966621

theorem tailTrace_1521203 : CollatzResearch.WordTrace tailWord_1521203 prefixEnd_1521203 781108312061517019966621 := by
  unfold tailWord_1521203
  simp only [CollatzResearch.WordTrace]
  refine ⟨55482831507948806633712263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36988554338632537755808175 55482831507948806633712263)
  ·
    refine ⟨83224247261923209950568395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55482831507948806633712263 83224247261923209950568395)
    ·
      refine ⟨124836370892884814925852593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83224247261923209950568395 124836370892884814925852593)
      ·
        refine ⟨93627278169663611194389445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124836370892884814925852593 93627278169663611194389445)
        ·
          refine ⟨17555114656811927098948021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93627278169663611194389445 17555114656811927098948021)
          ·
            refine ⟨1645791999076118165526377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17555114656811927098948021 1645791999076118165526377)
            ·
              refine ⟨1234343999307088624144783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1645791999076118165526377 1234343999307088624144783)
              ·
                refine ⟨1851515998960632936217175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1234343999307088624144783 1851515998960632936217175)
                ·
                  refine ⟨2777273998440949404325763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1851515998960632936217175 2777273998440949404325763)
                  ·
                    refine ⟨4165910997661424106488645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2777273998440949404325763 4165910997661424106488645)
                    ·
                      refine ⟨781108312061517019966621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4165910997661424106488645 781108312061517019966621)
                      ·
                        rfl

theorem cell23_1521203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 1, 1, 4].length) (baseStart_1521203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521203 prefixEnd_1521203 := by exact prefixLift 1521203
  have htrace : WordTrace (prefixWord ++ tailWord_1521203) baseStart_1521203 baseEnd_1521203 := by
    simpa [prefixWord, tailWord_1521203, baseEnd_1521203] using wordTrace_append hprefix tailTrace_1521203
  have hstable : (prefixWord ++ tailWord_1521203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521203).length < 2 ^ (prefixWord ++ tailWord_1521203).sum := by decide
  have hdescent : baseEnd_1521203 < baseStart_1521203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521289 : List Nat := [1, 2, 1, 1, 4, 1, 2, 3, 2, 2, 4]
def baseStart_1521289 : Nat := 118140960795 + 1521289 * 2 ^ 59
def prefixEnd_1521289 : Nat := 4983230072969 + 3 ^ 40 * 1521289 * 2
def baseEnd_1521289 : Nat := 781152471397803683491225

theorem tailTrace_1521289 : CollatzResearch.WordTrace tailWord_1521289 prefixEnd_1521289 781152471397803683491225 := by
  unfold tailWord_1521289
  simp only [CollatzResearch.WordTrace]
  refine ⟨55485968185637243321342921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36990645457091495547561947 55485968185637243321342921)
  ·
    refine ⟨41614476139227932491007191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55485968185637243321342921 41614476139227932491007191)
    ·
      refine ⟨62421714208841898736510787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41614476139227932491007191 62421714208841898736510787)
      ·
        refine ⟨93632571313262848104766181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62421714208841898736510787 93632571313262848104766181)
        ·
          refine ⟨17556107121236784019643659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93632571313262848104766181 17556107121236784019643659)
          ·
            refine ⟨26334160681855176029465489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17556107121236784019643659 26334160681855176029465489)
            ·
              refine ⟨19750620511391382022099117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26334160681855176029465489 19750620511391382022099117)
              ·
                refine ⟨7406482691771768258287169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19750620511391382022099117 7406482691771768258287169)
                ·
                  refine ⟨5554862018828826193715377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7406482691771768258287169 5554862018828826193715377)
                  ·
                    refine ⟨4166146514121619645286533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5554862018828826193715377 4166146514121619645286533)
                    ·
                      refine ⟨781152471397803683491225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4166146514121619645286533 781152471397803683491225)
                      ·
                        rfl

theorem cell23_1521289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 2, 4].length) (baseStart_1521289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521289 prefixEnd_1521289 := by exact prefixLift 1521289
  have htrace : WordTrace (prefixWord ++ tailWord_1521289) baseStart_1521289 baseEnd_1521289 := by
    simpa [prefixWord, tailWord_1521289, baseEnd_1521289] using wordTrace_append hprefix tailTrace_1521289
  have hstable : (prefixWord ++ tailWord_1521289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521289).length < 2 ^ (prefixWord ++ tailWord_1521289).sum := by decide
  have hdescent : baseEnd_1521289 < baseStart_1521289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521310 : List Nat := [4, 3, 1, 1, 1, 3, 1, 2, 1, 4, 2]
def baseStart_1521310 : Nat := 118140960795 + 1521310 * 2 ^ 59
def prefixEnd_1521310 : Nat := 4983230072969 + 3 ^ 40 * 1521310 * 2
def baseEnd_1521310 : Nat := 781163254491548101328629

theorem tailTrace_1521310 : CollatzResearch.WordTrace tailWord_1521310 prefixEnd_1521310 781163254491548101328629 := by
  unfold tailWord_1521310
  simp only [CollatzResearch.WordTrace]
  refine ⟨6935841764820145488482173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36991156079040775938571589 6935841764820145488482173)
  ·
    refine ⟨2600940661807554558180815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6935841764820145488482173 2600940661807554558180815)
    ·
      refine ⟨3901410992711331837271223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2600940661807554558180815 3901410992711331837271223)
      ·
        refine ⟨5852116489066997755906835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3901410992711331837271223 5852116489066997755906835)
        ·
          refine ⟨8778174733600496633860253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5852116489066997755906835 8778174733600496633860253)
          ·
            refine ⟨3291815525100186237697595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8778174733600496633860253 3291815525100186237697595)
            ·
              refine ⟨4937723287650279356546393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3291815525100186237697595 4937723287650279356546393)
              ·
                refine ⟨3703292465737709517409795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4937723287650279356546393 3703292465737709517409795)
                ·
                  refine ⟨5554938698606564276114693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3703292465737709517409795 5554938698606564276114693)
                  ·
                    refine ⟨1041551005988730801771505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5554938698606564276114693 1041551005988730801771505)
                    ·
                      refine ⟨781163254491548101328629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1041551005988730801771505 781163254491548101328629)
                      ·
                        rfl

theorem cell23_1521310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_1521310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521310 prefixEnd_1521310 := by exact prefixLift 1521310
  have htrace : WordTrace (prefixWord ++ tailWord_1521310) baseStart_1521310 baseEnd_1521310 := by
    simpa [prefixWord, tailWord_1521310, baseEnd_1521310] using wordTrace_append hprefix tailTrace_1521310
  have hstable : (prefixWord ++ tailWord_1521310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521310).length < 2 ^ (prefixWord ++ tailWord_1521310).sum := by decide
  have hdescent : baseEnd_1521310 < baseStart_1521310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521314 : List Nat := [3, 3, 1, 4, 1, 1, 3, 1, 1, 3, 2]
def baseStart_1521314 : Nat := 118140960795 + 1521314 * 2 ^ 59
def prefixEnd_1521314 : Nat := 4983230072969 + 3 ^ 40 * 1521314 * 2
def baseEnd_1521314 : Nat := 781165308414166085678611

theorem tailTrace_1521314 : CollatzResearch.WordTrace tailWord_1521314 prefixEnd_1521314 781165308414166085678611 := by
  unfold tailWord_1521314
  simp only [CollatzResearch.WordTrace]
  refine ⟨13871720002636668147750749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36991253340364448394001997 13871720002636668147750749)
  ·
    refine ⟨5201895000988750555406531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13871720002636668147750749 5201895000988750555406531)
    ·
      refine ⟨7802842501483125833109797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5201895000988750555406531 7802842501483125833109797)
      ·
        refine ⟨1463032969028086093708087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7802842501483125833109797 1463032969028086093708087)
        ·
          refine ⟨2194549453542129140562131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1463032969028086093708087 2194549453542129140562131)
          ·
            refine ⟨3291824180313193710843197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2194549453542129140562131 3291824180313193710843197)
            ·
              refine ⟨1234434067617447641566199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3291824180313193710843197 1234434067617447641566199)
              ·
                refine ⟨1851651101426171462349299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1234434067617447641566199 1851651101426171462349299)
                ·
                  refine ⟨2777476652139257193523949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1851651101426171462349299 2777476652139257193523949)
                  ·
                    refine ⟨1041553744552221447571481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2777476652139257193523949 1041553744552221447571481)
                    ·
                      refine ⟨781165308414166085678611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1041553744552221447571481 781165308414166085678611)
                      ·
                        rfl

theorem cell23_1521314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_1521314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521314 prefixEnd_1521314 := by exact prefixLift 1521314
  have htrace : WordTrace (prefixWord ++ tailWord_1521314) baseStart_1521314 baseEnd_1521314 := by
    simpa [prefixWord, tailWord_1521314, baseEnd_1521314] using wordTrace_append hprefix tailTrace_1521314
  have hstable : (prefixWord ++ tailWord_1521314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521314).length < 2 ^ (prefixWord ++ tailWord_1521314).sum := by decide
  have hdescent : baseEnd_1521314 < baseStart_1521314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521349 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 3, 3, 4]
def baseStart_1521349 : Nat := 118140960795 + 1521349 * 2 ^ 59
def prefixEnd_1521349 : Nat := 4983230072969 + 3 ^ 40 * 1521349 * 2
def baseEnd_1521349 : Nat := 781183280237073448740949

theorem tailTrace_1521349 : CollatzResearch.WordTrace tailWord_1521349 prefixEnd_1521349 781183280237073448740949 := by
  unfold tailWord_1521349
  simp only [CollatzResearch.WordTrace]
  refine ⟨55488156565419873568527101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36992104376946582379018067 55488156565419873568527101)
  ·
    refine ⟨20808058712032452588197663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55488156565419873568527101 20808058712032452588197663)
    ·
      refine ⟨31212088068048678882296495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20808058712032452588197663 31212088068048678882296495)
      ·
        refine ⟨46818132102073018323444743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31212088068048678882296495 46818132102073018323444743)
        ·
          refine ⟨70227198153109527485167115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46818132102073018323444743 70227198153109527485167115)
          ·
            refine ⟨105340797229664291227750673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70227198153109527485167115 105340797229664291227750673)
            ·
              refine ⟨79005597922248218420813005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105340797229664291227750673 79005597922248218420813005)
              ·
                refine ⟨29627099220843081907804877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79005597922248218420813005 29627099220843081907804877)
                ·
                  refine ⟨11110162207816155715426829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29627099220843081907804877 11110162207816155715426829)
                  ·
                    refine ⟨4166310827931058393285061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11110162207816155715426829 4166310827931058393285061)
                    ·
                      refine ⟨781183280237073448740949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4166310827931058393285061 781183280237073448740949)
                      ·
                        rfl

theorem cell23_1521349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_1521349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521349 prefixEnd_1521349 := by exact prefixLift 1521349
  have htrace : WordTrace (prefixWord ++ tailWord_1521349) baseStart_1521349 baseEnd_1521349 := by
    simpa [prefixWord, tailWord_1521349, baseEnd_1521349] using wordTrace_append hprefix tailTrace_1521349
  have hstable : (prefixWord ++ tailWord_1521349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521349).length < 2 ^ (prefixWord ++ tailWord_1521349).sum := by decide
  have hdescent : baseEnd_1521349 < baseStart_1521349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521350 : List Nat := [6, 1, 2, 1, 1, 2, 1, 2, 7]
def baseStart_1521350 : Nat := 118140960795 + 1521350 * 2 ^ 59
def prefixEnd_1521350 : Nat := 4983230072969 + 3 ^ 40 * 1521350 * 2
def baseEnd_1521350 : Nat := 86798199301969771647605

theorem tailTrace_1521350 : CollatzResearch.WordTrace tailWord_1521350 prefixEnd_1521350 86798199301969771647605 := by
  unfold tailWord_1521350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1734006032450507835603547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36992128692277500492875669 1734006032450507835603547)
  ·
    refine ⟨2601009048675761753405321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1734006032450507835603547 2601009048675761753405321)
    ·
      refine ⟨1950756786506821315053991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2601009048675761753405321 1950756786506821315053991)
      ·
        refine ⟨2926135179760231972580987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1950756786506821315053991 2926135179760231972580987)
        ·
          refine ⟨4389202769640347958871481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2926135179760231972580987 4389202769640347958871481)
          ·
            refine ⟨3291902077230260969153611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4389202769640347958871481 3291902077230260969153611)
            ·
              refine ⟨4937853115845391453730417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3291902077230260969153611 4937853115845391453730417)
              ·
                refine ⟨3703389836884043590297813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4937853115845391453730417 3703389836884043590297813)
                ·
                  refine ⟨86798199301969771647605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3703389836884043590297813 86798199301969771647605)
                  ·
                    rfl

theorem cell23_1521350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_1521350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521350 prefixEnd_1521350 := by exact prefixLift 1521350
  have htrace : WordTrace (prefixWord ++ tailWord_1521350) baseStart_1521350 baseEnd_1521350 := by
    simpa [prefixWord, tailWord_1521350, baseEnd_1521350] using wordTrace_append hprefix tailTrace_1521350
  have hstable : (prefixWord ++ tailWord_1521350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521350).length < 2 ^ (prefixWord ++ tailWord_1521350).sum := by decide
  have hdescent : baseEnd_1521350 < baseStart_1521350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521393 : List Nat := [1, 2, 2, 2, 2, 4, 2, 1, 3, 4]
def baseStart_1521393 : Nat := 118140960795 + 1521393 * 2 ^ 59
def prefixEnd_1521393 : Nat := 4983230072969 + 3 ^ 40 * 1521393 * 2
def baseEnd_1521393 : Nat := 260401957795290425530249

theorem tailTrace_1521393 : CollatzResearch.WordTrace tailWord_1521393 prefixEnd_1521393 260401957795290425530249 := by
  unfold tailWord_1521393
  simp only [CollatzResearch.WordTrace]
  refine ⟨55489761377260469083128833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36993174251506979388752555 55489761377260469083128833)
  ·
    refine ⟨41617321032945351812346625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55489761377260469083128833 41617321032945351812346625)
    ·
      refine ⟨31212990774709013859259969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41617321032945351812346625 31212990774709013859259969)
      ·
        refine ⟨23409743081031760394444977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31212990774709013859259969 23409743081031760394444977)
        ·
          refine ⟨17557307310773820295833733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23409743081031760394444977 17557307310773820295833733)
          ·
            refine ⟨3291995120770091305468825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17557307310773820295833733 3291995120770091305468825)
            ·
              refine ⟨2468996340577568479101619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3291995120770091305468825 2468996340577568479101619)
              ·
                refine ⟨3703494510866352718652429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2468996340577568479101619 3703494510866352718652429)
                ·
                  refine ⟨1388810441574882269494661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3703494510866352718652429 1388810441574882269494661)
                  ·
                    refine ⟨260401957795290425530249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1388810441574882269494661 260401957795290425530249)
                    ·
                      rfl

theorem cell23_1521393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3, 4].length) (baseStart_1521393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521393 prefixEnd_1521393 := by exact prefixLift 1521393
  have htrace : WordTrace (prefixWord ++ tailWord_1521393) baseStart_1521393 baseEnd_1521393 := by
    simpa [prefixWord, tailWord_1521393, baseEnd_1521393] using wordTrace_append hprefix tailTrace_1521393
  have hstable : (prefixWord ++ tailWord_1521393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521393).length < 2 ^ (prefixWord ++ tailWord_1521393).sum := by decide
  have hdescent : baseEnd_1521393 < baseStart_1521393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521416 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 2, 5, 3]
def baseStart_1521416 : Nat := 118140960795 + 1521416 * 2 ^ 59
def prefixEnd_1521416 : Nat := 4983230072969 + 3 ^ 40 * 1521416 * 2
def baseEnd_1521416 : Nat := 781217683440924686603141

theorem tailTrace_1521416 : CollatzResearch.WordTrace tailWord_1521416 prefixEnd_1521416 781217683440924686603141 := by
  unfold tailWord_1521416
  simp only [CollatzResearch.WordTrace]
  refine ⟨27745300128088572005608051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36993733504118096007477401 27745300128088572005608051)
  ·
    refine ⟨41617950192132858008412077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27745300128088572005608051 41617950192132858008412077)
    ·
      refine ⟨15606731322049821753154529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41617950192132858008412077 15606731322049821753154529)
      ·
        refine ⟨11705048491537366314865897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15606731322049821753154529 11705048491537366314865897)
        ·
          refine ⟨8778786368653024736149423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11705048491537366314865897 8778786368653024736149423)
          ·
            refine ⟨13168179552979537104224135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8778786368653024736149423 13168179552979537104224135)
            ·
              refine ⟨19752269329469305656336203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13168179552979537104224135 19752269329469305656336203)
              ·
                refine ⟨29628403994203958484504305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19752269329469305656336203 29628403994203958484504305)
                ·
                  refine ⟨22221302995652968863378229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29628403994203958484504305 22221302995652968863378229)
                  ·
                    refine ⟨2083247155842465830941709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22221302995652968863378229 2083247155842465830941709)
                    ·
                      refine ⟨781217683440924686603141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2083247155842465830941709 781217683440924686603141)
                      ·
                        rfl

theorem cell23_1521416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_1521416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521416 prefixEnd_1521416 := by exact prefixLift 1521416
  have htrace : WordTrace (prefixWord ++ tailWord_1521416) baseStart_1521416 baseEnd_1521416 := by
    simpa [prefixWord, tailWord_1521416, baseEnd_1521416] using wordTrace_append hprefix tailTrace_1521416
  have hstable : (prefixWord ++ tailWord_1521416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521416).length < 2 ^ (prefixWord ++ tailWord_1521416).sum := by decide
  have hdescent : baseEnd_1521416 < baseStart_1521416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521443 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 4, 3, 2]
def baseStart_1521443 : Nat := 118140960795 + 1521443 * 2 ^ 59
def prefixEnd_1521443 : Nat := 4983230072969 + 3 ^ 40 * 1521443 * 2
def baseEnd_1521443 : Nat := 781231547418596080965517

theorem tailTrace_1521443 : CollatzResearch.WordTrace tailWord_1521443 prefixEnd_1521443 781231547418596080965517 := by
  unfold tailWord_1521443
  simp only [CollatzResearch.WordTrace]
  refine ⟨55491585027079327622448983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36994390018052885081632655 55491585027079327622448983)
  ·
    refine ⟨83237377540618991433673475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55491585027079327622448983 83237377540618991433673475)
    ·
      refine ⟨124856066310928487150510213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83237377540618991433673475 124856066310928487150510213)
      ·
        refine ⟨23410512433299091340720665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124856066310928487150510213 23410512433299091340720665)
        ·
          refine ⟨17557884324974318505540499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23410512433299091340720665 17557884324974318505540499)
          ·
            refine ⟨26336826487461477758310749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17557884324974318505540499 26336826487461477758310749)
            ·
              refine ⟨9876309932798054159366531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26336826487461477758310749 9876309932798054159366531)
              ·
                refine ⟨14814464899197081239049797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9876309932798054159366531 14814464899197081239049797)
                ·
                  refine ⟨2777712168599452732321837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14814464899197081239049797 2777712168599452732321837)
                  ·
                    refine ⟨1041642063224794774620689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2777712168599452732321837 1041642063224794774620689)
                    ·
                      refine ⟨781231547418596080965517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1041642063224794774620689 781231547418596080965517)
                      ·
                        rfl

theorem cell23_1521443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 3, 2].length) (baseStart_1521443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521443 prefixEnd_1521443 := by exact prefixLift 1521443
  have htrace : WordTrace (prefixWord ++ tailWord_1521443) baseStart_1521443 baseEnd_1521443 := by
    simpa [prefixWord, tailWord_1521443, baseEnd_1521443] using wordTrace_append hprefix tailTrace_1521443
  have hstable : (prefixWord ++ tailWord_1521443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521443).length < 2 ^ (prefixWord ++ tailWord_1521443).sum := by decide
  have hdescent : baseEnd_1521443 < baseStart_1521443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521449 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 2, 10]
def baseStart_1521449 : Nat := 118140960795 + 1521449 * 2 ^ 59
def prefixEnd_1521449 : Nat := 4983230072969 + 3 ^ 40 * 1521449 * 2
def baseEnd_1521449 : Nat := 260411542767507685830163

theorem tailTrace_1521449 : CollatzResearch.WordTrace tailWord_1521449 prefixEnd_1521449 260411542767507685830163 := by
  unfold tailWord_1521449
  simp only [CollatzResearch.WordTrace]
  refine ⟨55491803865057590647167401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36994535910038393764778267 55491803865057590647167401)
  ·
    refine ⟨41618852898793192985375551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55491803865057590647167401 41618852898793192985375551)
    ·
      refine ⟨62428279348189789478063327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41618852898793192985375551 62428279348189789478063327)
      ·
        refine ⟨93642419022284684217094991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62428279348189789478063327 93642419022284684217094991)
        ·
          refine ⟨140463628533427026325642487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93642419022284684217094991 140463628533427026325642487)
          ·
            refine ⟨210695442800140539488463731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140463628533427026325642487 210695442800140539488463731)
            ·
              refine ⟨316043164200210809232695597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210695442800140539488463731 316043164200210809232695597)
              ·
                refine ⟨118516186575079053462260849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 316043164200210809232695597 118516186575079053462260849)
                ·
                  refine ⟨88887139931309290096695637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118516186575079053462260849 88887139931309290096695637)
                  ·
                    refine ⟨260411542767507685830163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 88887139931309290096695637 260411542767507685830163)
                    ·
                      rfl

theorem cell23_1521449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 10].length) (baseStart_1521449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521449 prefixEnd_1521449 := by exact prefixLift 1521449
  have htrace : WordTrace (prefixWord ++ tailWord_1521449) baseStart_1521449 baseEnd_1521449 := by
    simpa [prefixWord, tailWord_1521449, baseEnd_1521449] using wordTrace_append hprefix tailTrace_1521449
  have hstable : (prefixWord ++ tailWord_1521449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521449).length < 2 ^ (prefixWord ++ tailWord_1521449).sum := by decide
  have hdescent : baseEnd_1521449 < baseStart_1521449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521470 : List Nat := [4, 2, 1, 2, 2, 1, 3, 2, 1, 5]
def baseStart_1521470 : Nat := 118140960795 + 1521470 * 2 ^ 59
def prefixEnd_1521470 : Nat := 4983230072969 + 3 ^ 40 * 1521470 * 2
def baseEnd_1521470 : Nat := 260415137132089158442631

theorem tailTrace_1521470 : CollatzResearch.WordTrace tailWord_1521470 prefixEnd_1521470 260415137132089158442631 := by
  unfold tailWord_1521470
  simp only [CollatzResearch.WordTrace]
  refine ⟨6936571224747688904210233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36995046531987674155787909 6936571224747688904210233)
  ·
    refine ⟨5202428418560766678157675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6936571224747688904210233 5202428418560766678157675)
    ·
      refine ⟨7803642627841150017236513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5202428418560766678157675 7803642627841150017236513)
      ·
        refine ⟨5852731970880862512927385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7803642627841150017236513 5852731970880862512927385)
        ·
          refine ⟨4389548978160646884695539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5852731970880862512927385 4389548978160646884695539)
          ·
            refine ⟨6584323467240970327043309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4389548978160646884695539 6584323467240970327043309)
            ·
              refine ⟨2469121300215363872641241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6584323467240970327043309 2469121300215363872641241)
              ·
                refine ⟨1851840975161522904480931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2469121300215363872641241 1851840975161522904480931)
                ·
                  refine ⟨2777761462742284356721397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1851840975161522904480931 2777761462742284356721397)
                  ·
                    refine ⟨260415137132089158442631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2777761462742284356721397 260415137132089158442631)
                    ·
                      rfl

theorem cell23_1521470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_1521470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521470 prefixEnd_1521470 := by exact prefixLift 1521470
  have htrace : WordTrace (prefixWord ++ tailWord_1521470) baseStart_1521470 baseEnd_1521470 := by
    simpa [prefixWord, tailWord_1521470, baseEnd_1521470] using wordTrace_append hprefix tailTrace_1521470
  have hstable : (prefixWord ++ tailWord_1521470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521470).length < 2 ^ (prefixWord ++ tailWord_1521470).sum := by decide
  have hdescent : baseEnd_1521470 < baseStart_1521470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521493 : List Nat := [1, 3, 2, 2, 2, 2, 3, 1, 1, 1, 5]
def baseStart_1521493 : Nat := 118140960795 + 1521493 * 2 ^ 59
def prefixEnd_1521493 : Nat := 4983230072969 + 3 ^ 40 * 1521493 * 2
def baseEnd_1521493 : Nat := 781257221451320885340287

theorem tailTrace_1521493 : CollatzResearch.WordTrace tailWord_1521493 prefixEnd_1521493 781257221451320885340287 := by
  unfold tailWord_1521493
  simp only [CollatzResearch.WordTrace]
  refine ⟨55493408676898186161769133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36995605784598790774512755 55493408676898186161769133)
  ·
    refine ⟨20810028253836819810663425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55493408676898186161769133 20810028253836819810663425)
    ·
      refine ⟨15607521190377614857997569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20810028253836819810663425 15607521190377614857997569)
      ·
        refine ⟨11705640892783211143498177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15607521190377614857997569 11705640892783211143498177)
        ·
          refine ⟨8779230669587408357623633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11705640892783211143498177 8779230669587408357623633)
          ·
            refine ⟨6584423002190556268217725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8779230669587408357623633 6584423002190556268217725)
            ·
              refine ⟨2469158625821458600581647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6584423002190556268217725 2469158625821458600581647)
              ·
                refine ⟨3703737938732187900872471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2469158625821458600581647 3703737938732187900872471)
                ·
                  refine ⟨5555606908098281851308707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3703737938732187900872471 5555606908098281851308707)
                  ·
                    refine ⟨8333410362147422776963061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5555606908098281851308707 8333410362147422776963061)
                    ·
                      refine ⟨781257221451320885340287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8333410362147422776963061 781257221451320885340287)
                      ·
                        rfl

theorem cell23_1521493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_1521493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521493 prefixEnd_1521493 := by exact prefixLift 1521493
  have htrace : WordTrace (prefixWord ++ tailWord_1521493) baseStart_1521493 baseEnd_1521493 := by
    simpa [prefixWord, tailWord_1521493, baseEnd_1521493] using wordTrace_append hprefix tailTrace_1521493
  have hstable : (prefixWord ++ tailWord_1521493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521493).length < 2 ^ (prefixWord ++ tailWord_1521493).sum := by decide
  have hdescent : baseEnd_1521493 < baseStart_1521493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521523 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 6, 1, 3]
def baseStart_1521523 : Nat := 118140960795 + 1521523 * 2 ^ 59
def prefixEnd_1521523 : Nat := 4983230072969 + 3 ^ 40 * 1521523 * 2
def baseEnd_1521523 : Nat := 781272625870955767965149

theorem tailTrace_1521523 : CollatzResearch.WordTrace tailWord_1521523 prefixEnd_1521523 781272625870955767965149 := by
  unfold tailWord_1521523
  simp only [CollatzResearch.WordTrace]
  refine ⟨55494502866789501285361223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36996335244526334190240815 55494502866789501285361223)
  ·
    refine ⟨83241754300184251928041835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55494502866789501285361223 83241754300184251928041835)
    ·
      refine ⟨124862631450276377892062753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83241754300184251928041835 124862631450276377892062753)
      ·
        refine ⟨93646973587707283419047065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124862631450276377892062753 93646973587707283419047065)
        ·
          refine ⟨70235230190780462564285299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93646973587707283419047065 70235230190780462564285299)
          ·
            refine ⟨105352845286170693846427949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70235230190780462564285299 105352845286170693846427949)
            ·
              refine ⟨39507316982314010192410481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105352845286170693846427949 39507316982314010192410481)
              ·
                refine ⟨29630487736735507644307861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39507316982314010192410481 29630487736735507644307861)
                ·
                  refine ⟨1388929112659476920826931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29630487736735507644307861 1388929112659476920826931)
                  ·
                    refine ⟨2083393668989215381240397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1388929112659476920826931 2083393668989215381240397)
                    ·
                      refine ⟨781272625870955767965149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2083393668989215381240397 781272625870955767965149)
                      ·
                        rfl

theorem cell23_1521523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6, 1, 3].length) (baseStart_1521523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521523 prefixEnd_1521523 := by exact prefixLift 1521523
  have htrace : WordTrace (prefixWord ++ tailWord_1521523) baseStart_1521523 baseEnd_1521523 := by
    simpa [prefixWord, tailWord_1521523, baseEnd_1521523] using wordTrace_append hprefix tailTrace_1521523
  have hstable : (prefixWord ++ tailWord_1521523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521523).length < 2 ^ (prefixWord ++ tailWord_1521523).sum := by decide
  have hdescent : baseEnd_1521523 < baseStart_1521523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521536 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 5]
def baseStart_1521536 : Nat := 118140960795 + 1521536 * 2 ^ 59
def prefixEnd_1521536 : Nat := 4983230072969 + 3 ^ 40 * 1521536 * 2
def baseEnd_1521536 : Nat := 781279301119464217102589

theorem tailTrace_1521536 : CollatzResearch.WordTrace tailWord_1521536 prefixEnd_1521536 781279301119464217102589 := by
  unfold tailWord_1521536
  simp only [CollatzResearch.WordTrace]
  refine ⟨27747488507871202252792231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36996651343828269670389641 27747488507871202252792231)
  ·
    refine ⟨41621232761806803379188347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27747488507871202252792231 41621232761806803379188347)
    ·
      refine ⟨62431849142710205068782521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41621232761806803379188347 62431849142710205068782521)
      ·
        refine ⟨46823886857032653801586891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62431849142710205068782521 46823886857032653801586891)
        ·
          refine ⟨70235830285548980702380337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46823886857032653801586891 70235830285548980702380337)
          ·
            refine ⟨52676872714161735526785253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70235830285548980702380337 52676872714161735526785253)
            ·
              refine ⟨9876913633905325411272235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52676872714161735526785253 9876913633905325411272235)
              ·
                refine ⟨14815370450857988116908353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9876913633905325411272235 14815370450857988116908353)
                ·
                  refine ⟨11111527838143491087681265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14815370450857988116908353 11111527838143491087681265)
                  ·
                    refine ⟨8333645878607618315760949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11111527838143491087681265 8333645878607618315760949)
                    ·
                      refine ⟨781279301119464217102589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8333645878607618315760949 781279301119464217102589)
                      ·
                        rfl

theorem cell23_1521536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_1521536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521536 prefixEnd_1521536 := by exact prefixLift 1521536
  have htrace : WordTrace (prefixWord ++ tailWord_1521536) baseStart_1521536 baseEnd_1521536 := by
    simpa [prefixWord, tailWord_1521536, baseEnd_1521536] using wordTrace_append hprefix tailTrace_1521536
  have hstable : (prefixWord ++ tailWord_1521536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521536).length < 2 ^ (prefixWord ++ tailWord_1521536).sum := by decide
  have hdescent : baseEnd_1521536 < baseStart_1521536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521544 : List Nat := [2, 1, 3, 3, 3, 2, 2, 1, 1, 2, 3]
def baseStart_1521544 : Nat := 118140960795 + 1521544 * 2 ^ 59
def prefixEnd_1521544 : Nat := 4983230072969 + 3 ^ 40 * 1521544 * 2
def baseEnd_1521544 : Nat := 781283408964700185802553

theorem tailTrace_1521544 : CollatzResearch.WordTrace tailWord_1521544 prefixEnd_1521544 781283408964700185802553 := by
  unfold tailWord_1521544
  simp only [CollatzResearch.WordTrace]
  refine ⟨27747634399856710935937843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36996845866475614581250457 27747634399856710935937843)
  ·
    refine ⟨41621451599785066403906765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27747634399856710935937843 41621451599785066403906765)
    ·
      refine ⟨15608044349919399901465037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41621451599785066403906765 15608044349919399901465037)
      ·
        refine ⟨5853016631219774963049389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15608044349919399901465037 5853016631219774963049389)
        ·
          refine ⟨2194881236707415611143521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5853016631219774963049389 2194881236707415611143521)
          ·
            refine ⟨1646160927530561708357641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2194881236707415611143521 1646160927530561708357641)
            ·
              refine ⟨1234620695647921281268231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1646160927530561708357641 1234620695647921281268231)
              ·
                refine ⟨1851931043471881921902347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1234620695647921281268231 1851931043471881921902347)
                ·
                  refine ⟨2777896565207822882853521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1851931043471881921902347 2777896565207822882853521)
                  ·
                    refine ⟨2083422423905867162140141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2777896565207822882853521 2083422423905867162140141)
                    ·
                      refine ⟨781283408964700185802553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2083422423905867162140141 781283408964700185802553)
                      ·
                        rfl

theorem cell23_1521544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_1521544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521544 prefixEnd_1521544 := by exact prefixLift 1521544
  have htrace : WordTrace (prefixWord ++ tailWord_1521544) baseStart_1521544 baseEnd_1521544 := by
    simpa [prefixWord, tailWord_1521544, baseEnd_1521544] using wordTrace_append hprefix tailTrace_1521544
  have hstable : (prefixWord ++ tailWord_1521544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521544).length < 2 ^ (prefixWord ++ tailWord_1521544).sum := by decide
  have hdescent : baseEnd_1521544 < baseStart_1521544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521558 : List Nat := [5, 3, 1, 1, 2, 1, 2, 1, 3, 2, 2]
def baseStart_1521558 : Nat := 118140960795 + 1521558 * 2 ^ 59
def prefixEnd_1521558 : Nat := 4983230072969 + 3 ^ 40 * 1521558 * 2
def baseEnd_1521558 : Nat := 781290597693863131027489

theorem tailTrace_1521558 : CollatzResearch.WordTrace tailWord_1521558 prefixEnd_1521558 781290597693863131027489 := by
  unfold tailWord_1521558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3468486213853918891430333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36997186281108468175256885 3468486213853918891430333)
  ·
    refine ⟨1300682330195219584286375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3468486213853918891430333 1300682330195219584286375)
    ·
      refine ⟨1951023495292829376429563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1300682330195219584286375 1951023495292829376429563)
      ·
        refine ⟨2926535242939244064644345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1951023495292829376429563 2926535242939244064644345)
        ·
          refine ⟨2194901432204433048483259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2926535242939244064644345 2194901432204433048483259)
          ·
            refine ⟨3292352148306649572724889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2194901432204433048483259 3292352148306649572724889)
            ·
              refine ⟨2469264111229987179543667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3292352148306649572724889 2469264111229987179543667)
              ·
                refine ⟨3703896166844980769315501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2469264111229987179543667 3703896166844980769315501)
                ·
                  refine ⟨1388961062566867788493313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3703896166844980769315501 1388961062566867788493313)
                  ·
                    refine ⟨1041720796925150841369985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1388961062566867788493313 1041720796925150841369985)
                    ·
                      refine ⟨781290597693863131027489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1041720796925150841369985 781290597693863131027489)
                      ·
                        rfl

theorem cell23_1521558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_1521558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521558 prefixEnd_1521558 := by exact prefixLift 1521558
  have htrace : WordTrace (prefixWord ++ tailWord_1521558) baseStart_1521558 baseEnd_1521558 := by
    simpa [prefixWord, tailWord_1521558, baseEnd_1521558] using wordTrace_append hprefix tailTrace_1521558
  have hstable : (prefixWord ++ tailWord_1521558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521558).length < 2 ^ (prefixWord ++ tailWord_1521558).sum := by decide
  have hdescent : baseEnd_1521558 < baseStart_1521558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521580 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 8, 2, 2]
def baseStart_1521580 : Nat := 118140960795 + 1521580 * 2 ^ 59
def prefixEnd_1521580 : Nat := 4983230072969 + 3 ^ 40 * 1521580 * 2
def baseEnd_1521580 : Nat := 781301894268262044952387

theorem tailTrace_1521580 : CollatzResearch.WordTrace tailWord_1521580 prefixEnd_1521580 781301894268262044952387 := by
  unfold tailWord_1521580
  simp only [CollatzResearch.WordTrace]
  refine ⟨27748290913791500010093097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36997721218388666680124129 27748290913791500010093097)
  ·
    refine ⟨20811218185343625007569823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27748290913791500010093097 20811218185343625007569823)
    ·
      refine ⟨31216827278015437511354735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20811218185343625007569823 31216827278015437511354735)
      ·
        refine ⟨46825240917023156267032103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31216827278015437511354735 46825240917023156267032103)
        ·
          refine ⟨70237861375534734400548155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46825240917023156267032103 70237861375534734400548155)
          ·
            refine ⟨105356792063302101600822233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70237861375534734400548155 105356792063302101600822233)
            ·
              refine ⟨79017594047476576200616675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105356792063302101600822233 79017594047476576200616675)
              ·
                refine ⟨118526391071214864300925013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79017594047476576200616675 118526391071214864300925013)
                ·
                  refine ⟨1388981145365799191026465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 118526391071214864300925013 1388981145365799191026465)
                  ·
                    refine ⟨1041735859024349393269849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1388981145365799191026465 1041735859024349393269849)
                    ·
                      refine ⟨781301894268262044952387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1041735859024349393269849 781301894268262044952387)
                      ·
                        rfl

theorem cell23_1521580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 2, 2].length) (baseStart_1521580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521580 prefixEnd_1521580 := by exact prefixLift 1521580
  have htrace : WordTrace (prefixWord ++ tailWord_1521580) baseStart_1521580 baseEnd_1521580 := by
    simpa [prefixWord, tailWord_1521580, baseEnd_1521580] using wordTrace_append hprefix tailTrace_1521580
  have hstable : (prefixWord ++ tailWord_1521580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521580).length < 2 ^ (prefixWord ++ tailWord_1521580).sum := by decide
  have hdescent : baseEnd_1521580 < baseStart_1521580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521597 : List Nat := [1, 4, 1, 2, 3, 1, 1, 2, 4, 2, 2]
def baseStart_1521597 : Nat := 118140960795 + 1521597 * 2 ^ 59
def prefixEnd_1521597 : Nat := 4983230072969 + 3 ^ 40 * 1521597 * 2
def baseEnd_1521597 : Nat := 781310623439388478439809

theorem tailTrace_1521597 : CollatzResearch.WordTrace tailWord_1521597 prefixEnd_1521597 781310623439388478439809 := by
  unfold tailWord_1521597
  simp only [CollatzResearch.WordTrace]
  refine ⟨55497201868521411923555045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36998134579014274615703363 55497201868521411923555045)
  ·
    refine ⟨10405725350347764735666571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55497201868521411923555045 10405725350347764735666571)
    ·
      refine ⟨15608588025521647103499857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10405725350347764735666571 15608588025521647103499857)
      ·
        refine ⟨11706441019141235327624893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15608588025521647103499857 11706441019141235327624893)
        ·
          refine ⟨4389915382177963247859335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11706441019141235327624893 4389915382177963247859335)
          ·
            refine ⟨6584873073266944871789003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4389915382177963247859335 6584873073266944871789003)
            ·
              refine ⟨9877309609900417307683505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6584873073266944871789003 9877309609900417307683505)
              ·
                refine ⟨7407982207425312980762629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9877309609900417307683505 7407982207425312980762629)
                ·
                  refine ⟨1388996663892246183892993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7407982207425312980762629 1388996663892246183892993)
                  ·
                    refine ⟨1041747497919184637919745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1388996663892246183892993 1041747497919184637919745)
                    ·
                      refine ⟨781310623439388478439809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1041747497919184637919745 781310623439388478439809)
                      ·
                        rfl

theorem cell23_1521597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_1521597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521597 prefixEnd_1521597 := by exact prefixLift 1521597
  have htrace : WordTrace (prefixWord ++ tailWord_1521597) baseStart_1521597 baseEnd_1521597 := by
    simpa [prefixWord, tailWord_1521597, baseEnd_1521597] using wordTrace_append hprefix tailTrace_1521597
  have hstable : (prefixWord ++ tailWord_1521597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521597).length < 2 ^ (prefixWord ++ tailWord_1521597).sum := by decide
  have hdescent : baseEnd_1521597 < baseStart_1521597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521631 : List Nat := [1, 1, 2, 3, 4, 3, 2, 1, 2, 2, 2]
def baseStart_1521631 : Nat := 118140960795 + 1521631 * 2 ^ 59
def prefixEnd_1521631 : Nat := 4983230072969 + 3 ^ 40 * 1521631 * 2
def baseEnd_1521631 : Nat := 781328081781641345414653

theorem tailTrace_1521631 : CollatzResearch.WordTrace tailWord_1521631 prefixEnd_1521631 781328081781641345414653 := by
  unfold tailWord_1521631
  simp only [CollatzResearch.WordTrace]
  refine ⟨55498441950398235730292747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36998961300265490486861831 55498441950398235730292747)
  ·
    refine ⟨83247662925597353595439121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55498441950398235730292747 83247662925597353595439121)
    ·
      refine ⟨62435747194198015196579341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83247662925597353595439121 62435747194198015196579341)
      ·
        refine ⟨23413405197824255698717253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62435747194198015196579341 23413405197824255698717253)
        ·
          refine ⟨4390013474592047943509485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23413405197824255698717253 4390013474592047943509485)
          ·
            refine ⟨1646255052972017978816057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4390013474592047943509485 1646255052972017978816057)
            ·
              refine ⟨1234691289729013484112043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1646255052972017978816057 1234691289729013484112043)
              ·
                refine ⟨1852036934593520226168065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1234691289729013484112043 1852036934593520226168065)
                ·
                  refine ⟨1389027700945140169626049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1852036934593520226168065 1389027700945140169626049)
                  ·
                    refine ⟨1041770775708855127219537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1389027700945140169626049 1041770775708855127219537)
                    ·
                      refine ⟨781328081781641345414653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1041770775708855127219537 781328081781641345414653)
                      ·
                        rfl

theorem cell23_1521631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 2, 2, 2].length) (baseStart_1521631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521631 prefixEnd_1521631 := by exact prefixLift 1521631
  have htrace : WordTrace (prefixWord ++ tailWord_1521631) baseStart_1521631 baseEnd_1521631 := by
    simpa [prefixWord, tailWord_1521631, baseEnd_1521631] using wordTrace_append hprefix tailTrace_1521631
  have hstable : (prefixWord ++ tailWord_1521631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521631).length < 2 ^ (prefixWord ++ tailWord_1521631).sum := by decide
  have hdescent : baseEnd_1521631 < baseStart_1521631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521673 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 5, 4, 3]
def baseStart_1521673 : Nat := 118140960795 + 1521673 * 2 ^ 59
def prefixEnd_1521673 : Nat := 4983230072969 + 3 ^ 40 * 1521673 * 2
def baseEnd_1521673 : Nat := 781349647969130181089459

theorem tailTrace_1521673 : CollatzResearch.WordTrace tailWord_1521673 prefixEnd_1521673 781349647969130181089459 := by
  unfold tailWord_1521673
  simp only [CollatzResearch.WordTrace]
  refine ⟨55499973816246076903321673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36999982544164051268881115 55499973816246076903321673)
  ·
    refine ⟨41624980362184557677491255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55499973816246076903321673 41624980362184557677491255)
    ·
      refine ⟨62437470543276836516236883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41624980362184557677491255 62437470543276836516236883)
      ·
        refine ⟨93656205814915254774355325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62437470543276836516236883 93656205814915254774355325)
        ·
          refine ⟨35121077180593220540383247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93656205814915254774355325 35121077180593220540383247)
          ·
            refine ⟨52681615770889830810574871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35121077180593220540383247 52681615770889830810574871)
            ·
              refine ⟨79022423656334746215862307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52681615770889830810574871 79022423656334746215862307)
              ·
                refine ⟨118533635484502119323793461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79022423656334746215862307 118533635484502119323793461)
                ·
                  refine ⟨11112528326672073686605637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118533635484502119323793461 11112528326672073686605637)
                  ·
                    refine ⟨2083599061251013816238557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11112528326672073686605637 2083599061251013816238557)
                    ·
                      refine ⟨781349647969130181089459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2083599061251013816238557 781349647969130181089459)
                      ·
                        rfl

theorem cell23_1521673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 4, 3].length) (baseStart_1521673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521673 prefixEnd_1521673 := by exact prefixLift 1521673
  have htrace : WordTrace (prefixWord ++ tailWord_1521673) baseStart_1521673 baseEnd_1521673 := by
    simpa [prefixWord, tailWord_1521673, baseEnd_1521673] using wordTrace_append hprefix tailTrace_1521673
  have hstable : (prefixWord ++ tailWord_1521673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521673).length < 2 ^ (prefixWord ++ tailWord_1521673).sum := by decide
  have hdescent : baseEnd_1521673 < baseStart_1521673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521697 : List Nat := [1, 2, 3, 2, 4, 1, 1, 2, 3, 4]
def baseStart_1521697 : Nat := 118140960795 + 1521697 * 2 ^ 59
def prefixEnd_1521697 : Nat := 4983230072969 + 3 ^ 40 * 1521697 * 2
def baseEnd_1521697 : Nat := 260453990501612695729783

theorem tailTrace_1521697 : CollatzResearch.WordTrace tailWord_1521697 prefixEnd_1521697 260453990501612695729783 := by
  unfold tailWord_1521697
  simp only [CollatzResearch.WordTrace]
  refine ⟨55500849168159129002195345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37000566112106086001463563 55500849168159129002195345)
  ·
    refine ⟨41625636876119346751646509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55500849168159129002195345 41625636876119346751646509)
    ·
      refine ⟨15609613828544755031867441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41625636876119346751646509 15609613828544755031867441)
      ·
        refine ⟨11707210371408566273900581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15609613828544755031867441 11707210371408566273900581)
        ·
          refine ⟨2195101944639106176356359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11707210371408566273900581 2195101944639106176356359)
          ·
            refine ⟨3292652916958659264534539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2195101944639106176356359 3292652916958659264534539)
            ·
              refine ⟨4938979375437988896801809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3292652916958659264534539 4938979375437988896801809)
              ·
                refine ⟨3704234531578491672601357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4938979375437988896801809 3704234531578491672601357)
                ·
                  refine ⟨1389087949341934377225509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3704234531578491672601357 1389087949341934377225509)
                  ·
                    refine ⟨260453990501612695729783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1389087949341934377225509 260453990501612695729783)
                    ·
                      rfl

theorem cell23_1521697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_1521697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521697 prefixEnd_1521697 := by exact prefixLift 1521697
  have htrace : WordTrace (prefixWord ++ tailWord_1521697) baseStart_1521697 baseEnd_1521697 := by
    simpa [prefixWord, tailWord_1521697, baseEnd_1521697] using wordTrace_append hprefix tailTrace_1521697
  have hstable : (prefixWord ++ tailWord_1521697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521697).length < 2 ^ (prefixWord ++ tailWord_1521697).sum := by decide
  have hdescent : baseEnd_1521697 < baseStart_1521697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521714 : List Nat := [3, 2, 1, 1, 2, 4, 2, 3, 1, 4]
def baseStart_1521714 : Nat := 118140960795 + 1521714 * 2 ^ 59
def prefixEnd_1521714 : Nat := 4983230072969 + 3 ^ 40 * 1521714 * 2
def baseEnd_1521714 : Nat := 260456900225321506892257

theorem tailTrace_1521714 : CollatzResearch.WordTrace tailWord_1521714 prefixEnd_1521714 260456900225321506892257 := by
  unfold tailWord_1521714
  simp only [CollatzResearch.WordTrace]
  refine ⟨13875367302274385226391049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37000979472731693937042797 13875367302274385226391049)
  ·
    refine ⟨10406525476705788919793287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13875367302274385226391049 10406525476705788919793287)
    ·
      refine ⟨15609788215058683379689931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10406525476705788919793287 15609788215058683379689931)
      ·
        refine ⟨23414682322588025069534897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15609788215058683379689931 23414682322588025069534897)
        ·
          refine ⟨17561011741941018802151173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23414682322588025069534897 17561011741941018802151173)
          ·
            refine ⟨3292689701613941025403345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17561011741941018802151173 3292689701613941025403345)
            ·
              refine ⟨2469517276210455769052509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3292689701613941025403345 2469517276210455769052509)
              ·
                refine ⟨926068978578920913394691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2469517276210455769052509 926068978578920913394691)
                ·
                  refine ⟨1389103467868381370092037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 926068978578920913394691 1389103467868381370092037)
                  ·
                    refine ⟨260456900225321506892257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1389103467868381370092037 260456900225321506892257)
                    ·
                      rfl

theorem cell23_1521714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_1521714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521714 prefixEnd_1521714 := by exact prefixLift 1521714
  have htrace : WordTrace (prefixWord ++ tailWord_1521714) baseStart_1521714 baseEnd_1521714 := by
    simpa [prefixWord, tailWord_1521714, baseEnd_1521714] using wordTrace_append hprefix tailTrace_1521714
  have hstable : (prefixWord ++ tailWord_1521714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521714).length < 2 ^ (prefixWord ++ tailWord_1521714).sum := by decide
  have hdescent : baseEnd_1521714 < baseStart_1521714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521737 : List Nat := [1, 2, 1, 1, 2, 2, 6, 1, 3, 1, 3]
def baseStart_1521737 : Nat := 118140960795 + 1521737 * 2 ^ 59
def prefixEnd_1521737 : Nat := 4983230072969 + 3 ^ 40 * 1521737 * 2
def baseEnd_1521737 : Nat := 781382510731017930689165

theorem tailTrace_1521737 : CollatzResearch.WordTrace tailWord_1521737 prefixEnd_1521737 781382510731017930689165 := by
  unfold tailWord_1521737
  simp only [CollatzResearch.WordTrace]
  refine ⟨55502308088014215833651465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37001538725342810555767643 55502308088014215833651465)
  ·
    refine ⟨41626731066010661875238599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55502308088014215833651465 41626731066010661875238599)
    ·
      refine ⟨62440096599015992812857899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41626731066010661875238599 62440096599015992812857899)
      ·
        refine ⟨93660144898523989219286849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62440096599015992812857899 93660144898523989219286849)
        ·
          refine ⟨70245108673892991914465137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93660144898523989219286849 70245108673892991914465137)
          ·
            refine ⟨52683831505419743935848853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70245108673892991914465137 52683831505419743935848853)
            ·
              refine ⟨2469554601816550496992915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52683831505419743935848853 2469554601816550496992915)
              ·
                refine ⟨3704331902724825745489373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2469554601816550496992915 3704331902724825745489373)
                ·
                  refine ⟨1389124463521809654558515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3704331902724825745489373 1389124463521809654558515)
                  ·
                    refine ⟨2083686695282714481837773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1389124463521809654558515 2083686695282714481837773)
                    ·
                      refine ⟨781382510731017930689165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2083686695282714481837773 781382510731017930689165)
                      ·
                        rfl

theorem cell23_1521737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3, 1, 3].length) (baseStart_1521737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521737 prefixEnd_1521737 := by exact prefixLift 1521737
  have htrace : WordTrace (prefixWord ++ tailWord_1521737) baseStart_1521737 baseEnd_1521737 := by
    simpa [prefixWord, tailWord_1521737, baseEnd_1521737] using wordTrace_append hprefix tailTrace_1521737
  have hstable : (prefixWord ++ tailWord_1521737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521737).length < 2 ^ (prefixWord ++ tailWord_1521737).sum := by decide
  have hdescent : baseEnd_1521737 < baseStart_1521737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521783 : List Nat := [1, 1, 3, 1, 1, 5, 11]
def baseStart_1521783 : Nat := 118140960795 + 1521783 * 2 ^ 59
def prefixEnd_1521783 : Nat := 4983230072969 + 3 ^ 40 * 1521783 * 2
def baseEnd_1521783 : Nat := 9646989269643515440913

theorem tailTrace_1521783 : CollatzResearch.WordTrace tailWord_1521783 prefixEnd_1521783 9646989269643515440913 := by
  unfold tailWord_1521783
  simp only [CollatzResearch.WordTrace]
  refine ⟨55503985845847565689826003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37002657230565043793217335 55503985845847565689826003)
  ·
    refine ⟨83255978768771348534739005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55503985845847565689826003 83255978768771348534739005)
    ·
      refine ⟨31220992038289255700527127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83255978768771348534739005 31220992038289255700527127)
      ·
        refine ⟨46831488057433883550790691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31220992038289255700527127 46831488057433883550790691)
        ·
          refine ⟨70247232086150825326186037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46831488057433883550790691 70247232086150825326186037)
          ·
            refine ⟨6585678008076639874329941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70247232086150825326186037 6585678008076639874329941)
            ·
              refine ⟨9646989269643515440913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6585678008076639874329941 9646989269643515440913)
              ·
                rfl

theorem cell23_1521783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 11].length) (baseStart_1521783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521783 prefixEnd_1521783 := by exact prefixLift 1521783
  have htrace : WordTrace (prefixWord ++ tailWord_1521783) baseStart_1521783 baseEnd_1521783 := by
    simpa [prefixWord, tailWord_1521783, baseEnd_1521783] using wordTrace_append hprefix tailTrace_1521783
  have hstable : (prefixWord ++ tailWord_1521783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521783).length < 2 ^ (prefixWord ++ tailWord_1521783).sum := by decide
  have hdescent : baseEnd_1521783 < baseStart_1521783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521800 : List Nat := [2, 1, 3, 4, 1, 1, 1, 10]
def baseStart_1521800 : Nat := 118140960795 + 1521800 * 2 ^ 59
def prefixEnd_1521800 : Nat := 4983230072969 + 3 ^ 40 * 1521800 * 2
def baseEnd_1521800 : Nat := 28941291111564858674125

theorem tailTrace_1521800 : CollatzResearch.WordTrace tailWord_1521800 prefixEnd_1521800 28941291111564858674125 := by
  unfold tailWord_1521800
  simp only [CollatzResearch.WordTrace]
  refine ⟨27752302943392988796597427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37003070591190651728796569 27752302943392988796597427)
  ·
    refine ⟨41628454415089483194896141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27752302943392988796597427 41628454415089483194896141)
    ·
      refine ⟨15610670405658556198086053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41628454415089483194896141 15610670405658556198086053)
      ·
        refine ⟨2927000701060979287141135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15610670405658556198086053 2927000701060979287141135)
        ·
          refine ⟨4390501051591468930711703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2927000701060979287141135 4390501051591468930711703)
          ·
            refine ⟨6585751577387203396067555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4390501051591468930711703 6585751577387203396067555)
            ·
              refine ⟨9878627366080805094101333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6585751577387203396067555 9878627366080805094101333)
              ·
                refine ⟨28941291111564858674125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9878627366080805094101333 28941291111564858674125)
                ·
                  rfl

theorem cell23_1521800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 10].length) (baseStart_1521800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521800 prefixEnd_1521800 := by exact prefixLift 1521800
  have htrace : WordTrace (prefixWord ++ tailWord_1521800) baseStart_1521800 baseEnd_1521800 := by
    simpa [prefixWord, tailWord_1521800, baseEnd_1521800] using wordTrace_append hprefix tailTrace_1521800
  have hstable : (prefixWord ++ tailWord_1521800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521800).length < 2 ^ (prefixWord ++ tailWord_1521800).sum := by decide
  have hdescent : baseEnd_1521800 < baseStart_1521800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521831 : List Nat := [1, 1, 6, 2, 3, 1, 1, 1, 1, 1, 5]
def baseStart_1521831 : Nat := 118140960795 + 1521831 * 2 ^ 59
def prefixEnd_1521831 : Nat := 4983230072969 + 3 ^ 40 * 1521831 * 2
def baseEnd_1521831 : Nat := 781430777912540562913733

theorem tailTrace_1521831 : CollatzResearch.WordTrace tailWord_1521831 prefixEnd_1521831 781430777912540562913733 := by
  unfold tailWord_1521831
  simp only [CollatzResearch.WordTrace]
  refine ⟨55505736549673669887573347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37003824366449113258382231 55505736549673669887573347)
  ·
    refine ⟨83258604824510504831360021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55505736549673669887573347 83258604824510504831360021)
    ·
      refine ⟨3902747101148929913970001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83258604824510504831360021 3902747101148929913970001)
      ·
        refine ⟨2927060325861697435477501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3902747101148929913970001 2927060325861697435477501)
        ·
          refine ⟨1097647622198136538304063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2927060325861697435477501 1097647622198136538304063)
          ·
            refine ⟨1646471433297204807456095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1097647622198136538304063 1646471433297204807456095)
            ·
              refine ⟨2469707149945807211184143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1646471433297204807456095 2469707149945807211184143)
              ·
                refine ⟨3704560724918710816776215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2469707149945807211184143 3704560724918710816776215)
                ·
                  refine ⟨5556841087378066225164323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3704560724918710816776215 5556841087378066225164323)
                  ·
                    refine ⟨8335261631067099337746485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5556841087378066225164323 8335261631067099337746485)
                    ·
                      refine ⟨781430777912540562913733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8335261631067099337746485 781430777912540562913733)
                      ·
                        rfl

theorem cell23_1521831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_1521831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521831 prefixEnd_1521831 := by exact prefixLift 1521831
  have htrace : WordTrace (prefixWord ++ tailWord_1521831) baseStart_1521831 baseEnd_1521831 := by
    simpa [prefixWord, tailWord_1521831, baseEnd_1521831] using wordTrace_append hprefix tailTrace_1521831
  have hstable : (prefixWord ++ tailWord_1521831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521831).length < 2 ^ (prefixWord ++ tailWord_1521831).sum := by decide
  have hdescent : baseEnd_1521831 < baseStart_1521831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521838 : List Nat := [4, 1, 4, 2, 1, 1, 2, 2, 2, 4]
def baseStart_1521838 : Nat := 118140960795 + 1521838 * 2 ^ 59
def prefixEnd_1521838 : Nat := 4983230072969 + 3 ^ 40 * 1521838 * 2
def baseEnd_1521838 : Nat := 260478124092374011842067

theorem tailTrace_1521838 : CollatzResearch.WordTrace tailWord_1521838 prefixEnd_1521838 260478124092374011842067 := by
  unfold tailWord_1521838
  simp only [CollatzResearch.WordTrace]
  refine ⟨6938248982581038760384771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37003994573765540055385445 6938248982581038760384771)
  ·
    refine ⟨10407373473871558140577157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6938248982581038760384771 10407373473871558140577157)
    ·
      refine ⟨1951382526350917151358217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10407373473871558140577157 1951382526350917151358217)
      ·
        refine ⟨1463536894763187863518663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1951382526350917151358217 1463536894763187863518663)
        ·
          refine ⟨2195305342144781795277995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1463536894763187863518663 2195305342144781795277995)
          ·
            refine ⟨3292958013217172692916993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2195305342144781795277995 3292958013217172692916993)
            ·
              refine ⟨2469718509912879519687745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3292958013217172692916993 2469718509912879519687745)
              ·
                refine ⟨1852288882434659639765809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2469718509912879519687745 1852288882434659639765809)
                ·
                  refine ⟨1389216661825994729824357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1852288882434659639765809 1389216661825994729824357)
                  ·
                    refine ⟨260478124092374011842067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1389216661825994729824357 260478124092374011842067)
                    ·
                      rfl

theorem cell23_1521838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_1521838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521838 prefixEnd_1521838 := by exact prefixLift 1521838
  have htrace : WordTrace (prefixWord ++ tailWord_1521838) baseStart_1521838 baseEnd_1521838 := by
    simpa [prefixWord, tailWord_1521838, baseEnd_1521838] using wordTrace_append hprefix tailTrace_1521838
  have hstable : (prefixWord ++ tailWord_1521838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521838).length < 2 ^ (prefixWord ++ tailWord_1521838).sum := by decide
  have hdescent : baseEnd_1521838 < baseStart_1521838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521845 : List Nat := [1, 3, 3, 4, 1, 1, 1, 4, 1, 2, 2]
def baseStart_1521845 : Nat := 118140960795 + 1521845 * 2 ^ 59
def prefixEnd_1521845 : Nat := 4983230072969 + 3 ^ 40 * 1521845 * 2
def baseEnd_1521845 : Nat := 781437966641703508138669

theorem tailTrace_1521845 : CollatzResearch.WordTrace tailWord_1521845 prefixEnd_1521845 781437966641703508138669 := by
  unfold tailWord_1521845
  simp only [CollatzResearch.WordTrace]
  refine ⟨55506247171622950278582989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37004164781081966852388659 55506247171622950278582989)
  ·
    refine ⟨20814842689358606354468621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55506247171622950278582989 20814842689358606354468621)
    ·
      refine ⟨7805566008509477382925733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20814842689358606354468621 7805566008509477382925733)
      ·
        refine ⟨1463543626595527009298575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7805566008509477382925733 1463543626595527009298575)
        ·
          refine ⟨2195315439893290513947863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1463543626595527009298575 2195315439893290513947863)
          ·
            refine ⟨3292973159839935770921795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2195315439893290513947863 3292973159839935770921795)
            ·
              refine ⟨4939459739759903656382693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3292973159839935770921795 4939459739759903656382693)
              ·
                refine ⟨926148701204981935571755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4939459739759903656382693 926148701204981935571755)
                ·
                  refine ⟨1389223051807472903357633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 926148701204981935571755 1389223051807472903357633)
                  ·
                    refine ⟨1041917288855604677518225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1389223051807472903357633 1041917288855604677518225)
                    ·
                      refine ⟨781437966641703508138669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1041917288855604677518225 781437966641703508138669)
                      ·
                        rfl

theorem cell23_1521845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_1521845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521845 prefixEnd_1521845 := by exact prefixLift 1521845
  have htrace : WordTrace (prefixWord ++ tailWord_1521845) baseStart_1521845 baseEnd_1521845 := by
    simpa [prefixWord, tailWord_1521845, baseEnd_1521845] using wordTrace_append hprefix tailTrace_1521845
  have hstable : (prefixWord ++ tailWord_1521845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521845).length < 2 ^ (prefixWord ++ tailWord_1521845).sum := by decide
  have hdescent : baseEnd_1521845 < baseStart_1521845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521850 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4]
def baseStart_1521850 : Nat := 118140960795 + 1521850 * 2 ^ 59
def prefixEnd_1521850 : Nat := 4983230072969 + 3 ^ 40 * 1521850 * 2
def baseEnd_1521850 : Nat := 781440534044975988576145

theorem tailTrace_1521850 : CollatzResearch.WordTrace tailWord_1521850 prefixEnd_1521850 781440534044975988576145 := by
  unfold tailWord_1521850
  simp only [CollatzResearch.WordTrace]
  refine ⟨13876607384151209033128751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37004286357736557421676669 13876607384151209033128751)
  ·
    refine ⟨20814911076226813549693127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13876607384151209033128751 20814911076226813549693127)
    ·
      refine ⟨31222366614340220324539691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20814911076226813549693127 31222366614340220324539691)
      ·
        refine ⟨46833549921510330486809537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31222366614340220324539691 46833549921510330486809537)
        ·
          refine ⟨35125162441132747865107153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46833549921510330486809537 35125162441132747865107153)
          ·
            refine ⟨26343871830849560898830365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35125162441132747865107153 26343871830849560898830365)
            ·
              refine ⟨9878951936568585337061387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26343871830849560898830365 9878951936568585337061387)
              ·
                refine ⟨14818427904852878005592081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9878951936568585337061387 14818427904852878005592081)
                ·
                  refine ⟨11113820928639658504194061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14818427904852878005592081 11113820928639658504194061)
                  ·
                    refine ⟨4167682848239871939072773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11113820928639658504194061 4167682848239871939072773)
                    ·
                      refine ⟨781440534044975988576145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4167682848239871939072773 781440534044975988576145)
                      ·
                        rfl

theorem cell23_1521850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_1521850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521850 prefixEnd_1521850 := by exact prefixLift 1521850
  have htrace : WordTrace (prefixWord ++ tailWord_1521850) baseStart_1521850 baseEnd_1521850 := by
    simpa [prefixWord, tailWord_1521850, baseEnd_1521850] using wordTrace_append hprefix tailTrace_1521850
  have hstable : (prefixWord ++ tailWord_1521850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521850).length < 2 ^ (prefixWord ++ tailWord_1521850).sum := by decide
  have hdescent : baseEnd_1521850 < baseStart_1521850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521907 : List Nat := [1, 1, 1, 2, 2, 4, 1, 6, 5]
def baseStart_1521907 : Nat := 118140960795 + 1521907 * 2 ^ 59
def prefixEnd_1521907 : Nat := 4983230072969 + 3 ^ 40 * 1521907 * 2
def baseEnd_1521907 : Nat := 86829978049142473951487

theorem tailTrace_1521907 : CollatzResearch.WordTrace tailWord_1521907 prefixEnd_1521907 86829978049142473951487 := by
  unfold tailWord_1521907
  simp only [CollatzResearch.WordTrace]
  refine ⟨55508508497398334867339975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37005672331598889911559983 55508508497398334867339975)
  ·
    refine ⟨83262762746097502301009963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55508508497398334867339975 83262762746097502301009963)
    ·
      refine ⟨124894144119146253451514945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83262762746097502301009963 124894144119146253451514945)
      ·
        refine ⟨93670608089359690088636209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124894144119146253451514945 93670608089359690088636209)
        ·
          refine ⟨70252956067019767566477157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93670608089359690088636209 70252956067019767566477157)
          ·
            refine ⟨13172429262566206418714467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70252956067019767566477157 13172429262566206418714467)
            ·
              refine ⟨19758643893849309628071701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13172429262566206418714467 19758643893849309628071701)
              ·
                refine ⟨926186432524186388815861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19758643893849309628071701 926186432524186388815861)
                ·
                  refine ⟨86829978049142473951487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 926186432524186388815861 86829978049142473951487)
                  ·
                    rfl

theorem cell23_1521907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6, 5].length) (baseStart_1521907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521907 prefixEnd_1521907 := by exact prefixLift 1521907
  have htrace : WordTrace (prefixWord ++ tailWord_1521907) baseStart_1521907 baseEnd_1521907 := by
    simpa [prefixWord, tailWord_1521907, baseEnd_1521907] using wordTrace_append hprefix tailTrace_1521907
  have hstable : (prefixWord ++ tailWord_1521907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521907).length < 2 ^ (prefixWord ++ tailWord_1521907).sum := by decide
  have hdescent : baseEnd_1521907 < baseStart_1521907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521920 : List Nat := [2, 1, 1, 2, 1, 1, 5, 2, 1, 7]
def baseStart_1521920 : Nat := 118140960795 + 1521920 * 2 ^ 59
def prefixEnd_1521920 : Nat := 4983230072969 + 3 ^ 40 * 1521920 * 2
def baseEnd_1521920 : Nat := 260492159230263571566941

theorem tailTrace_1521920 : CollatzResearch.WordTrace tailWord_1521920 prefixEnd_1521920 260492159230263571566941 := by
  unfold tailWord_1521920
  simp only [CollatzResearch.WordTrace]
  refine ⟨27754491323175619043781607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37005988430900825391708809 27754491323175619043781607)
  ·
    refine ⟨41631736984763428565672411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27754491323175619043781607 41631736984763428565672411)
    ·
      refine ⟨62447605477145142848508617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41631736984763428565672411 62447605477145142848508617)
      ·
        refine ⟨46835704107858857136381463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62447605477145142848508617 46835704107858857136381463)
        ·
          refine ⟨70253556161788285704572195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46835704107858857136381463 70253556161788285704572195)
          ·
            refine ⟨105380334242682428556858293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70253556161788285704572195 105380334242682428556858293)
            ·
              refine ⟨9879406335251477677205465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105380334242682428556858293 9879406335251477677205465)
              ·
                refine ⟨7409554751438608257904099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9879406335251477677205465 7409554751438608257904099)
                ·
                  refine ⟨11114332127157912386856149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7409554751438608257904099 11114332127157912386856149)
                  ·
                    refine ⟨260492159230263571566941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11114332127157912386856149 260492159230263571566941)
                    ·
                      rfl

theorem cell23_1521920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 1, 7].length) (baseStart_1521920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521920 prefixEnd_1521920 := by exact prefixLift 1521920
  have htrace : WordTrace (prefixWord ++ tailWord_1521920) baseStart_1521920 baseEnd_1521920 := by
    simpa [prefixWord, tailWord_1521920, baseEnd_1521920] using wordTrace_append hprefix tailTrace_1521920
  have hstable : (prefixWord ++ tailWord_1521920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521920).length < 2 ^ (prefixWord ++ tailWord_1521920).sum := by decide
  have hdescent : baseEnd_1521920 < baseStart_1521920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521954 : List Nat := [3, 3, 1, 1, 3, 2, 1, 2, 2, 5]
def baseStart_1521954 : Nat := 118140960795 + 1521954 * 2 ^ 59
def prefixEnd_1521954 : Nat := 4983230072969 + 3 ^ 40 * 1521954 * 2
def baseEnd_1521954 : Nat := 260497978677681193891889

theorem tailTrace_1521954 : CollatzResearch.WordTrace tailWord_1521954 prefixEnd_1521954 260497978677681193891889 := by
  unfold tailWord_1521954
  simp only [CollatzResearch.WordTrace]
  refine ⟨13877555682057015473575229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37006815152152041262867277 13877555682057015473575229)
  ·
    refine ⟨5204083380771380802590711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13877555682057015473575229 5204083380771380802590711)
    ·
      refine ⟨7806125071157071203886067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5204083380771380802590711 7806125071157071203886067)
      ·
        refine ⟨11709187606735606805829101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7806125071157071203886067 11709187606735606805829101)
        ·
          refine ⟨4390945352525852552185913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11709187606735606805829101 4390945352525852552185913)
          ·
            refine ⟨3293209014394389414139435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4390945352525852552185913 3293209014394389414139435)
            ·
              refine ⟨4939813521591584121209153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3293209014394389414139435 4939813521591584121209153)
              ·
                refine ⟨3704860141193688090906865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4939813521591584121209153 3704860141193688090906865)
                ·
                  refine ⟨2778645105895266068180149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3704860141193688090906865 2778645105895266068180149)
                  ·
                    refine ⟨260497978677681193891889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2778645105895266068180149 260497978677681193891889)
                    ·
                      rfl

theorem cell23_1521954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_1521954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1521954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1521954 prefixEnd_1521954 := by exact prefixLift 1521954
  have htrace : WordTrace (prefixWord ++ tailWord_1521954) baseStart_1521954 baseEnd_1521954 := by
    simpa [prefixWord, tailWord_1521954, baseEnd_1521954] using wordTrace_append hprefix tailTrace_1521954
  have hstable : (prefixWord ++ tailWord_1521954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521954).length < 2 ^ (prefixWord ++ tailWord_1521954).sum := by decide
  have hdescent : baseEnd_1521954 < baseStart_1521954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522018 : List Nat := [3, 3, 2, 1, 1, 3, 1, 4, 1, 4]
def baseStart_1522018 : Nat := 118140960795 + 1522018 * 2 ^ 59
def prefixEnd_1522018 : Nat := 4983230072969 + 3 ^ 40 * 1522018 * 2
def baseEnd_1522018 : Nat := 260508932931643777091791

theorem tailTrace_1522018 : CollatzResearch.WordTrace tailWord_1522018 prefixEnd_1522018 260508932931643777091791 := by
  unfold tailWord_1522018
  simp only [CollatzResearch.WordTrace]
  refine ⟨13878139249999050206157677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37008371333330800549753805 13878139249999050206157677)
  ·
    refine ⟨5204302218749643827309129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13878139249999050206157677 5204302218749643827309129)
    ·
      refine ⟨3903226664062232870481847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5204302218749643827309129 3903226664062232870481847)
      ·
        refine ⟨5854839996093349305722771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3903226664062232870481847 5854839996093349305722771)
        ·
          refine ⟨8782259994140023958584157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5854839996093349305722771 8782259994140023958584157)
          ·
            refine ⟨3293347497802508984469059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8782259994140023958584157 3293347497802508984469059)
            ·
              refine ⟨4940021246703763476703589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3293347497802508984469059 4940021246703763476703589)
              ·
                refine ⟨926253983756955651881923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4940021246703763476703589 926253983756955651881923)
                ·
                  refine ⟨1389380975635433477822885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 926253983756955651881923 1389380975635433477822885)
                  ·
                    refine ⟨260508932931643777091791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1389380975635433477822885 260508932931643777091791)
                    ·
                      rfl

theorem cell23_1522018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_1522018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522018 prefixEnd_1522018 := by exact prefixLift 1522018
  have htrace : WordTrace (prefixWord ++ tailWord_1522018) baseStart_1522018 baseEnd_1522018 := by
    simpa [prefixWord, tailWord_1522018, baseEnd_1522018] using wordTrace_append hprefix tailTrace_1522018
  have hstable : (prefixWord ++ tailWord_1522018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522018).length < 2 ^ (prefixWord ++ tailWord_1522018).sum := by decide
  have hdescent : baseEnd_1522018 < baseStart_1522018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522051 : List Nat := [1, 1, 1, 3, 6, 1, 1, 1, 1, 5, 2]
def baseStart_1522051 : Nat := 118140960795 + 1522051 * 2 ^ 59
def prefixEnd_1522051 : Nat := 4983230072969 + 3 ^ 40 * 1522051 * 2
def baseEnd_1522051 : Nat := 781543743656529702162721

theorem tailTrace_1522051 : CollatzResearch.WordTrace tailWord_1522051 prefixEnd_1522051 781543743656529702162721 := by
  unfold tailWord_1522051
  simp only [CollatzResearch.WordTrace]
  refine ⟨55513760608876647460582007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37009173739251098307054671 55513760608876647460582007)
  ·
    refine ⟨83270640913314971190873011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55513760608876647460582007 83270640913314971190873011)
    ·
      refine ⟨124905961369972456786309517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83270640913314971190873011 124905961369972456786309517)
      ·
        refine ⟨46839735513739671294866069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124905961369972456786309517 46839735513739671294866069)
        ·
          refine ⟨2195612602206547091946847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46839735513739671294866069 2195612602206547091946847)
          ·
            refine ⟨3293418903309820637920271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2195612602206547091946847 3293418903309820637920271)
            ·
              refine ⟨4940128354964730956880407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3293418903309820637920271 4940128354964730956880407)
              ·
                refine ⟨7410192532447096435320611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4940128354964730956880407 7410192532447096435320611)
                ·
                  refine ⟨11115288798670644652980917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7410192532447096435320611 11115288798670644652980917)
                  ·
                    refine ⟨1042058324875372936216961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11115288798670644652980917 1042058324875372936216961)
                    ·
                      refine ⟨781543743656529702162721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1042058324875372936216961 781543743656529702162721)
                      ·
                        rfl

theorem cell23_1522051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 5, 2].length) (baseStart_1522051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522051 prefixEnd_1522051 := by exact prefixLift 1522051
  have htrace : WordTrace (prefixWord ++ tailWord_1522051) baseStart_1522051 baseEnd_1522051 := by
    simpa [prefixWord, tailWord_1522051, baseEnd_1522051] using wordTrace_append hprefix tailTrace_1522051
  have hstable : (prefixWord ++ tailWord_1522051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522051).length < 2 ^ (prefixWord ++ tailWord_1522051).sum := by decide
  have hdescent : baseEnd_1522051 < baseStart_1522051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522084 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 5, 2, 3]
def baseStart_1522084 : Nat := 118140960795 + 1522084 * 2 ^ 59
def prefixEnd_1522084 : Nat := 4983230072969 + 3 ^ 40 * 1522084 * 2
def baseEnd_1522084 : Nat := 781560688518128073050069

theorem tailTrace_1522084 : CollatzResearch.WordTrace tailWord_1522084 prefixEnd_1522084 781560688518128073050069 := by
  unfold tailWord_1522084
  simp only [CollatzResearch.WordTrace]
  refine ⟨27757482108878547048266653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37009976145171396064355537 27757482108878547048266653)
  ·
    refine ⟨10409055790829455143099995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27757482108878547048266653 10409055790829455143099995)
    ·
      refine ⟨15613583686244182714649993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10409055790829455143099995 15613583686244182714649993)
      ·
        refine ⟨11710187764683137035987495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15613583686244182714649993 11710187764683137035987495)
        ·
          refine ⟨17565281647024705553981243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11710187764683137035987495 17565281647024705553981243)
          ·
            refine ⟨26347922470537058330971865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17565281647024705553981243 26347922470537058330971865)
            ·
              refine ⟨19760941852902793748228899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26347922470537058330971865 19760941852902793748228899)
              ·
                refine ⟨29641412779354190622343349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19760941852902793748228899 29641412779354190622343349)
                ·
                  refine ⟨2778882448064455370844689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29641412779354190622343349 2778882448064455370844689)
                  ·
                    refine ⟨2084161836048341528133517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2778882448064455370844689 2084161836048341528133517)
                    ·
                      refine ⟨781560688518128073050069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2084161836048341528133517 781560688518128073050069)
                      ·
                        rfl

theorem cell23_1522084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_1522084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522084 prefixEnd_1522084 := by exact prefixLift 1522084
  have htrace : WordTrace (prefixWord ++ tailWord_1522084) baseStart_1522084 baseEnd_1522084 := by
    simpa [prefixWord, tailWord_1522084, baseEnd_1522084] using wordTrace_append hprefix tailTrace_1522084
  have hstable : (prefixWord ++ tailWord_1522084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522084).length < 2 ^ (prefixWord ++ tailWord_1522084).sum := by decide
  have hdescent : baseEnd_1522084 < baseStart_1522084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522127 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 5]
def baseStart_1522127 : Nat := 118140960795 + 1522127 * 2 ^ 59
def prefixEnd_1522127 : Nat := 4983230072969 + 3 ^ 40 * 1522127 * 2
def baseEnd_1522127 : Nat := 781582768186271404812371

theorem tailTrace_1522127 : CollatzResearch.WordTrace tailWord_1522127 prefixEnd_1522127 781582768186271404812371 := by
  unfold tailWord_1522127
  simp only [CollatzResearch.WordTrace]
  refine ⟨55516532556601312440348635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37011021704400874960232423 55516532556601312440348635)
  ·
    refine ⟨83274798834901968660522953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55516532556601312440348635 83274798834901968660522953)
    ·
      refine ⟨62456099126176476495392215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83274798834901968660522953 62456099126176476495392215)
      ·
        refine ⟨93684148689264714743088323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62456099126176476495392215 93684148689264714743088323)
        ·
          refine ⟨140526223033897072114632485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93684148689264714743088323 140526223033897072114632485)
          ·
            refine ⟨26348666818855701021493591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140526223033897072114632485 26348666818855701021493591)
            ·
              refine ⟨39523000228283551532240387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26348666818855701021493591 39523000228283551532240387)
              ·
                refine ⟨59284500342425327298360581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39523000228283551532240387 59284500342425327298360581)
                ·
                  refine ⟨11115843814204748868442609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59284500342425327298360581 11115843814204748868442609)
                  ·
                    refine ⟨8336882860653561651331957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11115843814204748868442609 8336882860653561651331957)
                    ·
                      refine ⟨781582768186271404812371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8336882860653561651331957 781582768186271404812371)
                      ·
                        rfl

theorem cell23_1522127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 5].length) (baseStart_1522127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522127 prefixEnd_1522127 := by exact prefixLift 1522127
  have htrace : WordTrace (prefixWord ++ tailWord_1522127) baseStart_1522127 baseEnd_1522127 := by
    simpa [prefixWord, tailWord_1522127, baseEnd_1522127] using wordTrace_append hprefix tailTrace_1522127
  have hstable : (prefixWord ++ tailWord_1522127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522127).length < 2 ^ (prefixWord ++ tailWord_1522127).sum := by decide
  have hdescent : baseEnd_1522127 < baseStart_1522127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522158 : List Nat := [4, 1, 2, 1, 2, 3, 1, 1, 3, 3, 2]
def baseStart_1522158 : Nat := 118140960795 + 1522158 * 2 ^ 59
def prefixEnd_1522158 : Nat := 4983230072969 + 3 ^ 40 * 1522158 * 2
def baseEnd_1522158 : Nat := 781598686086560783524729

theorem tailTrace_1522158 : CollatzResearch.WordTrace tailWord_1522158 prefixEnd_1522158 781598686086560783524729 := by
  unfold tailWord_1522158
  simp only [CollatzResearch.WordTrace]
  refine ⟨6939707902436125591840891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37011775479659336489818085 6939707902436125591840891)
  ·
    refine ⟨10409561853654188387761337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6939707902436125591840891 10409561853654188387761337)
    ·
      refine ⟨7807171390240641290821003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10409561853654188387761337 7807171390240641290821003)
      ·
        refine ⟨11710757085360961936231505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7807171390240641290821003 11710757085360961936231505)
        ·
          refine ⟨8783067814020721452173629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11710757085360961936231505 8783067814020721452173629)
          ·
            refine ⟨3293650430257770544565111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8783067814020721452173629 3293650430257770544565111)
            ·
              refine ⟨4940475645386655816847667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3293650430257770544565111 4940475645386655816847667)
              ·
                refine ⟨7410713468079983725271501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4940475645386655816847667 7410713468079983725271501)
                ·
                  refine ⟨2779017550529993896976813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7410713468079983725271501 2779017550529993896976813)
                  ·
                    refine ⟨1042131581448747711366305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2779017550529993896976813 1042131581448747711366305)
                    ·
                      refine ⟨781598686086560783524729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1042131581448747711366305 781598686086560783524729)
                      ·
                        rfl

theorem cell23_1522158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_1522158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522158 prefixEnd_1522158 := by exact prefixLift 1522158
  have htrace : WordTrace (prefixWord ++ tailWord_1522158) baseStart_1522158 baseEnd_1522158 := by
    simpa [prefixWord, tailWord_1522158, baseEnd_1522158] using wordTrace_append hprefix tailTrace_1522158
  have hstable : (prefixWord ++ tailWord_1522158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522158).length < 2 ^ (prefixWord ++ tailWord_1522158).sum := by decide
  have hdescent : baseEnd_1522158 < baseStart_1522158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522167 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 6]
def baseStart_1522167 : Nat := 118140960795 + 1522167 * 2 ^ 59
def prefixEnd_1522167 : Nat := 4983230072969 + 3 ^ 40 * 1522167 * 2
def baseEnd_1522167 : Nat := 781603307412451248312187

theorem tailTrace_1522167 : CollatzResearch.WordTrace tailWord_1522167 prefixEnd_1522167 781603307412451248312187 := by
  unfold tailWord_1522167
  simp only [CollatzResearch.WordTrace]
  refine ⟨55517991476456399271804755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37011994317637599514536503 55517991476456399271804755)
  ·
    refine ⟨83276987214684598907707133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55517991476456399271804755 83276987214684598907707133)
    ·
      refine ⟨31228870205506724590390175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83276987214684598907707133 31228870205506724590390175)
      ·
        refine ⟨46843305308260086885585263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31228870205506724590390175 46843305308260086885585263)
        ·
          refine ⟨70264957962390130328377895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46843305308260086885585263 70264957962390130328377895)
          ·
            refine ⟨105397436943585195492566843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70264957962390130328377895 105397436943585195492566843)
            ·
              refine ⟨158096155415377793238850265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105397436943585195492566843 158096155415377793238850265)
              ·
                refine ⟨118572116561533344929137699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158096155415377793238850265 118572116561533344929137699)
                ·
                  refine ⟨177858174842300017393706549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118572116561533344929137699 177858174842300017393706549)
                  ·
                    refine ⟨16674203891465626630659989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 177858174842300017393706549 16674203891465626630659989)
                    ·
                      refine ⟨781603307412451248312187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16674203891465626630659989 781603307412451248312187)
                      ·
                        rfl

theorem cell23_1522167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_1522167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522167 prefixEnd_1522167 := by exact prefixLift 1522167
  have htrace : WordTrace (prefixWord ++ tailWord_1522167) baseStart_1522167 baseEnd_1522167 := by
    simpa [prefixWord, tailWord_1522167, baseEnd_1522167] using wordTrace_append hprefix tailTrace_1522167
  have hstable : (prefixWord ++ tailWord_1522167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522167).length < 2 ^ (prefixWord ++ tailWord_1522167).sum := by decide
  have hdescent : baseEnd_1522167 < baseStart_1522167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522184 : List Nat := [2, 1, 3, 2, 1, 1, 1, 4, 2, 2, 4]
def baseStart_1522184 : Nat := 118140960795 + 1522184 * 2 ^ 59
def prefixEnd_1522184 : Nat := 4983230072969 + 3 ^ 40 * 1522184 * 2
def baseEnd_1522184 : Nat := 781612036583577681799609

theorem tailTrace_1522184 : CollatzResearch.WordTrace tailWord_1522184 prefixEnd_1522184 781612036583577681799609 := by
  unfold tailWord_1522184
  simp only [CollatzResearch.WordTrace]
  refine ⟨27759305758697405587586803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37012407678263207450115737 27759305758697405587586803)
  ·
    refine ⟨41638958638046108381380205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27759305758697405587586803 41638958638046108381380205)
    ·
      refine ⟨15614609489267290643017577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41638958638046108381380205 15614609489267290643017577)
      ·
        refine ⟨11710957116950467982263183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15614609489267290643017577 11710957116950467982263183)
        ·
          refine ⟨17566435675425701973394775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11710957116950467982263183 17566435675425701973394775)
          ·
            refine ⟨26349653513138552960092163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17566435675425701973394775 26349653513138552960092163)
            ·
              refine ⟨39524480269707829440138245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26349653513138552960092163 39524480269707829440138245)
              ·
                refine ⟨7410840050570218020025921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39524480269707829440138245 7410840050570218020025921)
                ·
                  refine ⟨5558130037927663515019441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7410840050570218020025921 5558130037927663515019441)
                  ·
                    refine ⟨4168597528445747636264581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5558130037927663515019441 4168597528445747636264581)
                    ·
                      refine ⟨781612036583577681799609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4168597528445747636264581 781612036583577681799609)
                      ·
                        rfl

theorem cell23_1522184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_1522184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522184 prefixEnd_1522184 := by exact prefixLift 1522184
  have htrace : WordTrace (prefixWord ++ tailWord_1522184) baseStart_1522184 baseEnd_1522184 := by
    simpa [prefixWord, tailWord_1522184, baseEnd_1522184] using wordTrace_append hprefix tailTrace_1522184
  have hstable : (prefixWord ++ tailWord_1522184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522184).length < 2 ^ (prefixWord ++ tailWord_1522184).sum := by decide
  have hdescent : baseEnd_1522184 < baseStart_1522184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522205 : List Nat := [1, 4, 2, 2, 1, 2, 2, 3, 2, 2, 2]
def baseStart_1522205 : Nat := 118140960795 + 1522205 * 2 ^ 59
def prefixEnd_1522205 : Nat := 4983230072969 + 3 ^ 40 * 1522205 * 2
def baseEnd_1522205 : Nat := 781622819677322099637013

theorem tailTrace_1522205 : CollatzResearch.WordTrace tailWord_1522205 prefixEnd_1522205 781622819677322099637013 := by
  unfold tailWord_1522205
  simp only [CollatzResearch.WordTrace]
  refine ⟨55519377450318731761688069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37012918300212487841125379 55519377450318731761688069)
  ·
    refine ⟨10409883271934762205316513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55519377450318731761688069 10409883271934762205316513)
    ·
      refine ⟨7807412453951071653987385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10409883271934762205316513 7807412453951071653987385)
      ·
        refine ⟨5855559340463303740490539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7807412453951071653987385 5855559340463303740490539)
        ·
          refine ⟨8783339010694955610735809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5855559340463303740490539 8783339010694955610735809)
          ·
            refine ⟨6587504258021216708051857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8783339010694955610735809 6587504258021216708051857)
            ·
              refine ⟨4940628193515912531038893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6587504258021216708051857 4940628193515912531038893)
              ·
                refine ⟨1852735572568467199139585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4940628193515912531038893 1852735572568467199139585)
                ·
                  refine ⟨1389551679426350399354689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1852735572568467199139585 1389551679426350399354689)
                  ·
                    refine ⟨1042163759569762799516017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1389551679426350399354689 1042163759569762799516017)
                    ·
                      refine ⟨781622819677322099637013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1042163759569762799516017 781622819677322099637013)
                      ·
                        rfl

theorem cell23_1522205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_1522205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522205 prefixEnd_1522205 := by exact prefixLift 1522205
  have htrace : WordTrace (prefixWord ++ tailWord_1522205) baseStart_1522205 baseEnd_1522205 := by
    simpa [prefixWord, tailWord_1522205, baseEnd_1522205] using wordTrace_append hprefix tailTrace_1522205
  have hstable : (prefixWord ++ tailWord_1522205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522205).length < 2 ^ (prefixWord ++ tailWord_1522205).sum := by decide
  have hdescent : baseEnd_1522205 < baseStart_1522205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522281 : List Nat := [1, 2, 1, 1, 1, 4, 1, 5, 2, 2, 3]
def baseStart_1522281 : Nat := 118140960795 + 1522281 * 2 ^ 59
def prefixEnd_1522281 : Nat := 4983230072969 + 3 ^ 40 * 1522281 * 2
def baseEnd_1522281 : Nat := 781661844207063802286663

theorem tailTrace_1522281 : CollatzResearch.WordTrace tailWord_1522281 prefixEnd_1522281 781661844207063802286663 := by
  unfold tailWord_1522281
  simp only [CollatzResearch.WordTrace]
  refine ⟨55522149398043396741454697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37014766265362264494303131 55522149398043396741454697)
  ·
    refine ⟨41641612048532547556091023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55522149398043396741454697 41641612048532547556091023)
    ·
      refine ⟨62462418072798821334136535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41641612048532547556091023 62462418072798821334136535)
      ·
        refine ⟨93693627109198232001204803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62462418072798821334136535 93693627109198232001204803)
        ·
          refine ⟨140540440663797348001807205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93693627109198232001204803 140540440663797348001807205)
          ·
            refine ⟨26351332624462002750338851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140540440663797348001807205 26351332624462002750338851)
            ·
              refine ⟨39526998936693004125508277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26351332624462002750338851 39526998936693004125508277)
              ·
                refine ⟨3705656150314969136766401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39526998936693004125508277 3705656150314969136766401)
                ·
                  refine ⟨2779242112736226852574801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3705656150314969136766401 2779242112736226852574801)
                  ·
                    refine ⟨2084431584552170139431101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2779242112736226852574801 2084431584552170139431101)
                    ·
                      refine ⟨781661844207063802286663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2084431584552170139431101 781661844207063802286663)
                      ·
                        rfl

theorem cell23_1522281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 2, 3].length) (baseStart_1522281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522281 prefixEnd_1522281 := by exact prefixLift 1522281
  have htrace : WordTrace (prefixWord ++ tailWord_1522281) baseStart_1522281 baseEnd_1522281 := by
    simpa [prefixWord, tailWord_1522281, baseEnd_1522281] using wordTrace_append hprefix tailTrace_1522281
  have hstable : (prefixWord ++ tailWord_1522281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522281).length < 2 ^ (prefixWord ++ tailWord_1522281).sum := by decide
  have hdescent : baseEnd_1522281 < baseStart_1522281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522284 : List Nat := [2, 2, 1, 1, 3, 1, 3, 2, 8]
def baseStart_1522284 : Nat := 118140960795 + 1522284 * 2 ^ 59
def prefixEnd_1522284 : Nat := 4983230072969 + 3 ^ 40 * 1522284 * 2
def baseEnd_1522284 : Nat := 86851487183225254505461

theorem tailTrace_1522284 : CollatzResearch.WordTrace tailWord_1522284 prefixEnd_1522284 86851487183225254505461 := by
  unfold tailWord_1522284
  simp only [CollatzResearch.WordTrace]
  refine ⟨27761129408516264126906953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37014839211355018835875937 27761129408516264126906953)
  ·
    refine ⟨20820847056387198095180215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27761129408516264126906953 20820847056387198095180215)
    ·
      refine ⟨31231270584580797142770323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20820847056387198095180215 31231270584580797142770323)
      ·
        refine ⟨46846905876871195714155485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31231270584580797142770323 46846905876871195714155485)
        ·
          refine ⟨17567589703826698392808307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46846905876871195714155485 17567589703826698392808307)
          ·
            refine ⟨26351384555740047589212461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17567589703826698392808307 26351384555740047589212461)
            ·
              refine ⟨9881769208402517845954673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26351384555740047589212461 9881769208402517845954673)
              ·
                refine ⟨7411326906301888384466005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9881769208402517845954673 7411326906301888384466005)
                ·
                  refine ⟨86851487183225254505461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7411326906301888384466005 86851487183225254505461)
                  ·
                    rfl

theorem cell23_1522284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 8].length) (baseStart_1522284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522284 prefixEnd_1522284 := by exact prefixLift 1522284
  have htrace : WordTrace (prefixWord ++ tailWord_1522284) baseStart_1522284 baseEnd_1522284 := by
    simpa [prefixWord, tailWord_1522284, baseEnd_1522284] using wordTrace_append hprefix tailTrace_1522284
  have hstable : (prefixWord ++ tailWord_1522284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522284).length < 2 ^ (prefixWord ++ tailWord_1522284).sum := by decide
  have hdescent : baseEnd_1522284 < baseStart_1522284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522328 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 5, 1, 3]
def baseStart_1522328 : Nat := 118140960795 + 1522328 * 2 ^ 59
def prefixEnd_1522328 : Nat := 4983230072969 + 3 ^ 40 * 1522328 * 2
def baseEnd_1522328 : Nat := 781685977797825118398947

theorem tailTrace_1522328 : CollatzResearch.WordTrace tailWord_1522328 prefixEnd_1522328 781685977797825118398947 := by
  unfold tailWord_1522328
  simp only [CollatzResearch.WordTrace]
  refine ⟨27761931814436561884207819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37015909085915415845610425 27761931814436561884207819)
  ·
    refine ⟨41642897721654842826311729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27761931814436561884207819 41642897721654842826311729)
    ·
      refine ⟨31232173291241132119733797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41642897721654842826311729 31232173291241132119733797)
      ·
        refine ⟨5856032492107712272450087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31232173291241132119733797 5856032492107712272450087)
        ·
          refine ⟨8784048738161568408675131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5856032492107712272450087 8784048738161568408675131)
          ·
            refine ⟨13176073107242352613012697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8784048738161568408675131 13176073107242352613012697)
            ·
              refine ⟨9882054830431764459759523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13176073107242352613012697 9882054830431764459759523)
              ·
                refine ⟨14823082245647646689639285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9882054830431764459759523 14823082245647646689639285)
                ·
                  refine ⟨1389663960529466877153683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14823082245647646689639285 1389663960529466877153683)
                  ·
                    refine ⟨2084495940794200315730525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1389663960529466877153683 2084495940794200315730525)
                    ·
                      refine ⟨781685977797825118398947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2084495940794200315730525 781685977797825118398947)
                      ·
                        rfl

theorem cell23_1522328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_1522328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522328 prefixEnd_1522328 := by exact prefixLift 1522328
  have htrace : WordTrace (prefixWord ++ tailWord_1522328) baseStart_1522328 baseEnd_1522328 := by
    simpa [prefixWord, tailWord_1522328, baseEnd_1522328] using wordTrace_append hprefix tailTrace_1522328
  have hstable : (prefixWord ++ tailWord_1522328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522328).length < 2 ^ (prefixWord ++ tailWord_1522328).sum := by decide
  have hdescent : baseEnd_1522328 < baseStart_1522328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522378 : List Nat := [3, 1, 2, 1, 4, 2, 2, 1, 1, 6]
def baseStart_1522378 : Nat := 118140960795 + 1522378 * 2 ^ 59
def prefixEnd_1522378 : Nat := 4983230072969 + 3 ^ 40 * 1522378 * 2
def baseEnd_1522378 : Nat := 260570550610183307591239

theorem tailTrace_1522378 : CollatzResearch.WordTrace tailWord_1522378 prefixEnd_1522378 260570550610183307591239 := by
  unfold tailWord_1522378
  simp only [CollatzResearch.WordTrace]
  refine ⟨13881421819672995576933947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37017124852461321538490525 13881421819672995576933947)
  ·
    refine ⟨20822132729509493365400921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13881421819672995576933947 20822132729509493365400921)
    ·
      refine ⟨15616599547132120024050691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20822132729509493365400921 15616599547132120024050691)
      ·
        refine ⟨23424899320698180036076037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15616599547132120024050691 23424899320698180036076037)
        ·
          refine ⟨4392168622630908756764257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23424899320698180036076037 4392168622630908756764257)
          ·
            refine ⟨3294126466973181567573193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4392168622630908756764257 3294126466973181567573193)
            ·
              refine ⟨2470594850229886175679895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3294126466973181567573193 2470594850229886175679895)
              ·
                refine ⟨3705892275344829263519843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2470594850229886175679895 3705892275344829263519843)
                ·
                  refine ⟨5558838413017243895279765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3705892275344829263519843 5558838413017243895279765)
                  ·
                    refine ⟨260570550610183307591239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5558838413017243895279765 260570550610183307591239)
                    ·
                      rfl

theorem cell23_1522378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_1522378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522378 prefixEnd_1522378 := by exact prefixLift 1522378
  have htrace : WordTrace (prefixWord ++ tailWord_1522378) baseStart_1522378 baseEnd_1522378 := by
    simpa [prefixWord, tailWord_1522378, baseEnd_1522378] using wordTrace_append hprefix tailTrace_1522378
  have hstable : (prefixWord ++ tailWord_1522378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522378).length < 2 ^ (prefixWord ++ tailWord_1522378).sum := by decide
  have hdescent : baseEnd_1522378 < baseStart_1522378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522385 : List Nat := [1, 2, 2, 1, 2, 3, 3, 2, 3, 2, 2]
def baseStart_1522385 : Nat := 118140960795 + 1522385 * 2 ^ 59
def prefixEnd_1522385 : Nat := 4983230072969 + 3 ^ 40 * 1522385 * 2
def baseEnd_1522385 : Nat := 781715246195131395386185

theorem tailTrace_1522385 : CollatzResearch.WordTrace tailWord_1522385 prefixEnd_1522385 781715246195131395386185 := by
  unfold tailWord_1522385
  simp only [CollatzResearch.WordTrace]
  refine ⟨55525942589666622503240609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37017295059777748335493739 55525942589666622503240609)
  ·
    refine ⟨41644456942249966877430457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55525942589666622503240609 41644456942249966877430457)
    ·
      refine ⟨31233342706687475158072843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41644456942249966877430457 31233342706687475158072843)
      ·
        refine ⟨46850014060031212737109265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31233342706687475158072843 46850014060031212737109265)
        ·
          refine ⟨35137510545023409552831949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46850014060031212737109265 35137510545023409552831949)
          ·
            refine ⟨13176566454383778582311981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35137510545023409552831949 13176566454383778582311981)
            ·
              refine ⟨4941212420393916968366993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13176566454383778582311981 4941212420393916968366993)
              ·
                refine ⟨3705909315295437726275245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4941212420393916968366993 3705909315295437726275245)
                ·
                  refine ⟨1389715993235789147353217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3705909315295437726275245 1389715993235789147353217)
                  ·
                    refine ⟨1042286994926841860514913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1389715993235789147353217 1042286994926841860514913)
                    ·
                      refine ⟨781715246195131395386185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1042286994926841860514913 781715246195131395386185)
                      ·
                        rfl

theorem cell23_1522385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3, 2, 2].length) (baseStart_1522385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522385 prefixEnd_1522385 := by exact prefixLift 1522385
  have htrace : WordTrace (prefixWord ++ tailWord_1522385) baseStart_1522385 baseEnd_1522385 := by
    simpa [prefixWord, tailWord_1522385, baseEnd_1522385] using wordTrace_append hprefix tailTrace_1522385
  have hstable : (prefixWord ++ tailWord_1522385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522385).length < 2 ^ (prefixWord ++ tailWord_1522385).sum := by decide
  have hdescent : baseEnd_1522385 < baseStart_1522385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522389 : List Nat := [1, 3, 2, 5, 1, 2, 1, 1, 2, 3, 2]
def baseStart_1522389 : Nat := 118140960795 + 1522389 * 2 ^ 59
def prefixEnd_1522389 : Nat := 4983230072969 + 3 ^ 40 * 1522389 * 2
def baseEnd_1522389 : Nat := 781717300117749379736167

theorem tailTrace_1522389 : CollatzResearch.WordTrace tailWord_1522389 prefixEnd_1522389 781717300117749379736167 := by
  unfold tailWord_1522389
  simp only [CollatzResearch.WordTrace]
  refine ⟨55526088481652131186386221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37017392321101420790924147 55526088481652131186386221)
  ·
    refine ⟨20822283180619549194894833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55526088481652131186386221 20822283180619549194894833)
    ·
      refine ⟨15616712385464661896171125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20822283180619549194894833 15616712385464661896171125)
      ·
        refine ⟨1464066786137312052766043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15616712385464661896171125 1464066786137312052766043)
        ·
          refine ⟨2196100179205968079149065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1464066786137312052766043 2196100179205968079149065)
          ·
            refine ⟨1647075134404476059361799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2196100179205968079149065 1647075134404476059361799)
            ·
              refine ⟨2470612701606714089042699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1647075134404476059361799 2470612701606714089042699)
              ·
                refine ⟨3705919052410071133564049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2470612701606714089042699 3705919052410071133564049)
                ·
                  refine ⟨2779439289307553350173037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3705919052410071133564049 2779439289307553350173037)
                  ·
                    refine ⟨1042289733490332506314889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2779439289307553350173037 1042289733490332506314889)
                    ·
                      refine ⟨781717300117749379736167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1042289733490332506314889 781717300117749379736167)
                      ·
                        rfl

theorem cell23_1522389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_1522389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522389 prefixEnd_1522389 := by exact prefixLift 1522389
  have htrace : WordTrace (prefixWord ++ tailWord_1522389) baseStart_1522389 baseEnd_1522389 := by
    simpa [prefixWord, tailWord_1522389, baseEnd_1522389] using wordTrace_append hprefix tailTrace_1522389
  have hstable : (prefixWord ++ tailWord_1522389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522389).length < 2 ^ (prefixWord ++ tailWord_1522389).sum := by decide
  have hdescent : baseEnd_1522389 < baseStart_1522389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522405 : List Nat := [1, 3, 1, 4, 1, 3, 1, 3, 1, 2, 3]
def baseStart_1522405 : Nat := 118140960795 + 1522405 * 2 ^ 59
def prefixEnd_1522405 : Nat := 4983230072969 + 3 ^ 40 * 1522405 * 2
def baseEnd_1522405 : Nat := 781725515808221317136093

theorem tailTrace_1522405 : CollatzResearch.WordTrace tailWord_1522405 prefixEnd_1522405 781725515808221317136093 := by
  unfold tailWord_1522405
  simp only [CollatzResearch.WordTrace]
  refine ⟨55526672049594165918968669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37017781366396110612645779 55526672049594165918968669)
  ·
    refine ⟨20822502018597812219613251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55526672049594165918968669 20822502018597812219613251)
    ·
      refine ⟨31233753027896718329419877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20822502018597812219613251 31233753027896718329419877)
      ·
        refine ⟨5856328692730634686766227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31233753027896718329419877 5856328692730634686766227)
        ·
          refine ⟨8784493039095952030149341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5856328692730634686766227 8784493039095952030149341)
          ·
            refine ⟨3294184889660982011306003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8784493039095952030149341 3294184889660982011306003)
            ·
              refine ⟨4941277334491473016959005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3294184889660982011306003 4941277334491473016959005)
              ·
                refine ⟨1852979000434302381359627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4941277334491473016959005 1852979000434302381359627)
                ·
                  refine ⟨2779468500651453572039441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1852979000434302381359627 2779468500651453572039441)
                  ·
                    refine ⟨2084601375488590179029581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2779468500651453572039441 2084601375488590179029581)
                    ·
                      refine ⟨781725515808221317136093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2084601375488590179029581 781725515808221317136093)
                      ·
                        rfl

theorem cell23_1522405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_1522405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522405 prefixEnd_1522405 := by exact prefixLift 1522405
  have htrace : WordTrace (prefixWord ++ tailWord_1522405) baseStart_1522405 baseEnd_1522405 := by
    simpa [prefixWord, tailWord_1522405, baseEnd_1522405] using wordTrace_append hprefix tailTrace_1522405
  have hstable : (prefixWord ++ tailWord_1522405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522405).length < 2 ^ (prefixWord ++ tailWord_1522405).sum := by decide
  have hdescent : baseEnd_1522405 < baseStart_1522405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522441 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 2, 3, 4]
def baseStart_1522441 : Nat := 118140960795 + 1522441 * 2 ^ 59
def prefixEnd_1522441 : Nat := 4983230072969 + 3 ^ 40 * 1522441 * 2
def baseEnd_1522441 : Nat := 781744001111783176285927

theorem tailTrace_1522441 : CollatzResearch.WordTrace tailWord_1522441 prefixEnd_1522441 781744001111783176285927 := by
  unfold tailWord_1522441
  simp only [CollatzResearch.WordTrace]
  refine ⟨55527985077463744067279177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37018656718309162711519451 55527985077463744067279177)
  ·
    refine ⟨41645988808097808050459383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55527985077463744067279177 41645988808097808050459383)
    ·
      refine ⟨62468983212146712075689075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41645988808097808050459383 62468983212146712075689075)
      ·
        refine ⟨93703474818220068113533613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62468983212146712075689075 93703474818220068113533613)
        ·
          refine ⟨35138803056832525542575105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93703474818220068113533613 35138803056832525542575105)
          ·
            refine ⟨26354102292624394156931329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35138803056832525542575105 26354102292624394156931329)
            ·
              refine ⟨19765576719468295617698497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26354102292624394156931329 19765576719468295617698497)
              ·
                refine ⟨14824182539601221713273873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19765576719468295617698497 14824182539601221713273873)
                ·
                  refine ⟨11118136904700916284955405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14824182539601221713273873 11118136904700916284955405)
                  ·
                    refine ⟨4169301339262843606858277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11118136904700916284955405 4169301339262843606858277)
                    ·
                      refine ⟨781744001111783176285927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4169301339262843606858277 781744001111783176285927)
                      ·
                        rfl

theorem cell23_1522441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 3, 4].length) (baseStart_1522441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522441 prefixEnd_1522441 := by exact prefixLift 1522441
  have htrace : WordTrace (prefixWord ++ tailWord_1522441) baseStart_1522441 baseEnd_1522441 := by
    simpa [prefixWord, tailWord_1522441, baseEnd_1522441] using wordTrace_append hprefix tailTrace_1522441
  have hstable : (prefixWord ++ tailWord_1522441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522441).length < 2 ^ (prefixWord ++ tailWord_1522441).sum := by decide
  have hdescent : baseEnd_1522441 < baseStart_1522441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522509 : List Nat := [1, 6, 1, 2, 2, 1, 1, 2, 1, 4, 2]
def baseStart_1522509 : Nat := 118140960795 + 1522509 * 2 ^ 59
def prefixEnd_1522509 : Nat := 4983230072969 + 3 ^ 40 * 1522509 * 2
def baseEnd_1522509 : Nat := 781778917796288910235615

theorem tailTrace_1522509 : CollatzResearch.WordTrace tailWord_1522509 prefixEnd_1522509 781778917796288910235615 := by
  unfold tailWord_1522509
  simp only [CollatzResearch.WordTrace]
  refine ⟨55530465241217391680754581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37020310160811594453836387 55530465241217391680754581)
  ·
    refine ⟨2602990558182065235035371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55530465241217391680754581 2602990558182065235035371)
    ·
      refine ⟨3904485837273097852553057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2602990558182065235035371 3904485837273097852553057)
      ·
        refine ⟨2928364377954823389414793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3904485837273097852553057 2928364377954823389414793)
        ·
          refine ⟨2196273283466117542061095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2928364377954823389414793 2196273283466117542061095)
          ·
            refine ⟨3294409925199176313091643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2196273283466117542061095 3294409925199176313091643)
            ·
              refine ⟨4941614887798764469637465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3294409925199176313091643 4941614887798764469637465)
              ·
                refine ⟨3706211165849073352228099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4941614887798764469637465 3706211165849073352228099)
                ·
                  refine ⟨5559316748773610028342149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3706211165849073352228099 5559316748773610028342149)
                  ·
                    refine ⟨1042371890395051880314153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5559316748773610028342149 1042371890395051880314153)
                    ·
                      refine ⟨781778917796288910235615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1042371890395051880314153 781778917796288910235615)
                      ·
                        rfl

theorem cell23_1522509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_1522509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522509 prefixEnd_1522509 := by exact prefixLift 1522509
  have htrace : WordTrace (prefixWord ++ tailWord_1522509) baseStart_1522509 baseEnd_1522509 := by
    simpa [prefixWord, tailWord_1522509, baseEnd_1522509] using wordTrace_append hprefix tailTrace_1522509
  have hstable : (prefixWord ++ tailWord_1522509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522509).length < 2 ^ (prefixWord ++ tailWord_1522509).sum := by decide
  have hdescent : baseEnd_1522509 < baseStart_1522509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522528 : List Nat := [2, 1, 1, 3, 3, 1, 1, 4, 2, 5]
def baseStart_1522528 : Nat := 118140960795 + 1522528 * 2 ^ 59
def prefixEnd_1522528 : Nat := 4983230072969 + 3 ^ 40 * 1522528 * 2
def baseEnd_1522528 : Nat := 260596224642908111966009

theorem tailTrace_1522528 : CollatzResearch.WordTrace tailWord_1522528 prefixEnd_1522528 260596224642908111966009 := by
  unfold tailWord_1522528
  simp only [CollatzResearch.WordTrace]
  refine ⟨27765579114074278962848119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37020772152099038617130825 27765579114074278962848119)
  ·
    refine ⟨41648368671111418444272179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27765579114074278962848119 41648368671111418444272179)
    ·
      refine ⟨62472553006667127666408269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41648368671111418444272179 62472553006667127666408269)
      ·
        refine ⟨23427207377500172874903101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62472553006667127666408269 23427207377500172874903101)
        ·
          refine ⟨8785202766562564828088663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23427207377500172874903101 8785202766562564828088663)
          ·
            refine ⟨13177804149843847242132995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8785202766562564828088663 13177804149843847242132995)
            ·
              refine ⟨19766706224765770863199493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13177804149843847242132995 19766706224765770863199493)
              ·
                refine ⟨3706257417143582036849905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19766706224765770863199493 3706257417143582036849905)
                ·
                  refine ⟨2779693062857686527637429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3706257417143582036849905 2779693062857686527637429)
                  ·
                    refine ⟨260596224642908111966009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2779693062857686527637429 260596224642908111966009)
                    ·
                      rfl

theorem cell23_1522528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 2, 5].length) (baseStart_1522528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522528 prefixEnd_1522528 := by exact prefixLift 1522528
  have htrace : WordTrace (prefixWord ++ tailWord_1522528) baseStart_1522528 baseEnd_1522528 := by
    simpa [prefixWord, tailWord_1522528, baseEnd_1522528] using wordTrace_append hprefix tailTrace_1522528
  have hstable : (prefixWord ++ tailWord_1522528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522528).length < 2 ^ (prefixWord ++ tailWord_1522528).sum := by decide
  have hdescent : baseEnd_1522528 < baseStart_1522528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522532 : List Nat := [2, 3, 1, 1, 4, 1, 4, 2, 5]
def baseStart_1522532 : Nat := 118140960795 + 1522532 * 2 ^ 59
def prefixEnd_1522532 : Nat := 4983230072969 + 3 ^ 40 * 1522532 * 2
def baseEnd_1522532 : Nat := 86865636427926924472001

theorem tailTrace_1522532 : CollatzResearch.WordTrace tailWord_1522532 prefixEnd_1522532 86865636427926924472001 := by
  unfold tailWord_1522532
  simp only [CollatzResearch.WordTrace]
  refine ⟨27765652060067033304420925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37020869413422711072561233 27765652060067033304420925)
  ·
    refine ⟨10412119522525137489157847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27765652060067033304420925 10412119522525137489157847)
    ·
      refine ⟨15618179283787706233736771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10412119522525137489157847 15618179283787706233736771)
      ·
        refine ⟨23427268925681559350605157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15618179283787706233736771 23427268925681559350605157)
        ·
          refine ⟨4392612923565292378238467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23427268925681559350605157 4392612923565292378238467)
          ·
            refine ⟨6588919385347938567357701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4392612923565292378238467 6588919385347938567357701)
            ·
              refine ⟨1235422384752738481379569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6588919385347938567357701 1235422384752738481379569)
              ·
                refine ⟨926566788564553861034677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1235422384752738481379569 926566788564553861034677)
                ·
                  refine ⟨86865636427926924472001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 926566788564553861034677 86865636427926924472001)
                  ·
                    rfl

theorem cell23_1522532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2, 5].length) (baseStart_1522532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522532 prefixEnd_1522532 := by exact prefixLift 1522532
  have htrace : WordTrace (prefixWord ++ tailWord_1522532) baseStart_1522532 baseEnd_1522532 := by
    simpa [prefixWord, tailWord_1522532, baseEnd_1522532] using wordTrace_append hprefix tailTrace_1522532
  have hstable : (prefixWord ++ tailWord_1522532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522532).length < 2 ^ (prefixWord ++ tailWord_1522532).sum := by decide
  have hdescent : baseEnd_1522532 < baseStart_1522532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522535 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 2, 5, 2]
def baseStart_1522535 : Nat := 118140960795 + 1522535 * 2 ^ 59
def prefixEnd_1522535 : Nat := 4983230072969 + 3 ^ 40 * 1522535 * 2
def baseEnd_1522535 : Nat := 781792268293305808510495

theorem tailTrace_1522535 : CollatzResearch.WordTrace tailWord_1522535 prefixEnd_1522535 781792268293305808510495 := by
  unfold tailWord_1522535
  simp only [CollatzResearch.WordTrace]
  refine ⟨55531413539123198121201059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37020942359415465414134039 55531413539123198121201059)
  ·
    refine ⟨83297120308684797181801589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55531413539123198121201059 83297120308684797181801589)
    ·
      refine ⟨7809105028939199735793899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83297120308684797181801589 7809105028939199735793899)
      ·
        refine ⟨11713657543408799603690849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7809105028939199735793899 11713657543408799603690849)
        ·
          refine ⟨8785243157556599702768137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11713657543408799603690849 8785243157556599702768137)
          ·
            refine ⟨6588932368167449777076103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8785243157556599702768137 6588932368167449777076103)
            ·
              refine ⟨9883398552251174665614155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6588932368167449777076103 9883398552251174665614155)
              ·
                refine ⟨14825097828376761998421233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9883398552251174665614155 14825097828376761998421233)
                ·
                  refine ⟨11118823371282571498815925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14825097828376761998421233 11118823371282571498815925)
                  ·
                    refine ⟨1042389691057741078013993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11118823371282571498815925 1042389691057741078013993)
                    ·
                      refine ⟨781792268293305808510495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1042389691057741078013993 781792268293305808510495)
                      ·
                        rfl

theorem cell23_1522535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_1522535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522535 prefixEnd_1522535 := by exact prefixLift 1522535
  have htrace : WordTrace (prefixWord ++ tailWord_1522535) baseStart_1522535 baseEnd_1522535 := by
    simpa [prefixWord, tailWord_1522535, baseEnd_1522535] using wordTrace_append hprefix tailTrace_1522535
  have hstable : (prefixWord ++ tailWord_1522535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522535).length < 2 ^ (prefixWord ++ tailWord_1522535).sum := by decide
  have hdescent : baseEnd_1522535 < baseStart_1522535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522542 : List Nat := [4, 1, 2, 3, 2, 1, 1, 1, 2, 3, 3]
def baseStart_1522542 : Nat := 118140960795 + 1522542 * 2 ^ 59
def prefixEnd_1522542 : Nat := 4983230072969 + 3 ^ 40 * 1522542 * 2
def baseEnd_1522542 : Nat := 781795862657887281122963

theorem tailTrace_1522542 : CollatzResearch.WordTrace tailWord_1522542 prefixEnd_1522542 781795862657887281122963 := by
  unfold tailWord_1522542
  simp only [CollatzResearch.WordTrace]
  refine ⟨6941458606262229789588235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37021112566731892211137253 6941458606262229789588235)
  ·
    refine ⟨10412187909393344684382353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6941458606262229789588235 10412187909393344684382353)
    ·
      refine ⟨7809140932045008513286765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10412187909393344684382353 7809140932045008513286765)
      ·
        refine ⟨2928427849516878192482537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7809140932045008513286765 2928427849516878192482537)
        ·
          refine ⟨2196320887137658644361903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2928427849516878192482537 2196320887137658644361903)
          ·
            refine ⟨3294481330706487966542855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2196320887137658644361903 3294481330706487966542855)
            ·
              refine ⟨4941721996059731949814283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3294481330706487966542855 4941721996059731949814283)
              ·
                refine ⟨7412582994089597924721425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4941721996059731949814283 7412582994089597924721425)
                ·
                  refine ⟨5559437245567198443541069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7412582994089597924721425 5559437245567198443541069)
                  ·
                    refine ⟨2084788967087699416327901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5559437245567198443541069 2084788967087699416327901)
                    ·
                      refine ⟨781795862657887281122963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2084788967087699416327901 781795862657887281122963)
                      ·
                        rfl

theorem cell23_1522542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_1522542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522542 prefixEnd_1522542 := by exact prefixLift 1522542
  have htrace : WordTrace (prefixWord ++ tailWord_1522542) baseStart_1522542 baseEnd_1522542 := by
    simpa [prefixWord, tailWord_1522542, baseEnd_1522542] using wordTrace_append hprefix tailTrace_1522542
  have hstable : (prefixWord ++ tailWord_1522542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522542).length < 2 ^ (prefixWord ++ tailWord_1522542).sum := by decide
  have hdescent : baseEnd_1522542 < baseStart_1522542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522565 : List Nat := [1, 3, 1, 1, 3, 3, 3, 1, 2, 1, 4]
def baseStart_1522565 : Nat := 118140960795 + 1522565 * 2 ^ 59
def prefixEnd_1522565 : Nat := 4983230072969 + 3 ^ 40 * 1522565 * 2
def baseEnd_1522565 : Nat := 781807672712940691135357

theorem tailTrace_1522565 : CollatzResearch.WordTrace tailWord_1522565 prefixEnd_1522565 781807672712940691135357 := by
  unfold tailWord_1522565
  simp only [CollatzResearch.WordTrace]
  refine ⟨55532507729014513244793149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37021671819343008829862099 55532507729014513244793149)
  ·
    refine ⟨20824690398380442466797431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55532507729014513244793149 20824690398380442466797431)
    ·
      refine ⟨31237035597570663700196147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20824690398380442466797431 31237035597570663700196147)
      ·
        refine ⟨46855553396355995550294221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31237035597570663700196147 46855553396355995550294221)
        ·
          refine ⟨17570832523633498331360333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46855553396355995550294221 17570832523633498331360333)
          ·
            refine ⟨6589062196362561874260125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17570832523633498331360333 6589062196362561874260125)
            ·
              refine ⟨2470898323635960702847547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6589062196362561874260125 2470898323635960702847547)
              ·
                refine ⟨3706347485453941054271321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2470898323635960702847547 3706347485453941054271321)
                ·
                  refine ⟨2779760614090455790703491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3706347485453941054271321 2779760614090455790703491)
                  ·
                    refine ⟨4169640921135683686055237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2779760614090455790703491 4169640921135683686055237)
                    ·
                      refine ⟨781807672712940691135357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4169640921135683686055237 781807672712940691135357)
                      ·
                        rfl

theorem cell23_1522565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 1, 4].length) (baseStart_1522565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522565 prefixEnd_1522565 := by exact prefixLift 1522565
  have htrace : WordTrace (prefixWord ++ tailWord_1522565) baseStart_1522565 baseEnd_1522565 := by
    simpa [prefixWord, tailWord_1522565, baseEnd_1522565] using wordTrace_append hprefix tailTrace_1522565
  have hstable : (prefixWord ++ tailWord_1522565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522565).length < 2 ^ (prefixWord ++ tailWord_1522565).sum := by decide
  have hdescent : baseEnd_1522565 < baseStart_1522565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522592 : List Nat := [2, 1, 1, 4, 1, 1, 4, 4, 1, 4]
def baseStart_1522592 : Nat := 118140960795 + 1522592 * 2 ^ 59
def prefixEnd_1522592 : Nat := 4983230072969 + 3 ^ 40 * 1522592 * 2
def baseEnd_1522592 : Nat := 260607178896870695165911

theorem tailTrace_1522592 : CollatzResearch.WordTrace tailWord_1522592 prefixEnd_1522592 260607178896870695165911 := by
  unfold tailWord_1522592
  simp only [CollatzResearch.WordTrace]
  refine ⟨27766746249958348428013015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37022328333277797904017353 27766746249958348428013015)
  ·
    refine ⟨41650119374937522642019523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27766746249958348428013015 41650119374937522642019523)
    ·
      refine ⟨62475179062406283963029285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41650119374937522642019523 62475179062406283963029285)
      ·
        refine ⟨11714096074201178243067991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62475179062406283963029285 11714096074201178243067991)
        ·
          refine ⟨17571144111301767364601987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11714096074201178243067991 17571144111301767364601987)
          ·
            refine ⟨26356716166952651046902981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17571144111301767364601987 26356716166952651046902981)
            ·
              refine ⟨4941884281303622071294309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26356716166952651046902981 4941884281303622071294309)
              ·
                refine ⟨926603302744429138367683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4941884281303622071294309 926603302744429138367683)
                ·
                  refine ⟨1389904954116643707551525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 926603302744429138367683 1389904954116643707551525)
                  ·
                    refine ⟨260607178896870695165911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1389904954116643707551525 260607178896870695165911)
                    ·
                      rfl

theorem cell23_1522592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4, 1, 4].length) (baseStart_1522592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522592 prefixEnd_1522592 := by exact prefixLift 1522592
  have htrace : WordTrace (prefixWord ++ tailWord_1522592) baseStart_1522592 baseEnd_1522592 := by
    simpa [prefixWord, tailWord_1522592, baseEnd_1522592] using wordTrace_append hprefix tailTrace_1522592
  have hstable : (prefixWord ++ tailWord_1522592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522592).length < 2 ^ (prefixWord ++ tailWord_1522592).sum := by decide
  have hdescent : baseEnd_1522592 < baseStart_1522592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522635 : List Nat := [1, 1, 1, 1, 3, 5, 2, 3, 1, 5]
def baseStart_1522635 : Nat := 118140960795 + 1522635 * 2 ^ 59
def prefixEnd_1522635 : Nat := 4983230072969 + 3 ^ 40 * 1522635 * 2
def baseEnd_1522635 : Nat := 260614538786251805753345

theorem tailTrace_1522635 : CollatzResearch.WordTrace tailWord_1522635 prefixEnd_1522635 260614538786251805753345 := by
  unfold tailWord_1522635
  simp only [CollatzResearch.WordTrace]
  refine ⟨55535060838760915199841359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37023373892507276799894239 55535060838760915199841359)
  ·
    refine ⟨83302591258141372799762039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55535060838760915199841359 83302591258141372799762039)
    ·
      refine ⟨124953886887212059199643059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83302591258141372799762039 124953886887212059199643059)
      ·
        refine ⟨187430830330818088799464589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124953886887212059199643059 187430830330818088799464589)
        ·
          refine ⟨70286561374056783299799221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187430830330818088799464589 70286561374056783299799221)
          ·
            refine ⟨6589365128817823434356177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70286561374056783299799221 6589365128817823434356177)
            ·
              refine ⟨4942023846613367575767133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6589365128817823434356177 4942023846613367575767133)
              ·
                refine ⟨1853258942480012840912675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4942023846613367575767133 1853258942480012840912675)
                ·
                  refine ⟨2779888413720019261369013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1853258942480012840912675 2779888413720019261369013)
                  ·
                    refine ⟨260614538786251805753345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2779888413720019261369013 260614538786251805753345)
                    ·
                      rfl

theorem cell23_1522635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 5].length) (baseStart_1522635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522635 prefixEnd_1522635 := by exact prefixLift 1522635
  have htrace : WordTrace (prefixWord ++ tailWord_1522635) baseStart_1522635 baseEnd_1522635 := by
    simpa [prefixWord, tailWord_1522635, baseEnd_1522635] using wordTrace_append hprefix tailTrace_1522635
  have hstable : (prefixWord ++ tailWord_1522635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522635).length < 2 ^ (prefixWord ++ tailWord_1522635).sum := by decide
  have hdescent : baseEnd_1522635 < baseStart_1522635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522649 : List Nat := [1, 2, 1, 2, 5, 3, 1, 1, 3, 1, 3]
def baseStart_1522649 : Nat := 118140960795 + 1522649 * 2 ^ 59
def prefixEnd_1522649 : Nat := 4983230072969 + 3 ^ 40 * 1522649 * 2
def baseEnd_1522649 : Nat := 781850805087918362484971

theorem tailTrace_1522649 : CollatzResearch.WordTrace tailWord_1522649 prefixEnd_1522649 781850805087918362484971 := by
  unfold tailWord_1522649
  simp only [CollatzResearch.WordTrace]
  refine ⟨55535571460710195590851001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37023714307140130393900667 55535571460710195590851001)
  ·
    refine ⟨41651678595532646693138251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55535571460710195590851001 41651678595532646693138251)
    ·
      refine ⟨62477517893298970039707377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41651678595532646693138251 62477517893298970039707377)
      ·
        refine ⟨46858138419974227529780533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62477517893298970039707377 46858138419974227529780533)
        ·
          refine ⟨4392950476872583830916925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46858138419974227529780533 4392950476872583830916925)
          ·
            refine ⟨1647356428827218936593847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4392950476872583830916925 1647356428827218936593847)
            ·
              refine ⟨2471034643240828404890771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1647356428827218936593847 2471034643240828404890771)
              ·
                refine ⟨3706551964861242607336157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2471034643240828404890771 3706551964861242607336157)
                ·
                  refine ⟨1389956986822965977751059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3706551964861242607336157 1389956986822965977751059)
                  ·
                    refine ⟨2084935480234448966626589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1389956986822965977751059 2084935480234448966626589)
                    ·
                      refine ⟨781850805087918362484971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2084935480234448966626589 781850805087918362484971)
                      ·
                        rfl

theorem cell23_1522649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3, 1, 3].length) (baseStart_1522649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522649 prefixEnd_1522649 := by exact prefixLift 1522649
  have htrace : WordTrace (prefixWord ++ tailWord_1522649) baseStart_1522649 baseEnd_1522649 := by
    simpa [prefixWord, tailWord_1522649, baseEnd_1522649] using wordTrace_append hprefix tailTrace_1522649
  have hstable : (prefixWord ++ tailWord_1522649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522649).length < 2 ^ (prefixWord ++ tailWord_1522649).sum := by decide
  have hdescent : baseEnd_1522649 < baseStart_1522649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522672 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 5, 2, 2]
def baseStart_1522672 : Nat := 118140960795 + 1522672 * 2 ^ 59
def prefixEnd_1522672 : Nat := 4983230072969 + 3 ^ 40 * 1522672 * 2
def baseEnd_1522672 : Nat := 781862615142971772497365

theorem tailTrace_1522672 : CollatzResearch.WordTrace tailWord_1522672 prefixEnd_1522672 781862615142971772497365 := by
  unfold tailWord_1522672
  simp only [CollatzResearch.WordTrace]
  refine ⟨27768205169813435259469135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37024273559751247012625513 27768205169813435259469135)
  ·
    refine ⟨41652307754720152889203703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27768205169813435259469135 41652307754720152889203703)
    ·
      refine ⟨62478461632080229333805555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41652307754720152889203703 62478461632080229333805555)
      ·
        refine ⟨93717692448120344000708333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62478461632080229333805555 93717692448120344000708333)
        ·
          refine ⟨35144134668045129000265625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93717692448120344000708333 35144134668045129000265625)
          ·
            refine ⟨26358101001033846750199219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35144134668045129000265625 26358101001033846750199219)
            ·
              refine ⟨39537151501550770125298829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26358101001033846750199219 39537151501550770125298829)
              ·
                refine ⟨14826431813081538796987061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39537151501550770125298829 14826431813081538796987061)
                ·
                  refine ⟨1389977982476394262217537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14826431813081538796987061 1389977982476394262217537)
                  ·
                    refine ⟨1042483486857295696663153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1389977982476394262217537 1042483486857295696663153)
                    ·
                      refine ⟨781862615142971772497365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1042483486857295696663153 781862615142971772497365)
                      ·
                        rfl

theorem cell23_1522672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 5, 2, 2].length) (baseStart_1522672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522672 prefixEnd_1522672 := by exact prefixLift 1522672
  have htrace : WordTrace (prefixWord ++ tailWord_1522672) baseStart_1522672 baseEnd_1522672 := by
    simpa [prefixWord, tailWord_1522672, baseEnd_1522672] using wordTrace_append hprefix tailTrace_1522672
  have hstable : (prefixWord ++ tailWord_1522672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522672).length < 2 ^ (prefixWord ++ tailWord_1522672).sum := by decide
  have hdescent : baseEnd_1522672 < baseStart_1522672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522686 : List Nat := [4, 2, 2, 2, 2, 1, 3, 1, 1, 5]
def baseStart_1522686 : Nat := 118140960795 + 1522686 * 2 ^ 59
def prefixEnd_1522686 : Nat := 4983230072969 + 3 ^ 40 * 1522686 * 2
def baseEnd_1522686 : Nat := 260623267957378239240767

theorem tailTrace_1522686 : CollatzResearch.WordTrace tailWord_1522686 prefixEnd_1522686 260623267957378239240767 := by
  unfold tailWord_1522686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6942115120197018863743489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37024613974384100606631941 6942115120197018863743489)
  ·
    refine ⟨5206586340147764147807617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6942115120197018863743489 5206586340147764147807617)
    ·
      refine ⟨3904939755110823110855713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5206586340147764147807617 3904939755110823110855713)
      ·
        refine ⟨2928704816333117333141785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3904939755110823110855713 2928704816333117333141785)
        ·
          refine ⟨2196528612249837999856339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2928704816333117333141785 2196528612249837999856339)
          ·
            refine ⟨3294792918374756999784509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2196528612249837999856339 3294792918374756999784509)
            ·
              refine ⟨1235547344390533874919191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3294792918374756999784509 1235547344390533874919191)
              ·
                refine ⟨1853321016585800812378787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1235547344390533874919191 1853321016585800812378787)
                ·
                  refine ⟨2779981524878701218568181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1853321016585800812378787 2779981524878701218568181)
                  ·
                    refine ⟨260623267957378239240767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2779981524878701218568181 260623267957378239240767)
                    ·
                      rfl

theorem cell23_1522686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_1522686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522686 prefixEnd_1522686 := by exact prefixLift 1522686
  have htrace : WordTrace (prefixWord ++ tailWord_1522686) baseStart_1522686 baseEnd_1522686 := by
    simpa [prefixWord, tailWord_1522686, baseEnd_1522686] using wordTrace_append hprefix tailTrace_1522686
  have hstable : (prefixWord ++ tailWord_1522686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522686).length < 2 ^ (prefixWord ++ tailWord_1522686).sum := by decide
  have hdescent : baseEnd_1522686 < baseStart_1522686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522689 : List Nat := [1, 2, 4, 1, 2, 3, 3, 1, 1, 1, 4]
def baseStart_1522689 : Nat := 118140960795 + 1522689 * 2 ^ 59
def prefixEnd_1522689 : Nat := 4983230072969 + 3 ^ 40 * 1522689 * 2
def baseEnd_1522689 : Nat := 781871344314098205984787

theorem tailTrace_1522689 : CollatzResearch.WordTrace tailWord_1522689 prefixEnd_1522689 781871344314098205984787 := by
  unfold tailWord_1522689
  simp only [CollatzResearch.WordTrace]
  refine ⟨55537030380565282422307121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37024686920376854948204747 55537030380565282422307121)
  ·
    refine ⟨41652772785423961816730341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55537030380565282422307121 41652772785423961816730341)
    ·
      refine ⟨7809894897266992840636939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41652772785423961816730341 7809894897266992840636939)
      ·
        refine ⟨11714842345900489260955409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7809894897266992840636939 11714842345900489260955409)
        ·
          refine ⟨8786131759425366945716557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11714842345900489260955409 8786131759425366945716557)
          ·
            refine ⟨3294799409784512604643709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8786131759425366945716557 3294799409784512604643709)
            ·
              refine ⟨1235549778669192226741391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3294799409784512604643709 1235549778669192226741391)
              ·
                refine ⟨1853324668003788340112087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1235549778669192226741391 1853324668003788340112087)
                ·
                  refine ⟨2779987002005682510168131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1853324668003788340112087 2779987002005682510168131)
                  ·
                    refine ⟨4169980503008523765252197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2779987002005682510168131 4169980503008523765252197)
                    ·
                      refine ⟨781871344314098205984787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4169980503008523765252197 781871344314098205984787)
                      ·
                        rfl

theorem cell23_1522689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_1522689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522689 prefixEnd_1522689 := by exact prefixLift 1522689
  have htrace : WordTrace (prefixWord ++ tailWord_1522689) baseStart_1522689 baseEnd_1522689 := by
    simpa [prefixWord, tailWord_1522689, baseEnd_1522689] using wordTrace_append hprefix tailTrace_1522689
  have hstable : (prefixWord ++ tailWord_1522689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522689).length < 2 ^ (prefixWord ++ tailWord_1522689).sum := by decide
  have hdescent : baseEnd_1522689 < baseStart_1522689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522722 : List Nat := [3, 3, 1, 1, 1, 3, 1, 3, 1, 3, 3]
def baseStart_1522722 : Nat := 118140960795 + 1522722 * 2 ^ 59
def prefixEnd_1522722 : Nat := 4983230072969 + 3 ^ 40 * 1522722 * 2
def baseEnd_1522722 : Nat := 781888289175696576872135

theorem tailTrace_1522722 : CollatzResearch.WordTrace tailWord_1522722 prefixEnd_1522722 781888289175696576872135 := by
  unfold tailWord_1522722
  simp only [CollatzResearch.WordTrace]
  refine ⟨13884558497361432264564605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37025489326297152705505613 13884558497361432264564605)
  ·
    refine ⟨5206709436510537099211727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13884558497361432264564605 5206709436510537099211727)
    ·
      refine ⟨7810064154765805648817591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5206709436510537099211727 7810064154765805648817591)
      ·
        refine ⟨11715096232148708473226387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7810064154765805648817591 11715096232148708473226387)
        ·
          refine ⟨17572644348223062709839581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11715096232148708473226387 17572644348223062709839581)
          ·
            refine ⟨6589741630583648516189843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17572644348223062709839581 6589741630583648516189843)
            ·
              refine ⟨9884612445875472774284765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6589741630583648516189843 9884612445875472774284765)
              ·
                refine ⟨3706729667203302290356787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9884612445875472774284765 3706729667203302290356787)
                ·
                  refine ⟨5560094500804953435535181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3706729667203302290356787 5560094500804953435535181)
                  ·
                    refine ⟨2085035437801857538325693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5560094500804953435535181 2085035437801857538325693)
                    ·
                      refine ⟨781888289175696576872135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2085035437801857538325693 781888289175696576872135)
                      ·
                        rfl

theorem cell23_1522722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_1522722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522722 prefixEnd_1522722 := by exact prefixLift 1522722
  have htrace : WordTrace (prefixWord ++ tailWord_1522722) baseStart_1522722 baseEnd_1522722 := by
    simpa [prefixWord, tailWord_1522722, baseEnd_1522722] using wordTrace_append hprefix tailTrace_1522722
  have hstable : (prefixWord ++ tailWord_1522722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522722).length < 2 ^ (prefixWord ++ tailWord_1522722).sum := by decide
  have hdescent : baseEnd_1522722 < baseStart_1522722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522732 : List Nat := [2, 2, 1, 1, 1, 2, 3, 3, 3, 3, 2]
def baseStart_1522732 : Nat := 118140960795 + 1522732 * 2 ^ 59
def prefixEnd_1522732 : Nat := 4983230072969 + 3 ^ 40 * 1522732 * 2
def baseEnd_1522732 : Nat := 781893423982241537747089

theorem tailTrace_1522732 : CollatzResearch.WordTrace tailWord_1522732 prefixEnd_1522732 781893423982241537747089 := by
  unfold tailWord_1522732
  simp only [CollatzResearch.WordTrace]
  refine ⟨27769299359704750383061225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37025732479606333844081633 27769299359704750383061225)
  ·
    refine ⟨20826974519778562787295919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27769299359704750383061225 20826974519778562787295919)
    ·
      refine ⟨31240461779667844180943879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20826974519778562787295919 31240461779667844180943879)
      ·
        refine ⟨46860692669501766271415819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31240461779667844180943879 46860692669501766271415819)
        ·
          refine ⟨70291039004252649407123729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46860692669501766271415819 70291039004252649407123729)
          ·
            refine ⟨52718279253189487055342797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70291039004252649407123729 52718279253189487055342797)
            ·
              refine ⟨19769354719946057645753549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52718279253189487055342797 19769354719946057645753549)
              ·
                refine ⟨7413508019979771617157581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19769354719946057645753549 7413508019979771617157581)
                ·
                  refine ⟨2780065507492414356434093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7413508019979771617157581 2780065507492414356434093)
                  ·
                    refine ⟨1042524565309655383662785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2780065507492414356434093 1042524565309655383662785)
                    ·
                      refine ⟨781893423982241537747089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1042524565309655383662785 781893423982241537747089)
                      ·
                        rfl

theorem cell23_1522732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 3, 2].length) (baseStart_1522732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522732 prefixEnd_1522732 := by exact prefixLift 1522732
  have htrace : WordTrace (prefixWord ++ tailWord_1522732) baseStart_1522732 baseEnd_1522732 := by
    simpa [prefixWord, tailWord_1522732, baseEnd_1522732] using wordTrace_append hprefix tailTrace_1522732
  have hstable : (prefixWord ++ tailWord_1522732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522732).length < 2 ^ (prefixWord ++ tailWord_1522732).sum := by decide
  have hdescent : baseEnd_1522732 < baseStart_1522732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522740 : List Nat := [2, 5, 1, 2, 1, 2, 2, 3, 1, 2, 2]
def baseStart_1522740 : Nat := 118140960795 + 1522740 * 2 ^ 59
def prefixEnd_1522740 : Nat := 4983230072969 + 3 ^ 40 * 1522740 * 2
def baseEnd_1522740 : Nat := 781897531827477506447053

theorem tailTrace_1522740 : CollatzResearch.WordTrace tailWord_1522740 prefixEnd_1522740 781897531827477506447053 := by
  unfold tailWord_1522740
  simp only [CollatzResearch.WordTrace]
  refine ⟨27769445251690259066206837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37025927002253678754942449 27769445251690259066206837)
  ·
    refine ⟨2603385492345961787456891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27769445251690259066206837 2603385492345961787456891)
    ·
      refine ⟨3905078238518942681185337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2603385492345961787456891 3905078238518942681185337)
      ·
        refine ⟨2928808678889207010889003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3905078238518942681185337 2928808678889207010889003)
        ·
          refine ⟨4393213018333810516333505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2928808678889207010889003 4393213018333810516333505)
          ·
            refine ⟨3294909763750357887250129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4393213018333810516333505 3294909763750357887250129)
            ·
              refine ⟨2471182322812768415437597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3294909763750357887250129 2471182322812768415437597)
              ·
                refine ⟨926693371054788155789099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2471182322812768415437597 926693371054788155789099)
                ·
                  refine ⟨1390040056582182233683649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 926693371054788155789099 1390040056582182233683649)
                  ·
                    refine ⟨1042530042436636675262737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1390040056582182233683649 1042530042436636675262737)
                    ·
                      refine ⟨781897531827477506447053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1042530042436636675262737 781897531827477506447053)
                      ·
                        rfl

theorem cell23_1522740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_1522740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522740 prefixEnd_1522740 := by exact prefixLift 1522740
  have htrace : WordTrace (prefixWord ++ tailWord_1522740) baseStart_1522740 baseEnd_1522740 := by
    simpa [prefixWord, tailWord_1522740, baseEnd_1522740] using wordTrace_append hprefix tailTrace_1522740
  have hstable : (prefixWord ++ tailWord_1522740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522740).length < 2 ^ (prefixWord ++ tailWord_1522740).sum := by decide
  have hdescent : baseEnd_1522740 < baseStart_1522740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522762 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 3, 4, 2]
def baseStart_1522762 : Nat := 118140960795 + 1522762 * 2 ^ 59
def prefixEnd_1522762 : Nat := 4983230072969 + 3 ^ 40 * 1522762 * 2
def baseEnd_1522762 : Nat := 781908828401876420371951

theorem tailTrace_1522762 : CollatzResearch.WordTrace tailWord_1522762 prefixEnd_1522762 781908828401876420371951 := by
  unfold tailWord_1522762
  simp only [CollatzResearch.WordTrace]
  refine ⟨13884923227325203972428635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37026461939533877259809693 13884923227325203972428635)
  ·
    refine ⟨20827384840987805958642953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13884923227325203972428635 20827384840987805958642953)
    ·
      refine ⟨15620538630740854468982215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20827384840987805958642953 15620538630740854468982215)
      ·
        refine ⟨23430807946111281703473323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15620538630740854468982215 23430807946111281703473323)
        ·
          refine ⟨35146211919166922555209985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23430807946111281703473323 35146211919166922555209985)
          ·
            refine ⟨26359658939375191916407489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35146211919166922555209985 26359658939375191916407489)
            ·
              refine ⟨19769744204531393937305617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26359658939375191916407489 19769744204531393937305617)
              ·
                refine ⟨14827308153398545452979213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19769744204531393937305617 14827308153398545452979213)
                ·
                  refine ⟨5560240557524454544867205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14827308153398545452979213 5560240557524454544867205)
                  ·
                    refine ⟨1042545104535835227162601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5560240557524454544867205 1042545104535835227162601)
                    ·
                      refine ⟨781908828401876420371951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1042545104535835227162601 781908828401876420371951)
                      ·
                        rfl

theorem cell23_1522762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 3, 4, 2].length) (baseStart_1522762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522762 prefixEnd_1522762 := by exact prefixLift 1522762
  have htrace : WordTrace (prefixWord ++ tailWord_1522762) baseStart_1522762 baseEnd_1522762 := by
    simpa [prefixWord, tailWord_1522762, baseEnd_1522762] using wordTrace_append hprefix tailTrace_1522762
  have hstable : (prefixWord ++ tailWord_1522762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522762).length < 2 ^ (prefixWord ++ tailWord_1522762).sum := by decide
  have hdescent : baseEnd_1522762 < baseStart_1522762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522785 : List Nat := [1, 2, 3, 1, 1, 2, 4, 2, 7]
def baseStart_1522785 : Nat := 118140960795 + 1522785 * 2 ^ 59
def prefixEnd_1522785 : Nat := 4983230072969 + 3 ^ 40 * 1522785 * 2
def baseEnd_1522785 : Nat := 86880070939658870042705

theorem tailTrace_1522785 : CollatzResearch.WordTrace tailWord_1522785 prefixEnd_1522785 86880070939658870042705 := by
  unfold tailWord_1522785
  simp only [CollatzResearch.WordTrace]
  refine ⟨55540531788217490817801809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37027021192144993878534539 55540531788217490817801809)
  ·
    refine ⟨41655398841163118113351357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55540531788217490817801809 41655398841163118113351357)
    ·
      refine ⟨15620774565436169292506759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41655398841163118113351357 15620774565436169292506759)
      ·
        refine ⟨23431161848154253938760139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15620774565436169292506759 23431161848154253938760139)
        ·
          refine ⟨35146742772231380908140209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23431161848154253938760139 35146742772231380908140209)
          ·
            refine ⟨26360057079173535681105157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35146742772231380908140209 26360057079173535681105157)
            ·
              refine ⟨4942510702345037940207217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26360057079173535681105157 4942510702345037940207217)
              ·
                refine ⟨3706883026758778455155413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4942510702345037940207217 3706883026758778455155413)
                ·
                  refine ⟨86880070939658870042705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3706883026758778455155413 86880070939658870042705)
                  ·
                    rfl

theorem cell23_1522785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 7].length) (baseStart_1522785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522785 prefixEnd_1522785 := by exact prefixLift 1522785
  have htrace : WordTrace (prefixWord ++ tailWord_1522785) baseStart_1522785 baseEnd_1522785 := by
    simpa [prefixWord, tailWord_1522785, baseEnd_1522785] using wordTrace_append hprefix tailTrace_1522785
  have hstable : (prefixWord ++ tailWord_1522785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522785).length < 2 ^ (prefixWord ++ tailWord_1522785).sum := by decide
  have hdescent : baseEnd_1522785 < baseStart_1522785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522819 : List Nat := [1, 1, 1, 3, 3, 2, 5, 2, 5]
def baseStart_1522819 : Nat := 118140960795 + 1522819 * 2 ^ 59
def prefixEnd_1522819 : Nat := 4983230072969 + 3 ^ 40 * 1522819 * 2
def baseEnd_1522819 : Nat := 86882010755464744151021

theorem tailTrace_1522819 : CollatzResearch.WordTrace tailWord_1522819 prefixEnd_1522819 86882010755464744151021 := by
  unfold tailWord_1522819
  simp only [CollatzResearch.WordTrace]
  refine ⟨55541771870094314624539511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37027847913396209749693007 55541771870094314624539511)
  ·
    refine ⟨83312657805141471936809267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55541771870094314624539511 83312657805141471936809267)
    ·
      refine ⟨124968986707712207905213901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83312657805141471936809267 124968986707712207905213901)
      ·
        refine ⟨46863370015392077964455213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124968986707712207905213901 46863370015392077964455213)
        ·
          refine ⟨17573763755772029236670705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46863370015392077964455213 17573763755772029236670705)
          ·
            refine ⟨13180322816829021927503029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17573763755772029236670705 13180322816829021927503029)
            ·
              refine ⟨1235655264077720805703409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13180322816829021927503029 1235655264077720805703409)
              ·
                refine ⟨926741448058290604277557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1235655264077720805703409 926741448058290604277557)
                ·
                  refine ⟨86882010755464744151021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 926741448058290604277557 86882010755464744151021)
                  ·
                    rfl

theorem cell23_1522819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2, 5].length) (baseStart_1522819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522819 prefixEnd_1522819 := by exact prefixLift 1522819
  have htrace : WordTrace (prefixWord ++ tailWord_1522819) baseStart_1522819 baseEnd_1522819 := by
    simpa [prefixWord, tailWord_1522819, baseEnd_1522819] using wordTrace_append hprefix tailTrace_1522819
  have hstable : (prefixWord ++ tailWord_1522819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522819).length < 2 ^ (prefixWord ++ tailWord_1522819).sum := by decide
  have hdescent : baseEnd_1522819 < baseStart_1522819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522825 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 1, 1, 7]
def baseStart_1522825 : Nat := 118140960795 + 1522825 * 2 ^ 59
def prefixEnd_1522825 : Nat := 4983230072969 + 3 ^ 40 * 1522825 * 2
def baseEnd_1522825 : Nat := 781941177683109673884161

theorem tailTrace_1522825 : CollatzResearch.WordTrace tailWord_1522825 prefixEnd_1522825 781941177683109673884161 := by
  unfold tailWord_1522825
  simp only [CollatzResearch.WordTrace]
  refine ⟨55541990708072577649257929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37027993805381718432838619 55541990708072577649257929)
  ·
    refine ⟨41656493031054433236943447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55541990708072577649257929 41656493031054433236943447)
    ·
      refine ⟨62484739546581649855415171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41656493031054433236943447 62484739546581649855415171)
      ·
        refine ⟨93727109319872474783122757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62484739546581649855415171 93727109319872474783122757)
        ·
          refine ⟨17573832997476089021835517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93727109319872474783122757 17573832997476089021835517)
          ·
            refine ⟨6590187374053533383188319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17573832997476089021835517 6590187374053533383188319)
            ·
              refine ⟨9885281061080300074782479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6590187374053533383188319 9885281061080300074782479)
              ·
                refine ⟨14827921591620450112173719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9885281061080300074782479 14827921591620450112173719)
                ·
                  refine ⟨22241882387430675168260579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14827921591620450112173719 22241882387430675168260579)
                  ·
                    refine ⟨33362823581146012752390869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22241882387430675168260579 33362823581146012752390869)
                    ·
                      refine ⟨781941177683109673884161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 33362823581146012752390869 781941177683109673884161)
                      ·
                        rfl

theorem cell23_1522825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 1, 7].length) (baseStart_1522825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522825 prefixEnd_1522825 := by exact prefixLift 1522825
  have htrace : WordTrace (prefixWord ++ tailWord_1522825) baseStart_1522825 baseEnd_1522825 := by
    simpa [prefixWord, tailWord_1522825, baseEnd_1522825] using wordTrace_append hprefix tailTrace_1522825
  have hstable : (prefixWord ++ tailWord_1522825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522825).length < 2 ^ (prefixWord ++ tailWord_1522825).sum := by decide
  have hdescent : baseEnd_1522825 < baseStart_1522825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522830 : List Nat := [4, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2]
def baseStart_1522830 : Nat := 118140960795 + 1522830 * 2 ^ 59
def prefixEnd_1522830 : Nat := 4983230072969 + 3 ^ 40 * 1522830 * 2
def baseEnd_1522830 : Nat := 781943745086382154321639

theorem tailTrace_1522830 : CollatzResearch.WordTrace tailWord_1522830 prefixEnd_1522830 781943745086382154321639 := by
  unfold tailWord_1522830
  simp only [CollatzResearch.WordTrace]
  refine ⟨6942771634131807937898743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37028115382036309002126629 6942771634131807937898743)
  ·
    refine ⟨10414157451197711906848115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6942771634131807937898743 10414157451197711906848115)
    ·
      refine ⟨15621236176796567860272173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10414157451197711906848115 15621236176796567860272173)
      ·
        refine ⟨5857963566298712947602065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15621236176796567860272173 5857963566298712947602065)
        ·
          refine ⟨4393472674724034710701549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5857963566298712947602065 4393472674724034710701549)
          ·
            refine ⟨1647552253021513016513081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4393472674724034710701549 1647552253021513016513081)
            ·
              refine ⟨1235664189766134762384811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1647552253021513016513081 1235664189766134762384811)
              ·
                refine ⟨1853496284649202143577217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1235664189766134762384811 1853496284649202143577217)
                ·
                  refine ⟨1390122213486901607682913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1853496284649202143577217 1390122213486901607682913)
                  ·
                    refine ⟨1042591660115176205762185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1390122213486901607682913 1042591660115176205762185)
                    ·
                      refine ⟨781943745086382154321639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1042591660115176205762185 781943745086382154321639)
                      ·
                        rfl

theorem cell23_1522830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_1522830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522830 prefixEnd_1522830 := by exact prefixLift 1522830
  have htrace : WordTrace (prefixWord ++ tailWord_1522830) baseStart_1522830 baseEnd_1522830 := by
    simpa [prefixWord, tailWord_1522830, baseEnd_1522830] using wordTrace_append hprefix tailTrace_1522830
  have hstable : (prefixWord ++ tailWord_1522830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522830).length < 2 ^ (prefixWord ++ tailWord_1522830).sum := by decide
  have hdescent : baseEnd_1522830 < baseStart_1522830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522835 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 4]
def baseStart_1522835 : Nat := 118140960795 + 1522835 * 2 ^ 59
def prefixEnd_1522835 : Nat := 4983230072969 + 3 ^ 40 * 1522835 * 2
def baseEnd_1522835 : Nat := 781946312489654634759115

theorem tailTrace_1522835 : CollatzResearch.WordTrace tailWord_1522835 prefixEnd_1522835 781946312489654634759115 := by
  unfold tailWord_1522835
  simp only [CollatzResearch.WordTrace]
  refine ⟨55542355438036349357121959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37028236958690899571414639 55542355438036349357121959)
  ·
    refine ⟨83313533157054524035682939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55542355438036349357121959 83313533157054524035682939)
    ·
      refine ⟨124970299735581786053524409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83313533157054524035682939 124970299735581786053524409)
      ·
        refine ⟨93727724801686339540143307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124970299735581786053524409 93727724801686339540143307)
        ·
          refine ⟨140591587202529509310214961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93727724801686339540143307 140591587202529509310214961)
          ·
            refine ⟨105443690401897131982661221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140591587202529509310214961 105443690401897131982661221)
            ·
              refine ⟨19770691950355712246748979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105443690401897131982661221 19770691950355712246748979)
              ·
                refine ⟨29656037925533568370123469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19770691950355712246748979 29656037925533568370123469)
                ·
                  refine ⟨11121014222075088138796301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29656037925533568370123469 11121014222075088138796301)
                  ·
                    refine ⟨4170380333278158052048613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11121014222075088138796301 4170380333278158052048613)
                    ·
                      refine ⟨781946312489654634759115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4170380333278158052048613 781946312489654634759115)
                      ·
                        rfl

theorem cell23_1522835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 4].length) (baseStart_1522835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522835 prefixEnd_1522835 := by exact prefixLift 1522835
  have htrace : WordTrace (prefixWord ++ tailWord_1522835) baseStart_1522835 baseEnd_1522835 := by
    simpa [prefixWord, tailWord_1522835, baseEnd_1522835] using wordTrace_append hprefix tailTrace_1522835
  have hstable : (prefixWord ++ tailWord_1522835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522835).length < 2 ^ (prefixWord ++ tailWord_1522835).sum := by decide
  have hdescent : baseEnd_1522835 < baseStart_1522835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522872 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 4, 2, 3]
def baseStart_1522872 : Nat := 118140960795 + 1522872 * 2 ^ 59
def prefixEnd_1522872 : Nat := 4983230072969 + 3 ^ 40 * 1522872 * 2
def baseEnd_1522872 : Nat := 781965311273870989996445

theorem tailTrace_1522872 : CollatzResearch.WordTrace tailWord_1522872 prefixEnd_1522872 781965311273870989996445 := by
  unfold tailWord_1522872
  simp only [CollatzResearch.WordTrace]
  refine ⟨27771852469451152338109435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37029136625934869784145913 27771852469451152338109435)
  ·
    refine ⟨41657778704176728507164153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27771852469451152338109435 41657778704176728507164153)
    ·
      refine ⟨31243334028132546380373115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41657778704176728507164153 31243334028132546380373115)
      ·
        refine ⟨46865001042198819570559673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31243334028132546380373115 46865001042198819570559673)
        ·
          refine ⟨35148750781649114677919755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46865001042198819570559673 35148750781649114677919755)
          ·
            refine ⟨52723126172473672016879633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35148750781649114677919755 52723126172473672016879633)
            ·
              refine ⟨39542344629355254012659725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52723126172473672016879633 39542344629355254012659725)
              ·
                refine ⟨14828379236008220254747397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39542344629355254012659725 14828379236008220254747397)
                ·
                  refine ⟨2780321106751541297765137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14828379236008220254747397 2780321106751541297765137)
                  ·
                    refine ⟨2085240830063655973323853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2780321106751541297765137 2085240830063655973323853)
                    ·
                      refine ⟨781965311273870989996445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2085240830063655973323853 781965311273870989996445)
                      ·
                        rfl

theorem cell23_1522872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 4, 2, 3].length) (baseStart_1522872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522872 prefixEnd_1522872 := by exact prefixLift 1522872
  have htrace : WordTrace (prefixWord ++ tailWord_1522872) baseStart_1522872 baseEnd_1522872 := by
    simpa [prefixWord, tailWord_1522872, baseEnd_1522872] using wordTrace_append hprefix tailTrace_1522872
  have hstable : (prefixWord ++ tailWord_1522872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522872).length < 2 ^ (prefixWord ++ tailWord_1522872).sum := by decide
  have hdescent : baseEnd_1522872 < baseStart_1522872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522895 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 6]
def baseStart_1522895 : Nat := 118140960795 + 1522895 * 2 ^ 59
def prefixEnd_1522895 : Nat := 4983230072969 + 3 ^ 40 * 1522895 * 2
def baseEnd_1522895 : Nat := 781977121328924400008839

theorem tailTrace_1522895 : CollatzResearch.WordTrace tailWord_1522895 prefixEnd_1522895 781977121328924400008839 := by
  unfold tailWord_1522895
  simp only [CollatzResearch.WordTrace]
  refine ⟨55544543817818979604306139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37029695878545986402870759 55544543817818979604306139)
  ·
    refine ⟨83316815726728469406459209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55544543817818979604306139 83316815726728469406459209)
    ·
      refine ⟨62487611795046352054844407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83316815726728469406459209 62487611795046352054844407)
      ·
        refine ⟨93731417692569528082266611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62487611795046352054844407 93731417692569528082266611)
        ·
          refine ⟨140597126538854292123399917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93731417692569528082266611 140597126538854292123399917)
          ·
            refine ⟨52723922452070359546274969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140597126538854292123399917 52723922452070359546274969)
            ·
              refine ⟨39542941839052769659706227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52723922452070359546274969 39542941839052769659706227)
              ·
                refine ⟨59314412758579154489559341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39542941839052769659706227 59314412758579154489559341)
                ·
                  refine ⟨22242904784467182933584753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59314412758579154489559341 22242904784467182933584753)
                  ·
                    refine ⟨16682178588350387200188565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22242904784467182933584753 16682178588350387200188565)
                    ·
                      refine ⟨781977121328924400008839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16682178588350387200188565 781977121328924400008839)
                      ·
                        rfl

theorem cell23_1522895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 6].length) (baseStart_1522895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522895 prefixEnd_1522895 := by exact prefixLift 1522895
  have htrace : WordTrace (prefixWord ++ tailWord_1522895) baseStart_1522895 baseEnd_1522895 := by
    simpa [prefixWord, tailWord_1522895, baseEnd_1522895] using wordTrace_append hprefix tailTrace_1522895
  have hstable : (prefixWord ++ tailWord_1522895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522895).length < 2 ^ (prefixWord ++ tailWord_1522895).sum := by decide
  have hdescent : baseEnd_1522895 < baseStart_1522895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522929 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 4, 3, 2]
def baseStart_1522929 : Nat := 118140960795 + 1522929 * 2 ^ 59
def prefixEnd_1522929 : Nat := 4983230072969 + 3 ^ 40 * 1522929 * 2
def baseEnd_1522929 : Nat := 781994579671177266983683

theorem tailTrace_1522929 : CollatzResearch.WordTrace tailWord_1522929 prefixEnd_1522929 781994579671177266983683 := by
  unfold tailWord_1522929
  simp only [CollatzResearch.WordTrace]
  refine ⟨55545783899695803411043841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37030522599797202274029227 55545783899695803411043841)
  ·
    refine ⟨41659337924771852558282881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55545783899695803411043841 41659337924771852558282881)
    ·
      refine ⟨31244503443578889418712161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41659337924771852558282881 31244503443578889418712161)
      ·
        refine ⟨23433377582684167064034121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31244503443578889418712161 23433377582684167064034121)
        ·
          refine ⟨17575033187013125298025591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23433377582684167064034121 17575033187013125298025591)
          ·
            refine ⟨26362549780519687947038387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17575033187013125298025591 26362549780519687947038387)
            ·
              refine ⟨39543824670779531920557581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26362549780519687947038387 39543824670779531920557581)
              ·
                refine ⟨14828934251542324470209093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39543824670779531920557581 14828934251542324470209093)
                ·
                  refine ⟨2780425172164185838164205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14828934251542324470209093 2780425172164185838164205)
                  ·
                    refine ⟨1042659439561569689311577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2780425172164185838164205 1042659439561569689311577)
                    ·
                      refine ⟨781994579671177266983683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1042659439561569689311577 781994579671177266983683)
                      ·
                        rfl

theorem cell23_1522929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 3, 2].length) (baseStart_1522929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522929 prefixEnd_1522929 := by exact prefixLift 1522929
  have htrace : WordTrace (prefixWord ++ tailWord_1522929) baseStart_1522929 baseEnd_1522929 := by
    simpa [prefixWord, tailWord_1522929, baseEnd_1522929] using wordTrace_append hprefix tailTrace_1522929
  have hstable : (prefixWord ++ tailWord_1522929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522929).length < 2 ^ (prefixWord ++ tailWord_1522929).sum := by decide
  have hdescent : baseEnd_1522929 < baseStart_1522929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522970 : List Nat := [3, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3]
def baseStart_1522970 : Nat := 118140960795 + 1522970 * 2 ^ 59
def prefixEnd_1522970 : Nat := 4983230072969 + 3 ^ 40 * 1522970 * 2
def baseEnd_1522970 : Nat := 782015632378011606570995

theorem tailTrace_1522970 : CollatzResearch.WordTrace tailWord_1522970 prefixEnd_1522970 782015632378011606570995 := by
  unfold tailWord_1522970
  simp only [CollatzResearch.WordTrace]
  refine ⟨13886819823136816853321591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37031519528364844942190909 13886819823136816853321591)
  ·
    refine ⟨20830229734705225279982387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13886819823136816853321591 20830229734705225279982387)
    ·
      refine ⟨31245344602057837919973581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20830229734705225279982387 31245344602057837919973581)
      ·
        refine ⟨11717004225771689219990093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31245344602057837919973581 11717004225771689219990093)
        ·
          refine ⟨4393876584664383457496285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11717004225771689219990093 4393876584664383457496285)
          ·
            refine ⟨1647703719249143796561107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4393876584664383457496285 1647703719249143796561107)
            ·
              refine ⟨2471555578873715694841661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1647703719249143796561107 2471555578873715694841661)
              ·
                refine ⟨926833342077643385565623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2471555578873715694841661 926833342077643385565623)
                ·
                  refine ⟨1390250013116465078348435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 926833342077643385565623 1390250013116465078348435)
                  ·
                    refine ⟨2085375019674697617522653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1390250013116465078348435 2085375019674697617522653)
                    ·
                      refine ⟨782015632378011606570995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2085375019674697617522653 782015632378011606570995)
                      ·
                        rfl

theorem cell23_1522970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_1522970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522970 prefixEnd_1522970 := by exact prefixLift 1522970
  have htrace : WordTrace (prefixWord ++ tailWord_1522970) baseStart_1522970 baseEnd_1522970 := by
    simpa [prefixWord, tailWord_1522970, baseEnd_1522970] using wordTrace_append hprefix tailTrace_1522970
  have hstable : (prefixWord ++ tailWord_1522970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522970).length < 2 ^ (prefixWord ++ tailWord_1522970).sum := by decide
  have hdescent : baseEnd_1522970 < baseStart_1522970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522979 : List Nat := [1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 5]
def baseStart_1522979 : Nat := 118140960795 + 1522979 * 2 ^ 59
def prefixEnd_1522979 : Nat := 4983230072969 + 3 ^ 40 * 1522979 * 2
def baseEnd_1522979 : Nat := 782020253703902071358453

theorem tailTrace_1522979 : CollatzResearch.WordTrace tailWord_1522979 prefixEnd_1522979 782020253703902071358453 := by
  unfold tailWord_1522979
  simp only [CollatzResearch.WordTrace]
  refine ⟨55547607549514661950363991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37031738366343107966909327 55547607549514661950363991)
  ·
    refine ⟨83321411324271992925545987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55547607549514661950363991 83321411324271992925545987)
    ·
      refine ⟨124982116986407989388318981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83321411324271992925545987 124982116986407989388318981)
      ·
        refine ⟨23434146934951498010309809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124982116986407989388318981 23434146934951498010309809)
        ·
          refine ⟨17575610201213623507732357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23434146934951498010309809 17575610201213623507732357)
          ·
            refine ⟨3295426912727554407699817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17575610201213623507732357 3295426912727554407699817)
            ·
              refine ⟨2471570184545665805774863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3295426912727554407699817 2471570184545665805774863)
              ·
                refine ⟨3707355276818498708662295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2471570184545665805774863 3707355276818498708662295)
                ·
                  refine ⟨5561032915227748062993443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3707355276818498708662295 5561032915227748062993443)
                  ·
                    refine ⟨8341549372841622094490165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5561032915227748062993443 8341549372841622094490165)
                    ·
                      refine ⟨782020253703902071358453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8341549372841622094490165 782020253703902071358453)
                      ·
                        rfl

theorem cell23_1522979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_1522979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522979 prefixEnd_1522979 := by exact prefixLift 1522979
  have htrace : WordTrace (prefixWord ++ tailWord_1522979) baseStart_1522979 baseEnd_1522979 := by
    simpa [prefixWord, tailWord_1522979, baseEnd_1522979] using wordTrace_append hprefix tailTrace_1522979
  have hstable : (prefixWord ++ tailWord_1522979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522979).length < 2 ^ (prefixWord ++ tailWord_1522979).sum := by decide
  have hdescent : baseEnd_1522979 < baseStart_1522979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522986 : List Nat := [3, 1, 4, 2, 1, 1, 2, 1, 4, 4]
def baseStart_1522986 : Nat := 118140960795 + 1522986 * 2 ^ 59
def prefixEnd_1522986 : Nat := 4983230072969 + 3 ^ 40 * 1522986 * 2
def baseEnd_1522986 : Nat := 260674616022827847990307

theorem tailTrace_1522986 : CollatzResearch.WordTrace tailWord_1522986 prefixEnd_1522986 260674616022827847990307 := by
  unfold tailWord_1522986
  simp only [CollatzResearch.WordTrace]
  refine ⟨13886965715122325536467203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37031908573659534763912541 13886965715122325536467203)
  ·
    refine ⟨20830448572683488304700805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13886965715122325536467203 20830448572683488304700805)
    ·
      refine ⟨3905709107378154057131401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20830448572683488304700805 3905709107378154057131401)
      ·
        refine ⟨2929281830533615542848551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3905709107378154057131401 2929281830533615542848551)
        ·
          refine ⟨4393922745800423314272827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2929281830533615542848551 4393922745800423314272827)
          ·
            refine ⟨6590884118700634971409241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4393922745800423314272827 6590884118700634971409241)
            ·
              refine ⟨4943163089025476228556931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6590884118700634971409241 4943163089025476228556931)
              ·
                refine ⟨7414744633538214342835397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4943163089025476228556931 7414744633538214342835397)
                ·
                  refine ⟨1390264618788415189281637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7414744633538214342835397 1390264618788415189281637)
                  ·
                    refine ⟨260674616022827847990307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1390264618788415189281637 260674616022827847990307)
                    ·
                      rfl

theorem cell23_1522986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_1522986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522986 prefixEnd_1522986 := by exact prefixLift 1522986
  have htrace : WordTrace (prefixWord ++ tailWord_1522986) baseStart_1522986 baseEnd_1522986 := by
    simpa [prefixWord, tailWord_1522986, baseEnd_1522986] using wordTrace_append hprefix tailTrace_1522986
  have hstable : (prefixWord ++ tailWord_1522986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522986).length < 2 ^ (prefixWord ++ tailWord_1522986).sum := by decide
  have hdescent : baseEnd_1522986 < baseStart_1522986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522993 : List Nat := [1, 2, 2, 3, 3, 1, 3, 1, 3, 2, 2]
def baseStart_1522993 : Nat := 118140960795 + 1522993 * 2 ^ 59
def prefixEnd_1522993 : Nat := 4983230072969 + 3 ^ 40 * 1522993 * 2
def baseEnd_1522993 : Nat := 782027442433065016583389

theorem tailTrace_1522993 : CollatzResearch.WordTrace tailWord_1522993 prefixEnd_1522993 782027442433065016583389 := by
  unfold tailWord_1522993
  simp only [CollatzResearch.WordTrace]
  refine ⟨55548118171463942341373633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37032078780975961560915755 55548118171463942341373633)
  ·
    refine ⟨41661088628597956756030225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55548118171463942341373633 41661088628597956756030225)
    ·
      refine ⟨31245816471448467567022669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41661088628597956756030225 31245816471448467567022669)
      ·
        refine ⟨11717181176793175337633501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31245816471448467567022669 11717181176793175337633501)
        ·
          refine ⟨4393942941297440751612563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11717181176793175337633501 4393942941297440751612563)
          ·
            refine ⟨6590914411946161127418845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4393942941297440751612563 6590914411946161127418845)
            ·
              refine ⟨2471592904479810422782067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6590914411946161127418845 2471592904479810422782067)
              ·
                refine ⟨3707389356719715634173101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2471592904479810422782067 3707389356719715634173101)
                ·
                  refine ⟨1390271008769893362814913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3707389356719715634173101 1390271008769893362814913)
                  ·
                    refine ⟨1042703256577420022111185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1390271008769893362814913 1042703256577420022111185)
                    ·
                      refine ⟨782027442433065016583389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1042703256577420022111185 782027442433065016583389)
                      ·
                        rfl

theorem cell23_1522993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_1522993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522993 prefixEnd_1522993 := by exact prefixLift 1522993
  have htrace : WordTrace (prefixWord ++ tailWord_1522993) baseStart_1522993 baseEnd_1522993 := by
    simpa [prefixWord, tailWord_1522993, baseEnd_1522993] using wordTrace_append hprefix tailTrace_1522993
  have hstable : (prefixWord ++ tailWord_1522993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522993).length < 2 ^ (prefixWord ++ tailWord_1522993).sum := by decide
  have hdescent : baseEnd_1522993 < baseStart_1522993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522996 : List Nat := [2, 5, 1, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_1522996 : Nat := 118140960795 + 1522996 * 2 ^ 59
def prefixEnd_1522996 : Nat := 4983230072969 + 3 ^ 40 * 1522996 * 2
def baseEnd_1522996 : Nat := 782028982875028504845875

theorem tailTrace_1522996 : CollatzResearch.WordTrace tailWord_1522996 prefixEnd_1522996 782028982875028504845875 := by
  unfold tailWord_1522996
  simp only [CollatzResearch.WordTrace]
  refine ⟨27774113795226536926866421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37032151726968715902488561 27774113795226536926866421)
  ·
    refine ⟨2603823168302487836893727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27774113795226536926866421 2603823168302487836893727)
    ·
      refine ⟨3905734752453731755340591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2603823168302487836893727 3905734752453731755340591)
      ·
        refine ⟨5858602128680597633010887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3905734752453731755340591 5858602128680597633010887)
        ·
          refine ⟨8787903193020896449516331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5858602128680597633010887 8787903193020896449516331)
          ·
            refine ⟨13181854789531344674274497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8787903193020896449516331 13181854789531344674274497)
            ·
              refine ⟨9886391092148508505705873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13181854789531344674274497 9886391092148508505705873)
              ·
                refine ⟨7414793319111381379279405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9886391092148508505705873 7414793319111381379279405)
                ·
                  refine ⟨2780547494666768017229777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7414793319111381379279405 2780547494666768017229777)
                  ·
                    refine ⟨2085410621000076012922333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2780547494666768017229777 2085410621000076012922333)
                    ·
                      refine ⟨782028982875028504845875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2085410621000076012922333 782028982875028504845875)
                      ·
                        rfl

theorem cell23_1522996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_1522996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1522996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1522996 prefixEnd_1522996 := by exact prefixLift 1522996
  have htrace : WordTrace (prefixWord ++ tailWord_1522996) baseStart_1522996 baseEnd_1522996 := by
    simpa [prefixWord, tailWord_1522996, baseEnd_1522996] using wordTrace_append hprefix tailTrace_1522996
  have hstable : (prefixWord ++ tailWord_1522996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522996).length < 2 ^ (prefixWord ++ tailWord_1522996).sum := by decide
  have hdescent : baseEnd_1522996 < baseStart_1522996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523002 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6]
def baseStart_1523002 : Nat := 118140960795 + 1523002 * 2 ^ 59
def prefixEnd_1523002 : Nat := 4983230072969 + 3 ^ 40 * 1523002 * 2
def baseEnd_1523002 : Nat := 782032063758955481370847

theorem tailTrace_1523002 : CollatzResearch.WordTrace tailWord_1523002 prefixEnd_1523002 782032063758955481370847 := by
  unfold tailWord_1523002
  simp only [CollatzResearch.WordTrace]
  refine ⟨13887111607107834219612815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37032297618954224585634173 13887111607107834219612815)
  ·
    refine ⟨20830667410661751329419223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13887111607107834219612815 20830667410661751329419223)
    ·
      refine ⟨31246001115992626994128835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20830667410661751329419223 31246001115992626994128835)
      ·
        refine ⟨46869001673988940491193253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31246001115992626994128835 46869001673988940491193253)
        ·
          refine ⟨8787937813872926342098735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46869001673988940491193253 8787937813872926342098735)
          ·
            refine ⟨13181906720809389513148103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8787937813872926342098735 13181906720809389513148103)
            ·
              refine ⟨19772860081214084269722155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13181906720809389513148103 19772860081214084269722155)
              ·
                refine ⟨29659290121821126404583233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19772860081214084269722155 29659290121821126404583233)
                ·
                  refine ⟨22244467591365844803437425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29659290121821126404583233 22244467591365844803437425)
                  ·
                    refine ⟨16683350693524383602578069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22244467591365844803437425 16683350693524383602578069)
                    ·
                      refine ⟨782032063758955481370847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16683350693524383602578069 782032063758955481370847)
                      ·
                        rfl

theorem cell23_1523002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_1523002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523002 prefixEnd_1523002 := by exact prefixLift 1523002
  have htrace : WordTrace (prefixWord ++ tailWord_1523002) baseStart_1523002 baseEnd_1523002 := by
    simpa [prefixWord, tailWord_1523002, baseEnd_1523002] using wordTrace_append hprefix tailTrace_1523002
  have hstable : (prefixWord ++ tailWord_1523002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523002).length < 2 ^ (prefixWord ++ tailWord_1523002).sum := by decide
  have hdescent : baseEnd_1523002 < baseStart_1523002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523037 : List Nat := [1, 4, 5, 1, 1, 1, 2, 2, 2, 4]
def baseStart_1523037 : Nat := 118140960795 + 1523037 * 2 ^ 59
def prefixEnd_1523037 : Nat := 4983230072969 + 3 ^ 40 * 1523037 * 2
def baseEnd_1523037 : Nat := 260683345193954281477729

theorem tailTrace_1523037 : CollatzResearch.WordTrace tailWord_1523037 prefixEnd_1523037 260683345193954281477729 := by
  unfold tailWord_1523037
  simp only [CollatzResearch.WordTrace]
  refine ⟨55549722983304537855975365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37033148655536358570650243 55549722983304537855975365)
  ·
    refine ⟨10415573059369600847995381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55549722983304537855975365 10415573059369600847995381)
    ·
      refine ⟨976459974315900079499567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10415573059369600847995381 976459974315900079499567)
      ·
        refine ⟨1464689961473850119249351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 976459974315900079499567 1464689961473850119249351)
        ·
          refine ⟨2197034942210775178874027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1464689961473850119249351 2197034942210775178874027)
          ·
            refine ⟨3295552413316162768311041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2197034942210775178874027 3295552413316162768311041)
            ·
              refine ⟨2471664309987122076233281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3295552413316162768311041 2471664309987122076233281)
              ·
                refine ⟨1853748232490341557174961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2471664309987122076233281 1853748232490341557174961)
                ·
                  refine ⟨1390311174367756167881221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1853748232490341557174961 1390311174367756167881221)
                  ·
                    refine ⟨260683345193954281477729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1390311174367756167881221 260683345193954281477729)
                    ·
                      rfl

theorem cell23_1523037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_1523037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523037 prefixEnd_1523037 := by exact prefixLift 1523037
  have htrace : WordTrace (prefixWord ++ tailWord_1523037) baseStart_1523037 baseEnd_1523037 := by
    simpa [prefixWord, tailWord_1523037, baseEnd_1523037] using wordTrace_append hprefix tailTrace_1523037
  have hstable : (prefixWord ++ tailWord_1523037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523037).length < 2 ^ (prefixWord ++ tailWord_1523037).sum := by decide
  have hdescent : baseEnd_1523037 < baseStart_1523037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523043 : List Nat := [1, 1, 1, 5, 2, 3, 2, 2, 2, 1, 3]
def baseStart_1523043 : Nat := 118140960795 + 1523043 * 2 ^ 59
def prefixEnd_1523043 : Nat := 4983230072969 + 3 ^ 40 * 1523043 * 2
def baseEnd_1523043 : Nat := 782053116465789820958159

theorem tailTrace_1523043 : CollatzResearch.WordTrace tailWord_1523043 prefixEnd_1523043 782053116465789820958159 := by
  unfold tailWord_1523043
  simp only [CollatzResearch.WordTrace]
  refine ⟨55549941821282800880693783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37033294547521867253795855 55549941821282800880693783)
  ·
    refine ⟨83324912731924201321040675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55549941821282800880693783 83324912731924201321040675)
    ·
      refine ⟨124987369097886301981561013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83324912731924201321040675 124987369097886301981561013)
      ·
        refine ⟨11717565852926840810771345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124987369097886301981561013 11717565852926840810771345)
        ·
          refine ⟨8788174389695130608078509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11717565852926840810771345 8788174389695130608078509)
          ·
            refine ⟨3295565396135673978029441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8788174389695130608078509 3295565396135673978029441)
            ·
              refine ⟨2471674047101755483522081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3295565396135673978029441 2471674047101755483522081)
              ·
                refine ⟨1853755535326316612641561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2471674047101755483522081 1853755535326316612641561)
                ·
                  refine ⟨1390316651494737459481171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1853755535326316612641561 1390316651494737459481171)
                  ·
                    refine ⟨2085474977242106189221757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1390316651494737459481171 2085474977242106189221757)
                    ·
                      refine ⟨782053116465789820958159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2085474977242106189221757 782053116465789820958159)
                      ·
                        rfl

theorem cell23_1523043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_1523043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523043 prefixEnd_1523043 := by exact prefixLift 1523043
  have htrace : WordTrace (prefixWord ++ tailWord_1523043) baseStart_1523043 baseEnd_1523043 := by
    simpa [prefixWord, tailWord_1523043, baseEnd_1523043] using wordTrace_append hprefix tailTrace_1523043
  have hstable : (prefixWord ++ tailWord_1523043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523043).length < 2 ^ (prefixWord ++ tailWord_1523043).sum := by decide
  have hdescent : baseEnd_1523043 < baseStart_1523043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523069 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 2, 4, 3]
def baseStart_1523069 : Nat := 118140960795 + 1523069 * 2 ^ 59
def prefixEnd_1523069 : Nat := 4983230072969 + 3 ^ 40 * 1523069 * 2
def baseEnd_1523069 : Nat := 782066466962806719233039

theorem tailTrace_1523069 : CollatzResearch.WordTrace tailWord_1523069 prefixEnd_1523069 782066466962806719233039 := by
  unfold tailWord_1523069
  simp only [CollatzResearch.WordTrace]
  refine ⟨55550890119188607321140261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37033926746125738214093507 55550890119188607321140261)
  ·
    refine ⟨10415791897347863872713799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55550890119188607321140261 10415791897347863872713799)
    ·
      refine ⟨15623687846021795809070699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10415791897347863872713799 15623687846021795809070699)
      ·
        refine ⟨23435531769032693713606049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15623687846021795809070699 23435531769032693713606049)
        ·
          refine ⟨17576648826774520285204537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23435531769032693713606049 17576648826774520285204537)
          ·
            refine ⟨13182486620080890213903403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17576648826774520285204537 13182486620080890213903403)
            ·
              refine ⟨19773729930121335320855105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13182486620080890213903403 19773729930121335320855105)
              ·
                refine ⟨14830297447591001490641329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19773729930121335320855105 14830297447591001490641329)
                ·
                  refine ⟨11122723085693251117980997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14830297447591001490641329 11122723085693251117980997)
                  ·
                    refine ⟨2085510578567484584621437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11122723085693251117980997 2085510578567484584621437)
                    ·
                      refine ⟨782066466962806719233039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2085510578567484584621437 782066466962806719233039)
                      ·
                        rfl

theorem cell23_1523069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_1523069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523069 prefixEnd_1523069 := by exact prefixLift 1523069
  have htrace : WordTrace (prefixWord ++ tailWord_1523069) baseStart_1523069 baseEnd_1523069 := by
    simpa [prefixWord, tailWord_1523069, baseEnd_1523069] using wordTrace_append hprefix tailTrace_1523069
  have hstable : (prefixWord ++ tailWord_1523069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523069).length < 2 ^ (prefixWord ++ tailWord_1523069).sum := by decide
  have hdescent : baseEnd_1523069 < baseStart_1523069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523106 : List Nat := [3, 3, 1, 2, 1, 3, 2, 1, 7]
def baseStart_1523106 : Nat := 118140960795 + 1523106 * 2 ^ 59
def prefixEnd_1523106 : Nat := 4983230072969 + 3 ^ 40 * 1523106 * 2
def baseEnd_1523106 : Nat := 86898385083002563830041

theorem tailTrace_1523106 : CollatzResearch.WordTrace tailWord_1523106 prefixEnd_1523106 86898385083002563830041 := by
  unfold tailWord_1523106
  simp only [CollatzResearch.WordTrace]
  refine ⟨13888059905013640660059293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37034826413369708426824781 13888059905013640660059293)
  ·
    refine ⟨5208022464380115247522235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13888059905013640660059293 5208022464380115247522235)
    ·
      refine ⟨7812033696570172871283353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5208022464380115247522235 7812033696570172871283353)
      ·
        refine ⟨5859025272427629653462515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7812033696570172871283353 5859025272427629653462515)
        ·
          refine ⟨8788537908641444480193773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5859025272427629653462515 8788537908641444480193773)
          ·
            refine ⟨3295701715740541680072665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8788537908641444480193773 3295701715740541680072665)
            ·
              refine ⟨2471776286805406260054499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3295701715740541680072665 2471776286805406260054499)
              ·
                refine ⟨3707664430208109390081749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2471776286805406260054499 3707664430208109390081749)
                ·
                  refine ⟨86898385083002563830041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3707664430208109390081749 86898385083002563830041)
                  ·
                    rfl

theorem cell23_1523106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_1523106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523106 prefixEnd_1523106 := by exact prefixLift 1523106
  have htrace : WordTrace (prefixWord ++ tailWord_1523106) baseStart_1523106 baseEnd_1523106 := by
    simpa [prefixWord, tailWord_1523106, baseEnd_1523106] using wordTrace_append hprefix tailTrace_1523106
  have hstable : (prefixWord ++ tailWord_1523106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523106).length < 2 ^ (prefixWord ++ tailWord_1523106).sum := by decide
  have hdescent : baseEnd_1523106 < baseStart_1523106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523139 : List Nat := [1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 4]
def baseStart_1523139 : Nat := 118140960795 + 1523139 * 2 ^ 59
def prefixEnd_1523139 : Nat := 4983230072969 + 3 ^ 40 * 1523139 * 2
def baseEnd_1523139 : Nat := 782102410608621445357717

theorem tailTrace_1523139 : CollatzResearch.WordTrace tailWord_1523139 prefixEnd_1523139 782102410608621445357717 := by
  unfold tailWord_1523139
  simp only [CollatzResearch.WordTrace]
  refine ⟨55553443228935009276188471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37035628819290006184125647 55553443228935009276188471)
  ·
    refine ⟨83330164843402513914282707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55553443228935009276188471 83330164843402513914282707)
    ·
      refine ⟨124995247265103770871424061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83330164843402513914282707 124995247265103770871424061)
      ·
        refine ⟨46873217724413914076784023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124995247265103770871424061 46873217724413914076784023)
        ·
          refine ⟨70309826586620871115176035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46873217724413914076784023 70309826586620871115176035)
          ·
            refine ⟨105464739879931306672764053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70309826586620871115176035 105464739879931306672764053)
            ·
              refine ⟨4943659681871780000285815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 105464739879931306672764053 4943659681871780000285815)
              ·
                refine ⟨7415489522807670000428723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4943659681871780000285815 7415489522807670000428723)
                ·
                  refine ⟨11123234284211505000643085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7415489522807670000428723 11123234284211505000643085)
                  ·
                    refine ⟨4171212856579314375241157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11123234284211505000643085 4171212856579314375241157)
                    ·
                      refine ⟨782102410608621445357717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4171212856579314375241157 782102410608621445357717)
                      ·
                        rfl

theorem cell23_1523139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_1523139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523139 prefixEnd_1523139 := by exact prefixLift 1523139
  have htrace : WordTrace (prefixWord ++ tailWord_1523139) baseStart_1523139 baseEnd_1523139 := by
    simpa [prefixWord, tailWord_1523139, baseEnd_1523139] using wordTrace_append hprefix tailTrace_1523139
  have hstable : (prefixWord ++ tailWord_1523139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523139).length < 2 ^ (prefixWord ++ tailWord_1523139).sum := by decide
  have hdescent : baseEnd_1523139 < baseStart_1523139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523140 : List Nat := [2, 3, 3, 2, 1, 3, 1, 3, 5]
def baseStart_1523140 : Nat := 118140960795 + 1523140 * 2 ^ 59
def prefixEnd_1523140 : Nat := 4983230072969 + 3 ^ 40 * 1523140 * 2
def baseEnd_1523140 : Nat := 86900324898808437938357

theorem tailTrace_1523140 : CollatzResearch.WordTrace tailWord_1523140 prefixEnd_1523140 86900324898808437938357 := by
  unfold tailWord_1523140
  simp only [CollatzResearch.WordTrace]
  refine ⟨27776739850965693223487437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37035653134620924297983249 27776739850965693223487437)
  ·
    refine ⟨10416277444112134958807789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27776739850965693223487437 10416277444112134958807789)
    ·
      refine ⟨3906104041542050609552921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10416277444112134958807789 3906104041542050609552921)
      ·
        refine ⟨2929578031156537957164691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3906104041542050609552921 2929578031156537957164691)
        ·
          refine ⟨4394367046734806935747037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2929578031156537957164691 4394367046734806935747037)
          ·
            refine ⟨1647887642525552600905139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4394367046734806935747037 1647887642525552600905139)
            ·
              refine ⟨2471831463788328901357709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1647887642525552600905139 2471831463788328901357709)
              ·
                refine ⟨926936798920623338009141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2471831463788328901357709 926936798920623338009141)
                ·
                  refine ⟨86900324898808437938357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 926936798920623338009141 86900324898808437938357)
                  ·
                    rfl

theorem cell23_1523140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3, 5].length) (baseStart_1523140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523140 prefixEnd_1523140 := by exact prefixLift 1523140
  have htrace : WordTrace (prefixWord ++ tailWord_1523140) baseStart_1523140 baseEnd_1523140 := by
    simpa [prefixWord, tailWord_1523140, baseEnd_1523140] using wordTrace_append hprefix tailTrace_1523140
  have hstable : (prefixWord ++ tailWord_1523140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523140).length < 2 ^ (prefixWord ++ tailWord_1523140).sum := by decide
  have hdescent : baseEnd_1523140 < baseStart_1523140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523176 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 4, 2, 3]
def baseStart_1523176 : Nat := 118140960795 + 1523176 * 2 ^ 59
def prefixEnd_1523176 : Nat := 4983230072969 + 3 ^ 40 * 1523176 * 2
def baseEnd_1523176 : Nat := 782121409392837800595047

theorem tailTrace_1523176 : CollatzResearch.WordTrace tailWord_1523176 prefixEnd_1523176 782121409392837800595047 := by
  unfold tailWord_1523176
  simp only [CollatzResearch.WordTrace]
  refine ⟨27777396364900482297642691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37036528486533976396856921 27777396364900482297642691)
  ·
    refine ⟨41666094547350723446464037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27777396364900482297642691 41666094547350723446464037)
    ·
      refine ⟨7812392727628260646212007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41666094547350723446464037 7812392727628260646212007)
      ·
        refine ⟨11718589091442390969318011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7812392727628260646212007 11718589091442390969318011)
        ·
          refine ⟨17577883637163586453977017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11718589091442390969318011 17577883637163586453977017)
          ·
            refine ⟨13183412727872689840482763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17577883637163586453977017 13183412727872689840482763)
            ·
              refine ⟨19775119091809034760724145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13183412727872689840482763 19775119091809034760724145)
              ·
                refine ⟨14831339318856776070543109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19775119091809034760724145 14831339318856776070543109)
                ·
                  refine ⟨2780876122285645513226833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14831339318856776070543109 2780876122285645513226833)
                  ·
                    refine ⟨2085657091714234134920125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2780876122285645513226833 2085657091714234134920125)
                    ·
                      refine ⟨782121409392837800595047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2085657091714234134920125 782121409392837800595047)
                      ·
                        rfl

theorem cell23_1523176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_1523176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523176 prefixEnd_1523176 := by exact prefixLift 1523176
  have htrace : WordTrace (prefixWord ++ tailWord_1523176) baseStart_1523176 baseEnd_1523176 := by
    simpa [prefixWord, tailWord_1523176, baseEnd_1523176] using wordTrace_append hprefix tailTrace_1523176
  have hstable : (prefixWord ++ tailWord_1523176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523176).length < 2 ^ (prefixWord ++ tailWord_1523176).sum := by decide
  have hdescent : baseEnd_1523176 < baseStart_1523176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523256 : List Nat := [2, 1, 2, 1, 4, 2, 2, 2, 1, 6]
def baseStart_1523256 : Nat := 118140960795 + 1523256 * 2 ^ 59
def prefixEnd_1523256 : Nat := 4983230072969 + 3 ^ 40 * 1523256 * 2
def baseEnd_1523256 : Nat := 260720829281732495864893

theorem tailTrace_1523256 : CollatzResearch.WordTrace tailWord_1523256 prefixEnd_1523256 260720829281732495864893 := by
  unfold tailWord_1523256
  simp only [CollatzResearch.WordTrace]
  refine ⟨27778855284755569129098811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37038473713007425505465081 27778855284755569129098811)
  ·
    refine ⟨41668282927133353693648217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27778855284755569129098811 41668282927133353693648217)
    ·
      refine ⟨31251212195350015270236163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41668282927133353693648217 31251212195350015270236163)
      ·
        refine ⟨46876818293025022905354245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31251212195350015270236163 46876818293025022905354245)
        ·
          refine ⟨8789403429942191794753921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46876818293025022905354245 8789403429942191794753921)
          ·
            refine ⟨6592052572456643846065441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8789403429942191794753921 6592052572456643846065441)
            ·
              refine ⟨4944039429342482884549081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6592052572456643846065441 4944039429342482884549081)
              ·
                refine ⟨3708029572006862163411811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4944039429342482884549081 3708029572006862163411811)
                ·
                  refine ⟨5562044358010293245117717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3708029572006862163411811 5562044358010293245117717)
                  ·
                    refine ⟨260720829281732495864893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5562044358010293245117717 260720829281732495864893)
                    ·
                      rfl

theorem cell23_1523256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 1, 6].length) (baseStart_1523256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523256 prefixEnd_1523256 := by exact prefixLift 1523256
  have htrace : WordTrace (prefixWord ++ tailWord_1523256) baseStart_1523256 baseEnd_1523256 := by
    simpa [prefixWord, tailWord_1523256, baseEnd_1523256] using wordTrace_append hprefix tailTrace_1523256
  have hstable : (prefixWord ++ tailWord_1523256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523256).length < 2 ^ (prefixWord ++ tailWord_1523256).sum := by decide
  have hdescent : baseEnd_1523256 < baseStart_1523256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523257 : List Nat := [1, 2, 1, 5, 1, 3, 2, 3, 1, 1, 3]
def baseStart_1523257 : Nat := 118140960795 + 1523257 * 2 ^ 59
def prefixEnd_1523257 : Nat := 4983230072969 + 3 ^ 40 * 1523257 * 2
def baseEnd_1523257 : Nat := 782163001325851983682175

theorem tailTrace_1523257 : CollatzResearch.WordTrace tailWord_1523257 prefixEnd_1523257 782163001325851983682175 := by
  unfold tailWord_1523257
  simp only [CollatzResearch.WordTrace]
  refine ⟨55557747042507515428984025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37038498028338343619322683 55557747042507515428984025)
  ·
    refine ⟨41668310281880636571738019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55557747042507515428984025 41668310281880636571738019)
    ·
      refine ⟨62502465422820954857607029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41668310281880636571738019 62502465422820954857607029)
      ·
        refine ⟨5859606133389464517900659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62502465422820954857607029 5859606133389464517900659)
        ·
          refine ⟨8789409200084196776850989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5859606133389464517900659 8789409200084196776850989)
          ·
            refine ⟨3296028450031573791319121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8789409200084196776850989 3296028450031573791319121)
            ·
              refine ⟨2472021337523680343489341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3296028450031573791319121 2472021337523680343489341)
              ·
                refine ⟨927008001571380128808503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2472021337523680343489341 927008001571380128808503)
                ·
                  refine ⟨1390512002357070193212755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 927008001571380128808503 1390512002357070193212755)
                  ·
                    refine ⟨2085768003535605289819133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1390512002357070193212755 2085768003535605289819133)
                    ·
                      refine ⟨782163001325851983682175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2085768003535605289819133 782163001325851983682175)
                      ·
                        rfl

theorem cell23_1523257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_1523257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523257 prefixEnd_1523257 := by exact prefixLift 1523257
  have htrace : WordTrace (prefixWord ++ tailWord_1523257) baseStart_1523257 baseEnd_1523257 := by
    simpa [prefixWord, tailWord_1523257, baseEnd_1523257] using wordTrace_append hprefix tailTrace_1523257
  have hstable : (prefixWord ++ tailWord_1523257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523257).length < 2 ^ (prefixWord ++ tailWord_1523257).sum := by decide
  have hdescent : baseEnd_1523257 < baseStart_1523257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523263 : List Nat := [1, 1, 2, 2, 3, 4, 1, 3, 1, 1, 4]
def baseStart_1523263 : Nat := 118140960795 + 1523263 * 2 ^ 59
def prefixEnd_1523263 : Nat := 4983230072969 + 3 ^ 40 * 1523263 * 2
def baseEnd_1523263 : Nat := 782166082209778960207147

theorem tailTrace_1523263 : CollatzResearch.WordTrace tailWord_1523263 prefixEnd_1523263 782166082209778960207147 := by
  unfold tailWord_1523263
  simp only [CollatzResearch.WordTrace]
  refine ⟨55557965880485778453702443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37038643920323852302468295 55557965880485778453702443)
  ·
    refine ⟨83336948820728667680553665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55557965880485778453702443 83336948820728667680553665)
    ·
      refine ⟨62502711615546500760415249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83336948820728667680553665 62502711615546500760415249)
      ·
        refine ⟨46877033711659875570311437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62502711615546500760415249 46877033711659875570311437)
        ·
          refine ⟨17578887641872453338866789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46877033711659875570311437 17578887641872453338866789)
          ·
            refine ⟨3296041432851085001037523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17578887641872453338866789 3296041432851085001037523)
            ·
              refine ⟨4944062149276627501556285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3296041432851085001037523 4944062149276627501556285)
              ·
                refine ⟨1854023305978735313083607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4944062149276627501556285 1854023305978735313083607)
                ·
                  refine ⟨2781034958968102969625411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1854023305978735313083607 2781034958968102969625411)
                  ·
                    refine ⟨4171552438452154454438117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2781034958968102969625411 4171552438452154454438117)
                    ·
                      refine ⟨782166082209778960207147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4171552438452154454438117 782166082209778960207147)
                      ·
                        rfl

theorem cell23_1523263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 1, 4].length) (baseStart_1523263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523263 prefixEnd_1523263 := by exact prefixLift 1523263
  have htrace : WordTrace (prefixWord ++ tailWord_1523263) baseStart_1523263 baseEnd_1523263 := by
    simpa [prefixWord, tailWord_1523263, baseEnd_1523263] using wordTrace_append hprefix tailTrace_1523263
  have hstable : (prefixWord ++ tailWord_1523263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523263).length < 2 ^ (prefixWord ++ tailWord_1523263).sum := by decide
  have hdescent : baseEnd_1523263 < baseStart_1523263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523269 : List Nat := [1, 3, 1, 1, 1, 4, 12]
def baseStart_1523269 : Nat := 118140960795 + 1523269 * 2 ^ 59
def prefixEnd_1523269 : Nat := 4983230072969 + 3 ^ 40 * 1523269 * 2
def baseEnd_1523269 : Nat := 9656409420909949836199

theorem tailTrace_1523269 : CollatzResearch.WordTrace tailWord_1523269 prefixEnd_1523269 9656409420909949836199 := by
  unfold tailWord_1523269
  simp only [CollatzResearch.WordTrace]
  refine ⟨55558184718464041478420861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37038789812309360985613907 55558184718464041478420861)
  ·
    refine ⟨20834319269424015554407823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55558184718464041478420861 20834319269424015554407823)
    ·
      refine ⟨31251478904136023331611735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20834319269424015554407823 31251478904136023331611735)
      ·
        refine ⟨46877218356204034997417603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31251478904136023331611735 46877218356204034997417603)
        ·
          refine ⟨70315827534306052496126405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46877218356204034997417603 70315827534306052496126405)
          ·
            refine ⟨13184217662682384843023701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70315827534306052496126405 13184217662682384843023701)
            ·
              refine ⟨9656409420909949836199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 13184217662682384843023701 9656409420909949836199)
              ·
                rfl

theorem cell23_1523269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 12].length) (baseStart_1523269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523269 prefixEnd_1523269 := by exact prefixLift 1523269
  have htrace : WordTrace (prefixWord ++ tailWord_1523269) baseStart_1523269 baseEnd_1523269 := by
    simpa [prefixWord, tailWord_1523269, baseEnd_1523269] using wordTrace_append hprefix tailTrace_1523269
  have hstable : (prefixWord ++ tailWord_1523269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523269).length < 2 ^ (prefixWord ++ tailWord_1523269).sum := by decide
  have hdescent : baseEnd_1523269 < baseStart_1523269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523279 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 7]
def baseStart_1523279 : Nat := 118140960795 + 1523279 * 2 ^ 59
def prefixEnd_1523279 : Nat := 4983230072969 + 3 ^ 40 * 1523279 * 2
def baseEnd_1523279 : Nat := 782174297900250897607073

theorem tailTrace_1523279 : CollatzResearch.WordTrace tailWord_1523279 prefixEnd_1523279 782174297900250897607073 := by
  unfold tailWord_1523279
  simp only [CollatzResearch.WordTrace]
  refine ⟨55558549448427813186284891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37039032965618542124189927 55558549448427813186284891)
  ·
    refine ⟨83337824172641719779427337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55558549448427813186284891 83337824172641719779427337)
    ·
      refine ⟨62503368129481289834570503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83337824172641719779427337 62503368129481289834570503)
      ·
        refine ⟨93755052194221934751855755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62503368129481289834570503 93755052194221934751855755)
        ·
          refine ⟨140632578291332902127783633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93755052194221934751855755 140632578291332902127783633)
          ·
            refine ⟨105474433718499676595837725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140632578291332902127783633 105474433718499676595837725)
            ·
              refine ⟨39552912644437378723439147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105474433718499676595837725 39552912644437378723439147)
              ·
                refine ⟨59329368966656068085158721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39552912644437378723439147 59329368966656068085158721)
                ·
                  refine ⟨44497026724992051063869041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59329368966656068085158721 44497026724992051063869041)
                  ·
                    refine ⟨33372770043744038297901781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44497026724992051063869041 33372770043744038297901781)
                    ·
                      refine ⟨782174297900250897607073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 33372770043744038297901781 782174297900250897607073)
                      ·
                        rfl

theorem cell23_1523279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 7].length) (baseStart_1523279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523279 prefixEnd_1523279 := by exact prefixLift 1523279
  have htrace : WordTrace (prefixWord ++ tailWord_1523279) baseStart_1523279 baseEnd_1523279 := by
    simpa [prefixWord, tailWord_1523279, baseEnd_1523279] using wordTrace_append hprefix tailTrace_1523279
  have hstable : (prefixWord ++ tailWord_1523279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523279).length < 2 ^ (prefixWord ++ tailWord_1523279).sum := by decide
  have hdescent : baseEnd_1523279 < baseStart_1523279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523280 : List Nat := [2, 1, 1, 1, 1, 3, 6, 1, 3, 2, 2]
def baseStart_1523280 : Nat := 118140960795 + 1523280 * 2 ^ 59
def prefixEnd_1523280 : Nat := 4983230072969 + 3 ^ 40 * 1523280 * 2
def baseEnd_1523280 : Nat := 782174811380905393694569

theorem tailTrace_1523280 : CollatzResearch.WordTrace tailWord_1523280 prefixEnd_1523280 782174811380905393694569 := by
  unfold tailWord_1523280
  simp only [CollatzResearch.WordTrace]
  refine ⟨27779292960712095178535647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37039057280949460238047529 27779292960712095178535647)
  ·
    refine ⟨41668939441068142767803471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27779292960712095178535647 41668939441068142767803471)
    ·
      refine ⟨62503409161602214151705207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41668939441068142767803471 62503409161602214151705207)
      ·
        refine ⟨93755113742403321227557811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62503409161602214151705207 93755113742403321227557811)
        ·
          refine ⟨140632670613604981841336717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93755113742403321227557811 140632670613604981841336717)
          ·
            refine ⟨52737251480101868190501269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140632670613604981841336717 52737251480101868190501269)
            ·
              refine ⟨2472058663129775071429747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52737251480101868190501269 2472058663129775071429747)
              ·
                refine ⟨3708087994694662607144621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2472058663129775071429747 3708087994694662607144621)
                ·
                  refine ⟨1390532998010498477679233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3708087994694662607144621 1390532998010498477679233)
                  ·
                    refine ⟨1042899748507873858259425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1390532998010498477679233 1042899748507873858259425)
                    ·
                      refine ⟨782174811380905393694569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1042899748507873858259425 782174811380905393694569)
                      ·
                        rfl

theorem cell23_1523280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 3, 2, 2].length) (baseStart_1523280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523280 prefixEnd_1523280 := by exact prefixLift 1523280
  have htrace : WordTrace (prefixWord ++ tailWord_1523280) baseStart_1523280 baseEnd_1523280 := by
    simpa [prefixWord, tailWord_1523280, baseEnd_1523280] using wordTrace_append hprefix tailTrace_1523280
  have hstable : (prefixWord ++ tailWord_1523280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523280).length < 2 ^ (prefixWord ++ tailWord_1523280).sum := by decide
  have hdescent : baseEnd_1523280 < baseStart_1523280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523300 : List Nat := [2, 3, 1, 1, 2, 4, 2, 2, 1, 2, 3]
def baseStart_1523300 : Nat := 118140960795 + 1523300 * 2 ^ 59
def prefixEnd_1523300 : Nat := 4983230072969 + 3 ^ 40 * 1523300 * 2
def baseEnd_1523300 : Nat := 782185080993995315444477

theorem tailTrace_1523300 : CollatzResearch.WordTrace tailWord_1523300 prefixEnd_1523300 782185080993995315444477 := by
  unfold tailWord_1523300
  simp only [CollatzResearch.WordTrace]
  refine ⟨27779657690675866886399677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37039543587567822515199569 27779657690675866886399677)
  ·
    refine ⟨10417371634003450082399879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27779657690675866886399677 10417371634003450082399879)
    ·
      refine ⟨15626057451005175123599819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10417371634003450082399879 15626057451005175123599819)
      ·
        refine ⟨23439086176507762685399729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15626057451005175123599819 23439086176507762685399729)
        ·
          refine ⟨17579314632380822014049797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23439086176507762685399729 17579314632380822014049797)
          ·
            refine ⟨3296121493571404127634337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17579314632380822014049797 3296121493571404127634337)
            ·
              refine ⟨2472091120178553095725753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3296121493571404127634337 2472091120178553095725753)
              ·
                refine ⟨1854068340133914821794315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2472091120178553095725753 1854068340133914821794315)
                ·
                  refine ⟨2781102510200872232691473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1854068340133914821794315 2781102510200872232691473)
                  ·
                    refine ⟨2085826882650654174518605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2781102510200872232691473 2085826882650654174518605)
                    ·
                      refine ⟨782185080993995315444477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2085826882650654174518605 782185080993995315444477)
                      ·
                        rfl

theorem cell23_1523300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_1523300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523300 prefixEnd_1523300 := by exact prefixLift 1523300
  have htrace : WordTrace (prefixWord ++ tailWord_1523300) baseStart_1523300 baseEnd_1523300 := by
    simpa [prefixWord, tailWord_1523300, baseEnd_1523300] using wordTrace_append hprefix tailTrace_1523300
  have hstable : (prefixWord ++ tailWord_1523300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523300).length < 2 ^ (prefixWord ++ tailWord_1523300).sum := by decide
  have hdescent : baseEnd_1523300 < baseStart_1523300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523314 : List Nat := [3, 2, 1, 2, 3, 1, 3, 3, 1, 2, 2]
def baseStart_1523314 : Nat := 118140960795 + 1523314 * 2 ^ 59
def prefixEnd_1523314 : Nat := 4983230072969 + 3 ^ 40 * 1523314 * 2
def baseEnd_1523314 : Nat := 782192269723158260669413

theorem tailTrace_1523314 : CollatzResearch.WordTrace tailWord_1523314 prefixEnd_1523314 782192269723158260669413 := by
  unfold tailWord_1523314
  simp only [CollatzResearch.WordTrace]
  refine ⟨13889956500825253540952249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37039884002200676109205997 13889956500825253540952249)
  ·
    refine ⟨10417467375618940155714187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13889956500825253540952249 10417467375618940155714187)
    ·
      refine ⟨15626201063428410233571281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10417467375618940155714187 15626201063428410233571281)
      ·
        refine ⟨11719650797571307675178461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15626201063428410233571281 11719650797571307675178461)
        ·
          refine ⟨4394869049089240378191923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11719650797571307675178461 4394869049089240378191923)
          ·
            refine ⟨6592303573633860567287885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4394869049089240378191923 6592303573633860567287885)
            ·
              refine ⟨2472113840112697712732957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6592303573633860567287885 2472113840112697712732957)
              ·
                refine ⟨927042690042261642274859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2472113840112697712732957 927042690042261642274859)
                ·
                  refine ⟨1390564035063392463412289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 927042690042261642274859 1390564035063392463412289)
                  ·
                    refine ⟨1042923026297544347559217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1390564035063392463412289 1042923026297544347559217)
                    ·
                      refine ⟨782192269723158260669413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1042923026297544347559217 782192269723158260669413)
                      ·
                        rfl

theorem cell23_1523314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_1523314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523314 prefixEnd_1523314 := by exact prefixLift 1523314
  have htrace : WordTrace (prefixWord ++ tailWord_1523314) baseStart_1523314 baseEnd_1523314 := by
    simpa [prefixWord, tailWord_1523314, baseEnd_1523314] using wordTrace_append hprefix tailTrace_1523314
  have hstable : (prefixWord ++ tailWord_1523314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523314).length < 2 ^ (prefixWord ++ tailWord_1523314).sum := by decide
  have hdescent : baseEnd_1523314 < baseStart_1523314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523373 : List Nat := [1, 5, 2, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_1523373 : Nat := 118140960795 + 1523373 * 2 ^ 59
def prefixEnd_1523373 : Nat := 4983230072969 + 3 ^ 40 * 1523373 * 2
def baseEnd_1523373 : Nat := 782222565081773529831641

theorem tailTrace_1523373 : CollatzResearch.WordTrace tailWord_1523373 prefixEnd_1523373 782222565081773529831641 := by
  unfold tailWord_1523373
  simp only [CollatzResearch.WordTrace]
  refine ⟨55561977910087267240206773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37041318606724844826804515 55561977910087267240206773)
  ·
    refine ⟨5208935429070681303769385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55561977910087267240206773 5208935429070681303769385)
    ·
      refine ⟨3906701571803010977827039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5208935429070681303769385 3906701571803010977827039)
      ·
        refine ⟨5860052357704516466740559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3906701571803010977827039 5860052357704516466740559)
        ·
          refine ⟨8790078536556774700110839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5860052357704516466740559 8790078536556774700110839)
          ·
            refine ⟨13185117804835162050166259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8790078536556774700110839 13185117804835162050166259)
            ·
              refine ⟨19777676707252743075249389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13185117804835162050166259 19777676707252743075249389)
              ·
                refine ⟨7416628765219778653218521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19777676707252743075249389 7416628765219778653218521)
                ·
                  refine ⟨5562471573914833989913891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7416628765219778653218521 5562471573914833989913891)
                  ·
                    refine ⟨8343707360872250984870837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5562471573914833989913891 8343707360872250984870837)
                    ·
                      refine ⟨782222565081773529831641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8343707360872250984870837 782222565081773529831641)
                      ·
                        rfl

theorem cell23_1523373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_1523373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523373 prefixEnd_1523373 := by exact prefixLift 1523373
  have htrace : WordTrace (prefixWord ++ tailWord_1523373) baseStart_1523373 baseEnd_1523373 := by
    simpa [prefixWord, tailWord_1523373, baseEnd_1523373] using wordTrace_append hprefix tailTrace_1523373
  have hstable : (prefixWord ++ tailWord_1523373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523373).length < 2 ^ (prefixWord ++ tailWord_1523373).sum := by decide
  have hdescent : baseEnd_1523373 < baseStart_1523373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523427 : List Nat := [1, 1, 1, 7, 2, 1, 2, 3, 5]
def baseStart_1523427 : Nat := 118140960795 + 1523427 * 2 ^ 59
def prefixEnd_1523427 : Nat := 4983230072969 + 3 ^ 40 * 1523427 * 2
def baseEnd_1523427 : Nat := 86916699226346257617377

theorem tailTrace_1523427 : CollatzResearch.WordTrace tailWord_1523427 prefixEnd_1523427 86916699226346257617377 := by
  unfold tailWord_1523427
  simp only [CollatzResearch.WordTrace]
  refine ⟨55563947451891634462672535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37042631634594422975115023 55563947451891634462672535)
  ·
    refine ⟨83345921177837451694008803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55563947451891634462672535 83345921177837451694008803)
    ·
      refine ⟨125018881766756177541013205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83345921177837451694008803 125018881766756177541013205)
      ·
        refine ⟨2930130041408347911117497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 125018881766756177541013205 2930130041408347911117497)
        ·
          refine ⟨2197597531056260933338123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2930130041408347911117497 2197597531056260933338123)
          ·
            refine ⟨3296396296584391400007185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2197597531056260933338123 3296396296584391400007185)
            ·
              refine ⟨2472297222438293550005389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3296396296584391400007185 2472297222438293550005389)
              ·
                refine ⟨927111458414360081252021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2472297222438293550005389 927111458414360081252021)
                ·
                  refine ⟨86916699226346257617377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 927111458414360081252021 86916699226346257617377)
                  ·
                    rfl

theorem cell23_1523427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3, 5].length) (baseStart_1523427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523427 prefixEnd_1523427 := by exact prefixLift 1523427
  have htrace : WordTrace (prefixWord ++ tailWord_1523427) baseStart_1523427 baseEnd_1523427 := by
    simpa [prefixWord, tailWord_1523427, baseEnd_1523427] using wordTrace_append hprefix tailTrace_1523427
  have hstable : (prefixWord ++ tailWord_1523427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523427).length < 2 ^ (prefixWord ++ tailWord_1523427).sum := by decide
  have hdescent : baseEnd_1523427 < baseStart_1523427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523443 : List Nat := [1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 4]
def baseStart_1523443 : Nat := 118140960795 + 1523443 * 2 ^ 59
def prefixEnd_1523443 : Nat := 4983230072969 + 3 ^ 40 * 1523443 * 2
def baseEnd_1523443 : Nat := 782258508727588255956319

theorem tailTrace_1523443 : CollatzResearch.WordTrace tailWord_1523443 prefixEnd_1523443 782258508727588255956319 := by
  unfold tailWord_1523443
  simp only [CollatzResearch.WordTrace]
  refine ⟨55564531019833669195254983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37043020679889112796836655 55564531019833669195254983)
  ·
    refine ⟨83346796529750503792882475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55564531019833669195254983 83346796529750503792882475)
    ·
      refine ⟨125020194794625755689323713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83346796529750503792882475 125020194794625755689323713)
      ·
        refine ⟨93765146095969316766992785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125020194794625755689323713 93765146095969316766992785)
        ·
          refine ⟨70323859571976987575244589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93765146095969316766992785 70323859571976987575244589)
          ·
            refine ⟨26371447339491370340716721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70323859571976987575244589 26371447339491370340716721)
            ·
              refine ⟨19778585504618527755537541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26371447339491370340716721 19778585504618527755537541)
              ·
                refine ⟨3708484782115973954163289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19778585504618527755537541 3708484782115973954163289)
                ·
                  refine ⟨2781363586586980465622467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3708484782115973954163289 2781363586586980465622467)
                  ·
                    refine ⟨4172045379880470698433701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2781363586586980465622467 4172045379880470698433701)
                    ·
                      refine ⟨782258508727588255956319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4172045379880470698433701 782258508727588255956319)
                      ·
                        rfl

theorem cell23_1523443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 4].length) (baseStart_1523443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523443 prefixEnd_1523443 := by exact prefixLift 1523443
  have htrace : WordTrace (prefixWord ++ tailWord_1523443) baseStart_1523443 baseEnd_1523443 := by
    simpa [prefixWord, tailWord_1523443, baseEnd_1523443] using wordTrace_append hprefix tailTrace_1523443
  have hstable : (prefixWord ++ tailWord_1523443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523443).length < 2 ^ (prefixWord ++ tailWord_1523443).sum := by decide
  have hdescent : baseEnd_1523443 < baseStart_1523443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523444 : List Nat := [2, 6, 1, 1, 1, 1, 2, 4, 5]
def baseStart_1523444 : Nat := 118140960795 + 1523444 * 2 ^ 59
def prefixEnd_1523444 : Nat := 4983230072969 + 3 ^ 40 * 1523444 * 2
def baseEnd_1523444 : Nat := 86917669134249194671535

theorem tailTrace_1523444 : CollatzResearch.WordTrace tailWord_1523444 prefixEnd_1523444 86917669134249194671535 := by
  unfold tailWord_1523444
  simp only [CollatzResearch.WordTrace]
  refine ⟨27782283746415023183020693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37043044995220030910694257 27782283746415023183020693)
  ·
    refine ⟨1302294550613204211704095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27782283746415023183020693 1302294550613204211704095)
    ·
      refine ⟨1953441825919806317556143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1302294550613204211704095 1953441825919806317556143)
      ·
        refine ⟨2930162738879709476334215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1953441825919806317556143 2930162738879709476334215)
        ·
          refine ⟨4395244108319564214501323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2930162738879709476334215 4395244108319564214501323)
          ·
            refine ⟨6592866162479346321751985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4395244108319564214501323 6592866162479346321751985)
            ·
              refine ⟨4944649621859509741313989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6592866162479346321751985 4944649621859509741313989)
              ·
                refine ⟨927121804098658076496373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4944649621859509741313989 927121804098658076496373)
                ·
                  refine ⟨86917669134249194671535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 927121804098658076496373 86917669134249194671535)
                  ·
                    rfl

theorem cell23_1523444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_1523444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523444 prefixEnd_1523444 := by exact prefixLift 1523444
  have htrace : WordTrace (prefixWord ++ tailWord_1523444) baseStart_1523444 baseEnd_1523444 := by
    simpa [prefixWord, tailWord_1523444, baseEnd_1523444] using wordTrace_append hprefix tailTrace_1523444
  have hstable : (prefixWord ++ tailWord_1523444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523444).length < 2 ^ (prefixWord ++ tailWord_1523444).sum := by decide
  have hdescent : baseEnd_1523444 < baseStart_1523444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523470 : List Nat := [4, 1, 1, 2, 1, 1, 4, 2, 3, 4]
def baseStart_1523470 : Nat := 118140960795 + 1523470 * 2 ^ 59
def prefixEnd_1523470 : Nat := 4983230072969 + 3 ^ 40 * 1523470 * 2
def baseEnd_1523470 : Nat := 260757457568419883439565

theorem tailTrace_1523470 : CollatzResearch.WordTrace tailWord_1523470 prefixEnd_1523470 260757457568419883439565 := by
  unfold tailWord_1523470
  simp only [CollatzResearch.WordTrace]
  refine ⟨6945689473841981600810983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37043677193823901870991909 6945689473841981600810983)
  ·
    refine ⟨10418534210762972401216475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6945689473841981600810983 10418534210762972401216475)
    ·
      refine ⟨15627801316144458601824713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10418534210762972401216475 15627801316144458601824713)
      ·
        refine ⟨11720850987108343951368535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15627801316144458601824713 11720850987108343951368535)
        ·
          refine ⟨17581276480662515927052803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11720850987108343951368535 17581276480662515927052803)
          ·
            refine ⟨26371914720993773890579205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17581276480662515927052803 26371914720993773890579205)
            ·
              refine ⟨4944734010186332604483601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26371914720993773890579205 4944734010186332604483601)
              ·
                refine ⟨3708550507639749453362701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4944734010186332604483601 3708550507639749453362701)
                ·
                  refine ⟨1390706440364906045011013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3708550507639749453362701 1390706440364906045011013)
                  ·
                    refine ⟨260757457568419883439565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1390706440364906045011013 260757457568419883439565)
                    ·
                      rfl

theorem cell23_1523470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_1523470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523470 prefixEnd_1523470 := by exact prefixLift 1523470
  have htrace : WordTrace (prefixWord ++ tailWord_1523470) baseStart_1523470 baseEnd_1523470 := by
    simpa [prefixWord, tailWord_1523470, baseEnd_1523470] using wordTrace_append hprefix tailTrace_1523470
  have hstable : (prefixWord ++ tailWord_1523470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523470).length < 2 ^ (prefixWord ++ tailWord_1523470).sum := by decide
  have hdescent : baseEnd_1523470 < baseStart_1523470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523517 : List Nat := [1, 4, 1, 4, 1, 1, 4, 1, 6]
def baseStart_1523517 : Nat := 118140960795 + 1523517 * 2 ^ 59
def prefixEnd_1523517 : Nat := 4983230072969 + 3 ^ 40 * 1523517 * 2
def baseEnd_1523517 : Nat := 86921834032891218492331

theorem tailTrace_1523517 : CollatzResearch.WordTrace tailWord_1523517 prefixEnd_1523517 86921834032891218492331 := by
  unfold tailWord_1523517
  simp only [CollatzResearch.WordTrace]
  refine ⟨55567230021565579833448805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37044820014377053222299203 55567230021565579833448805)
  ·
    refine ⟨10418855629043546218771651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55567230021565579833448805 10418855629043546218771651)
    ·
      refine ⟨15628283443565319328157477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10418855629043546218771651 15628283443565319328157477)
      ·
        refine ⟨2930303145668497374029527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15628283443565319328157477 2930303145668497374029527)
        ·
          refine ⟨4395454718502746061044291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2930303145668497374029527 4395454718502746061044291)
          ·
            refine ⟨6593182077754119091566437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4395454718502746061044291 6593182077754119091566437)
            ·
              refine ⟨1236221639578897329668707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6593182077754119091566437 1236221639578897329668707)
              ·
                refine ⟨1854332459368345994503061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1236221639578897329668707 1854332459368345994503061)
                ·
                  refine ⟨86921834032891218492331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1854332459368345994503061 86921834032891218492331)
                  ·
                    rfl

theorem cell23_1523517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 6].length) (baseStart_1523517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523517 prefixEnd_1523517 := by exact prefixLift 1523517
  have htrace : WordTrace (prefixWord ++ tailWord_1523517) baseStart_1523517 baseEnd_1523517 := by
    simpa [prefixWord, tailWord_1523517, baseEnd_1523517] using wordTrace_append hprefix tailTrace_1523517
  have hstable : (prefixWord ++ tailWord_1523517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523517).length < 2 ^ (prefixWord ++ tailWord_1523517).sum := by decide
  have hdescent : baseEnd_1523517 < baseStart_1523517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523537 : List Nat := [1, 2, 2, 1, 5, 1, 1, 3, 2, 3, 2]
def baseStart_1523537 : Nat := 118140960795 + 1523537 * 2 ^ 59
def prefixEnd_1523537 : Nat := 4983230072969 + 3 ^ 40 * 1523537 * 2
def baseEnd_1523537 : Nat := 782306775909110888180887

theorem tailTrace_1523537 : CollatzResearch.WordTrace tailWord_1523537 prefixEnd_1523537 782306775909110888180887 := by
  unfold tailWord_1523537
  simp only [CollatzResearch.WordTrace]
  refine ⟨55567959481493123249176865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37045306320995415499451243 55567959481493123249176865)
  ·
    refine ⟨41675969611119842436882649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55567959481493123249176865 41675969611119842436882649)
    ·
      refine ⟨31256977208339881827661987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41675969611119842436882649 31256977208339881827661987)
      ·
        refine ⟨46885465812509822741492981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31256977208339881827661987 46885465812509822741492981)
        ·
          refine ⟨4395512419922795882014967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46885465812509822741492981 4395512419922795882014967)
          ·
            refine ⟨6593268629884193823022451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4395512419922795882014967 6593268629884193823022451)
            ·
              refine ⟨9889902944826290734533677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6593268629884193823022451 9889902944826290734533677)
              ·
                refine ⟨3708713604309859025450129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9889902944826290734533677 3708713604309859025450129)
                ·
                  refine ⟨2781535203232394269087597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3708713604309859025450129 2781535203232394269087597)
                  ·
                    refine ⟨1043075701212147850907849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2781535203232394269087597 1043075701212147850907849)
                    ·
                      refine ⟨782306775909110888180887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1043075701212147850907849 782306775909110888180887)
                      ·
                        rfl

theorem cell23_1523537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 3, 2].length) (baseStart_1523537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523537 prefixEnd_1523537 := by exact prefixLift 1523537
  have htrace : WordTrace (prefixWord ++ tailWord_1523537) baseStart_1523537 baseEnd_1523537 := by
    simpa [prefixWord, tailWord_1523537, baseEnd_1523537] using wordTrace_append hprefix tailTrace_1523537
  have hstable : (prefixWord ++ tailWord_1523537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523537).length < 2 ^ (prefixWord ++ tailWord_1523537).sum := by decide
  have hdescent : baseEnd_1523537 < baseStart_1523537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523554 : List Nat := [3, 3, 2, 1, 2, 1, 2, 2, 2, 3, 2]
def baseStart_1523554 : Nat := 118140960795 + 1523554 * 2 ^ 59
def prefixEnd_1523554 : Nat := 4983230072969 + 3 ^ 40 * 1523554 * 2
def baseEnd_1523554 : Nat := 782315505080237321668309

theorem tailTrace_1523554 : CollatzResearch.WordTrace tailWord_1523554 prefixEnd_1523554 782315505080237321668309 := by
  unfold tailWord_1523554
  simp only [CollatzResearch.WordTrace]
  refine ⟨13892144880607883788136429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37045719681621023435030477 13892144880607883788136429)
  ·
    refine ⟨5209554330227956420551161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13892144880607883788136429 5209554330227956420551161)
    ·
      refine ⟨3907165747670967315413371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5209554330227956420551161 3907165747670967315413371)
      ·
        refine ⟨5860748621506450973120057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3907165747670967315413371 5860748621506450973120057)
        ·
          refine ⟨4395561466129838229840043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5860748621506450973120057 4395561466129838229840043)
          ·
            refine ⟨6593342199194757344760065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4395561466129838229840043 6593342199194757344760065)
            ·
              refine ⟨4945006649396068008570049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6593342199194757344760065 4945006649396068008570049)
              ·
                refine ⟨3708754987047051006427537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4945006649396068008570049 3708754987047051006427537)
                ·
                  refine ⟨2781566240285288254820653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3708754987047051006427537 2781566240285288254820653)
                  ·
                    refine ⟨1043087340106983095557745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2781566240285288254820653 1043087340106983095557745)
                    ·
                      refine ⟨782315505080237321668309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1043087340106983095557745 782315505080237321668309)
                      ·
                        rfl

theorem cell23_1523554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_1523554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523554 prefixEnd_1523554 := by exact prefixLift 1523554
  have htrace : WordTrace (prefixWord ++ tailWord_1523554) baseStart_1523554 baseEnd_1523554 := by
    simpa [prefixWord, tailWord_1523554, baseEnd_1523554] using wordTrace_append hprefix tailTrace_1523554
  have hstable : (prefixWord ++ tailWord_1523554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523554).length < 2 ^ (prefixWord ++ tailWord_1523554).sum := by decide
  have hdescent : baseEnd_1523554 < baseStart_1523554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523563 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 4]
def baseStart_1523563 : Nat := 118140960795 + 1523563 * 2 ^ 59
def prefixEnd_1523563 : Nat := 4983230072969 + 3 ^ 40 * 1523563 * 2
def baseEnd_1523563 : Nat := 782320126406127786455767

theorem tailTrace_1523563 : CollatzResearch.WordTrace tailWord_1523563 prefixEnd_1523563 782320126406127786455767 := by
  unfold tailWord_1523563
  simp only [CollatzResearch.WordTrace]
  refine ⟨55568907779398929689623343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37045938519599286459748895 55568907779398929689623343)
  ·
    refine ⟨83353361669098394534435015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55568907779398929689623343 83353361669098394534435015)
    ·
      refine ⟨125030042503647591801652523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83353361669098394534435015 125030042503647591801652523)
      ·
        refine ⟨187545063755471387702478785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125030042503647591801652523 187545063755471387702478785)
        ·
          refine ⟨140658797816603540776859089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187545063755471387702478785 140658797816603540776859089)
          ·
            refine ⟨105494098362452655582644317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140658797816603540776859089 105494098362452655582644317)
            ·
              refine ⟨39560286885919745843491619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105494098362452655582644317 39560286885919745843491619)
              ·
                refine ⟨59340430328879618765237429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39560286885919745843491619 59340430328879618765237429)
                ·
                  refine ⟨5563165343332464259241009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59340430328879618765237429 5563165343332464259241009)
                  ·
                    refine ⟨4172374007499348194430757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5563165343332464259241009 4172374007499348194430757)
                    ·
                      refine ⟨782320126406127786455767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4172374007499348194430757 782320126406127786455767)
                      ·
                        rfl

theorem cell23_1523563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 4].length) (baseStart_1523563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523563 prefixEnd_1523563 := by exact prefixLift 1523563
  have htrace : WordTrace (prefixWord ++ tailWord_1523563) baseStart_1523563 baseEnd_1523563 := by
    simpa [prefixWord, tailWord_1523563, baseEnd_1523563] using wordTrace_append hprefix tailTrace_1523563
  have hstable : (prefixWord ++ tailWord_1523563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523563).length < 2 ^ (prefixWord ++ tailWord_1523563).sum := by decide
  have hdescent : baseEnd_1523563 < baseStart_1523563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523598 : List Nat := [4, 1, 1, 5, 2, 1, 2, 1, 1, 5]
def baseStart_1523598 : Nat := 118140960795 + 1523598 * 2 ^ 59
def prefixEnd_1523598 : Nat := 4983230072969 + 3 ^ 40 * 1523598 * 2
def baseEnd_1523598 : Nat := 260779366076345049839369

theorem tailTrace_1523598 : CollatzResearch.WordTrace tailWord_1523598 prefixEnd_1523598 260779366076345049839369 := by
  unfold tailWord_1523598
  simp only [CollatzResearch.WordTrace]
  refine ⟨6946273041784016333393431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37046789556181420444764965 6946273041784016333393431)
  ·
    refine ⟨10419409562676024500090147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6946273041784016333393431 10419409562676024500090147)
    ·
      refine ⟨15629114344014036750135221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10419409562676024500090147 15629114344014036750135221)
      ·
        refine ⟨1465229469751315945325177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15629114344014036750135221 1465229469751315945325177)
        ·
          refine ⟨1098922102313486958993883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1465229469751315945325177 1098922102313486958993883)
          ·
            refine ⟨1648383153470230438490825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1098922102313486958993883 1648383153470230438490825)
            ·
              refine ⟨1236287365102672828868119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1648383153470230438490825 1236287365102672828868119)
              ·
                refine ⟨1854431047654009243302179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1236287365102672828868119 1854431047654009243302179)
                ·
                  refine ⟨2781646571481013864953269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1854431047654009243302179 2781646571481013864953269)
                  ·
                    refine ⟨260779366076345049839369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2781646571481013864953269 260779366076345049839369)
                    ·
                      rfl

theorem cell23_1523598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_1523598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523598 prefixEnd_1523598 := by exact prefixLift 1523598
  have htrace : WordTrace (prefixWord ++ tailWord_1523598) baseStart_1523598 baseEnd_1523598 := by
    simpa [prefixWord, tailWord_1523598, baseEnd_1523598] using wordTrace_append hprefix tailTrace_1523598
  have hstable : (prefixWord ++ tailWord_1523598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523598).length < 2 ^ (prefixWord ++ tailWord_1523598).sum := by decide
  have hdescent : baseEnd_1523598 < baseStart_1523598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523604 : List Nat := [2, 4, 2, 1, 1, 3, 1, 3, 1, 2, 3]
def baseStart_1523604 : Nat := 118140960795 + 1523604 * 2 ^ 59
def prefixEnd_1523604 : Nat := 4983230072969 + 3 ^ 40 * 1523604 * 2
def baseEnd_1523604 : Nat := 782341179112962126043079

theorem tailTrace_1523604 : CollatzResearch.WordTrace tailWord_1523604 prefixEnd_1523604 782341179112962126043079 := by
  unfold tailWord_1523604
  simp only [CollatzResearch.WordTrace]
  refine ⟨27785201586125196845932933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37046935448166929127910577 27785201586125196845932933)
  ·
    refine ⟨5209725297398474408612425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27785201586125196845932933 5209725297398474408612425)
    ·
      refine ⟨3907293973048855806459319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5209725297398474408612425 3907293973048855806459319)
      ·
        refine ⟨5860940959573283709688979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3907293973048855806459319 5860940959573283709688979)
        ·
          refine ⟨8791411439359925564533469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5860940959573283709688979 8791411439359925564533469)
          ·
            refine ⟨3296779289759972086700051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8791411439359925564533469 3296779289759972086700051)
            ·
              refine ⟨4945168934639958130050077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3296779289759972086700051 4945168934639958130050077)
              ·
                refine ⟨1854438350489984298768779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4945168934639958130050077 1854438350489984298768779)
                ·
                  refine ⟨2781657525734976448153169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1854438350489984298768779 2781657525734976448153169)
                  ·
                    refine ⟨2086243144301232336114877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2781657525734976448153169 2086243144301232336114877)
                    ·
                      refine ⟨782341179112962126043079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2086243144301232336114877 782341179112962126043079)
                      ·
                        rfl

theorem cell23_1523604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_1523604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523604 prefixEnd_1523604 := by exact prefixLift 1523604
  have htrace : WordTrace (prefixWord ++ tailWord_1523604) baseStart_1523604 baseEnd_1523604 := by
    simpa [prefixWord, tailWord_1523604, baseEnd_1523604] using wordTrace_append hprefix tailTrace_1523604
  have hstable : (prefixWord ++ tailWord_1523604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523604).length < 2 ^ (prefixWord ++ tailWord_1523604).sum := by decide
  have hdescent : baseEnd_1523604 < baseStart_1523604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523660 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 1, 3, 5]
def baseStart_1523660 : Nat := 118140960795 + 1523660 * 2 ^ 59
def prefixEnd_1523660 : Nat := 4983230072969 + 3 ^ 40 * 1523660 * 2
def baseEnd_1523660 : Nat := 782369934029613906942821

theorem tailTrace_1523660 : CollatzResearch.WordTrace tailWord_1523660 prefixEnd_1523660 782369934029613906942821 := by
  unfold tailWord_1523660
  simp only [CollatzResearch.WordTrace]
  refine ⟨27786222830023757627952217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37048297106698343503936289 27786222830023757627952217)
  ·
    refine ⟨20839667122517818220964163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27786222830023757627952217 20839667122517818220964163)
    ·
      refine ⟨31259500683776727331446245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20839667122517818220964163 31259500683776727331446245)
      ·
        refine ⟨5861156378208136374646171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31259500683776727331446245 5861156378208136374646171)
        ·
          refine ⟨8791734567312204561969257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5861156378208136374646171 8791734567312204561969257)
          ·
            refine ⟨6593800925484153421476943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8791734567312204561969257 6593800925484153421476943)
            ·
              refine ⟨9890701388226230132215415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6593800925484153421476943 9890701388226230132215415)
              ·
                refine ⟨14836052082339345198323123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9890701388226230132215415 14836052082339345198323123)
                ·
                  refine ⟨22254078123509017797484685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14836052082339345198323123 22254078123509017797484685)
                  ·
                    refine ⟨8345279296315881674056757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22254078123509017797484685 8345279296315881674056757)
                    ·
                      refine ⟨782369934029613906942821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8345279296315881674056757 782369934029613906942821)
                      ·
                        rfl

theorem cell23_1523660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_1523660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523660 prefixEnd_1523660 := by exact prefixLift 1523660
  have htrace : WordTrace (prefixWord ++ tailWord_1523660) baseStart_1523660 baseEnd_1523660 := by
    simpa [prefixWord, tailWord_1523660, baseEnd_1523660] using wordTrace_append hprefix tailTrace_1523660
  have hstable : (prefixWord ++ tailWord_1523660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523660).length < 2 ^ (prefixWord ++ tailWord_1523660).sum := by decide
  have hdescent : baseEnd_1523660 < baseStart_1523660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523720 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 3, 2, 5]
def baseStart_1523720 : Nat := 118140960795 + 1523720 * 2 ^ 59
def prefixEnd_1523720 : Nat := 4983230072969 + 3 ^ 40 * 1523720 * 2
def baseEnd_1523720 : Nat := 782400742868883672192545

theorem tailTrace_1523720 : CollatzResearch.WordTrace tailWord_1523720 prefixEnd_1523720 782400742868883672192545 := by
  unfold tailWord_1523720
  simp only [CollatzResearch.WordTrace]
  refine ⟨27787317019915072751544307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37049756026553430335392409 27787317019915072751544307)
  ·
    refine ⟨41680975529872609127316461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27787317019915072751544307 41680975529872609127316461)
    ·
      refine ⟨15630365823702228422743673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41680975529872609127316461 15630365823702228422743673)
      ·
        refine ⟨11722774367776671317057755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15630365823702228422743673 11722774367776671317057755)
        ·
          refine ⟨17584161551665006975586633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11722774367776671317057755 17584161551665006975586633)
          ·
            refine ⟨13188121163748755231689975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17584161551665006975586633 13188121163748755231689975)
            ·
              refine ⟨19782181745623132847534963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13188121163748755231689975 19782181745623132847534963)
              ·
                refine ⟨29673272618434699271302445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19782181745623132847534963 29673272618434699271302445)
                ·
                  refine ⟨11127477231913012226738417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29673272618434699271302445 11127477231913012226738417)
                  ·
                    refine ⟨8345607923934759170053813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11127477231913012226738417 8345607923934759170053813)
                    ·
                      refine ⟨782400742868883672192545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8345607923934759170053813 782400742868883672192545)
                      ·
                        rfl

theorem cell23_1523720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_1523720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523720 prefixEnd_1523720 := by exact prefixLift 1523720
  have htrace : WordTrace (prefixWord ++ tailWord_1523720) baseStart_1523720 baseEnd_1523720 := by
    simpa [prefixWord, tailWord_1523720, baseEnd_1523720] using wordTrace_append hprefix tailTrace_1523720
  have hstable : (prefixWord ++ tailWord_1523720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523720).length < 2 ^ (prefixWord ++ tailWord_1523720).sum := by decide
  have hdescent : baseEnd_1523720 < baseStart_1523720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523770 : List Nat := [3, 1, 1, 1, 3, 1, 1, 4, 8]
def baseStart_1523770 : Nat := 118140960795 + 1523770 * 2 ^ 59
def prefixEnd_1523770 : Nat := 4983230072969 + 3 ^ 40 * 1523770 * 2
def baseEnd_1523770 : Nat := 86936268544623164063035

theorem tailTrace_1523770 : CollatzResearch.WordTrace tailWord_1523770 prefixEnd_1523770 86936268544623164063035 := by
  unfold tailWord_1523770
  simp only [CollatzResearch.WordTrace]
  refine ⟨13894114422412251010602191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37050971793099336028272509 13894114422412251010602191)
  ·
    refine ⟨20841171633618376515903287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13894114422412251010602191 20841171633618376515903287)
    ·
      refine ⟨31261757450427564773854931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20841171633618376515903287 31261757450427564773854931)
      ·
        refine ⟨46892636175641347160782397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31261757450427564773854931 46892636175641347160782397)
        ·
          refine ⟨17584738565865505185293399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46892636175641347160782397 17584738565865505185293399)
          ·
            refine ⟨26377107848798257777940099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17584738565865505185293399 26377107848798257777940099)
            ·
              refine ⟨39565661773197386666910149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26377107848798257777940099 39565661773197386666910149)
              ·
                refine ⟨7418561582474510000045653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39565661773197386666910149 7418561582474510000045653)
                ·
                  refine ⟨86936268544623164063035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7418561582474510000045653 86936268544623164063035)
                  ·
                    rfl

theorem cell23_1523770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 8].length) (baseStart_1523770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523770 prefixEnd_1523770 := by exact prefixLift 1523770
  have htrace : WordTrace (prefixWord ++ tailWord_1523770) baseStart_1523770 baseEnd_1523770 := by
    simpa [prefixWord, tailWord_1523770, baseEnd_1523770] using wordTrace_append hprefix tailTrace_1523770
  have hstable : (prefixWord ++ tailWord_1523770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523770).length < 2 ^ (prefixWord ++ tailWord_1523770).sum := by decide
  have hdescent : baseEnd_1523770 < baseStart_1523770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523777 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_1523777 : Nat := 118140960795 + 1523777 * 2 ^ 59
def prefixEnd_1523777 : Nat := 4983230072969 + 3 ^ 40 * 1523777 * 2
def baseEnd_1523777 : Nat := 782430011266189949179783

theorem tailTrace_1523777 : CollatzResearch.WordTrace tailWord_1523777 prefixEnd_1523777 782430011266189949179783 := by
  unfold tailWord_1523777
  simp only [CollatzResearch.WordTrace]
  refine ⟨55576713000623644237913585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37051142000415762825275723 55576713000623644237913585)
  ·
    refine ⟨41682534750467733178435189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55576713000623644237913585 41682534750467733178435189)
    ·
      refine ⟨3907737632856349985478299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41682534750467733178435189 3907737632856349985478299)
      ·
        refine ⟨5861606449284524978217449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3907737632856349985478299 5861606449284524978217449)
        ·
          refine ⟨4396204836963393733663087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5861606449284524978217449 4396204836963393733663087)
          ·
            refine ⟨6594307255445090600494631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4396204836963393733663087 6594307255445090600494631)
            ·
              refine ⟨9891460883167635900741947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6594307255445090600494631 9891460883167635900741947)
              ·
                refine ⟨14837191324751453851112921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9891460883167635900741947 14837191324751453851112921)
                ·
                  refine ⟨11127893493563590388334691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14837191324751453851112921 11127893493563590388334691)
                  ·
                    refine ⟨16691840240345385582502037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11127893493563590388334691 16691840240345385582502037)
                    ·
                      refine ⟨782430011266189949179783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16691840240345385582502037 782430011266189949179783)
                      ·
                        rfl

theorem cell23_1523777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_1523777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523777 prefixEnd_1523777 := by exact prefixLift 1523777
  have htrace : WordTrace (prefixWord ++ tailWord_1523777) baseStart_1523777 baseEnd_1523777 := by
    simpa [prefixWord, tailWord_1523777, baseEnd_1523777] using wordTrace_append hprefix tailTrace_1523777
  have hstable : (prefixWord ++ tailWord_1523777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523777).length < 2 ^ (prefixWord ++ tailWord_1523777).sum := by decide
  have hdescent : baseEnd_1523777 < baseStart_1523777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523798 : List Nat := [5, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2]
def baseStart_1523798 : Nat := 118140960795 + 1523798 * 2 ^ 59
def prefixEnd_1523798 : Nat := 4983230072969 + 3 ^ 40 * 1523798 * 2
def baseEnd_1523798 : Nat := 782440794359934367017187

theorem tailTrace_1523798 : CollatzResearch.WordTrace tailWord_1523798 prefixEnd_1523798 782440794359934367017187 := by
  unfold tailWord_1523798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3473592433346722801526753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37051652622365043216285365 3473592433346722801526753)
  ·
    refine ⟨2605194325010042101145065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3473592433346722801526753 2605194325010042101145065)
    ·
      refine ⟨1953895743757531575858799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2605194325010042101145065 1953895743757531575858799)
      ·
        refine ⟨2930843615636297363788199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1953895743757531575858799 2930843615636297363788199)
        ·
          refine ⟨4396265423454446045682299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2930843615636297363788199 4396265423454446045682299)
          ·
            refine ⟨6594398135181669068523449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4396265423454446045682299 6594398135181669068523449)
            ·
              refine ⟨4945798601386251801392587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6594398135181669068523449 4945798601386251801392587)
              ·
                refine ⟨7418697902079377702088881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4945798601386251801392587 7418697902079377702088881)
                ·
                  refine ⟨5564023426559533276566661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7418697902079377702088881 5564023426559533276566661)
                  ·
                    refine ⟨1043254392479912489356249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5564023426559533276566661 1043254392479912489356249)
                    ·
                      refine ⟨782440794359934367017187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1043254392479912489356249 782440794359934367017187)
                      ·
                        rfl

theorem cell23_1523798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_1523798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523798 prefixEnd_1523798 := by exact prefixLift 1523798
  have htrace : WordTrace (prefixWord ++ tailWord_1523798) baseStart_1523798 baseEnd_1523798 := by
    simpa [prefixWord, tailWord_1523798, baseEnd_1523798] using wordTrace_append hprefix tailTrace_1523798
  have hstable : (prefixWord ++ tailWord_1523798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523798).length < 2 ^ (prefixWord ++ tailWord_1523798).sum := by decide
  have hdescent : baseEnd_1523798 < baseStart_1523798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523824 : List Nat := [2, 1, 1, 1, 5, 2, 2, 1, 1, 5, 2]
def baseStart_1523824 : Nat := 118140960795 + 1523824 * 2 ^ 59
def prefixEnd_1523824 : Nat := 4983230072969 + 3 ^ 40 * 1523824 * 2
def baseEnd_1523824 : Nat := 782454144856951265292067

theorem tailTrace_1523824 : CollatzResearch.WordTrace tailWord_1523824 prefixEnd_1523824 782454144856951265292067 := by
  unfold tailWord_1523824
  simp only [CollatzResearch.WordTrace]
  refine ⟨27789213615726685632437263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37052284820968914176583017 27789213615726685632437263)
  ·
    refine ⟨41683820423590028448655895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27789213615726685632437263 41683820423590028448655895)
    ·
      refine ⟨62525730635385042672983843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41683820423590028448655895 62525730635385042672983843)
      ·
        refine ⟨93788595953077564009475765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62525730635385042672983843 93788595953077564009475765)
        ·
          refine ⟨8792680870601021625888353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93788595953077564009475765 8792680870601021625888353)
          ·
            refine ⟨6594510652950766219416265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8792680870601021625888353 6594510652950766219416265)
            ·
              refine ⟨4945882989713074664562199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6594510652950766219416265 4945882989713074664562199)
              ·
                refine ⟨7418824484569611996843299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4945882989713074664562199 7418824484569611996843299)
                ·
                  refine ⟨11128236726854417995264949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7418824484569611996843299 11128236726854417995264949)
                  ·
                    refine ⟨1043272193142601687056089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11128236726854417995264949 1043272193142601687056089)
                    ·
                      refine ⟨782454144856951265292067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1043272193142601687056089 782454144856951265292067)
                      ·
                        rfl

theorem cell23_1523824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 1, 5, 2].length) (baseStart_1523824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523824 prefixEnd_1523824 := by exact prefixLift 1523824
  have htrace : WordTrace (prefixWord ++ tailWord_1523824) baseStart_1523824 baseEnd_1523824 := by
    simpa [prefixWord, tailWord_1523824, baseEnd_1523824] using wordTrace_append hprefix tailTrace_1523824
  have hstable : (prefixWord ++ tailWord_1523824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523824).length < 2 ^ (prefixWord ++ tailWord_1523824).sum := by decide
  have hdescent : baseEnd_1523824 < baseStart_1523824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523848 : List Nat := [2, 1, 3, 4, 1, 3, 1, 1, 3, 1, 3]
def baseStart_1523848 : Nat := 118140960795 + 1523848 * 2 ^ 59
def prefixEnd_1523848 : Nat := 4983230072969 + 3 ^ 40 * 1523848 * 2
def baseEnd_1523848 : Nat := 782466468392659171391957

theorem tailTrace_1523848 : CollatzResearch.WordTrace tailWord_1523848 prefixEnd_1523848 782466468392659171391957 := by
  unfold tailWord_1523848
  simp only [CollatzResearch.WordTrace]
  refine ⟨27789651291683211681874099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37052868388910948909165465 27789651291683211681874099)
  ·
    refine ⟨41684476937524817522811149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27789651291683211681874099 41684476937524817522811149)
    ·
      refine ⟨15631678851571806571054181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41684476937524817522811149 15631678851571806571054181)
      ·
        refine ⟨2930939784669713732072659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15631678851571806571054181 2930939784669713732072659)
        ·
          refine ⟨4396409677004570598108989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2930939784669713732072659 4396409677004570598108989)
          ·
            refine ⟨1648653628876713974290871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4396409677004570598108989 1648653628876713974290871)
            ·
              refine ⟨2472980443315070961436307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1648653628876713974290871 2472980443315070961436307)
              ·
                refine ⟨3709470664972606442154461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2472980443315070961436307 3709470664972606442154461)
                ·
                  refine ⟨1391051499364727415807923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3709470664972606442154461 1391051499364727415807923)
                  ·
                    refine ⟨2086577249047091123711885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1391051499364727415807923 2086577249047091123711885)
                    ·
                      refine ⟨782466468392659171391957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2086577249047091123711885 782466468392659171391957)
                      ·
                        rfl

theorem cell23_1523848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_1523848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523848 prefixEnd_1523848 := by exact prefixLift 1523848
  have htrace : WordTrace (prefixWord ++ tailWord_1523848) baseStart_1523848 baseEnd_1523848 := by
    simpa [prefixWord, tailWord_1523848, baseEnd_1523848] using wordTrace_append hprefix tailTrace_1523848
  have hstable : (prefixWord ++ tailWord_1523848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523848).length < 2 ^ (prefixWord ++ tailWord_1523848).sum := by decide
  have hdescent : baseEnd_1523848 < baseStart_1523848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523871 : List Nat := [1, 1, 2, 6, 1, 1, 3, 2, 1, 1, 4]
def baseStart_1523871 : Nat := 118140960795 + 1523871 * 2 ^ 59
def prefixEnd_1523871 : Nat := 4983230072969 + 3 ^ 40 * 1523871 * 2
def baseEnd_1523871 : Nat := 782478278447712581404351

theorem tailTrace_1523871 : CollatzResearch.WordTrace tailWord_1523871 prefixEnd_1523871 782478278447712581404351 := by
  unfold tailWord_1523871
  simp only [CollatzResearch.WordTrace]
  refine ⟨55580141462283098291835467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37053427641522065527890311 55580141462283098291835467)
  ·
    refine ⟨83370212193424647437753201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55580141462283098291835467 83370212193424647437753201)
    ·
      refine ⟨62527659145068485578314901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83370212193424647437753201 62527659145068485578314901)
      ·
        refine ⟨2930984022425085261483511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 62527659145068485578314901 2930984022425085261483511)
        ·
          refine ⟨4396476033637627892225267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2930984022425085261483511 4396476033637627892225267)
          ·
            refine ⟨6594714050456441838337901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4396476033637627892225267 6594714050456441838337901)
            ·
              refine ⟨2473017768921165689376713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6594714050456441838337901 2473017768921165689376713)
              ·
                refine ⟨1854763326690874267032535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2473017768921165689376713 1854763326690874267032535)
                ·
                  refine ⟨2782144990036311400548803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1854763326690874267032535 2782144990036311400548803)
                  ·
                    refine ⟨4173217485054467100823205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2782144990036311400548803 4173217485054467100823205)
                    ·
                      refine ⟨782478278447712581404351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4173217485054467100823205 782478278447712581404351)
                      ·
                        rfl

theorem cell23_1523871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_1523871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523871 prefixEnd_1523871 := by exact prefixLift 1523871
  have htrace : WordTrace (prefixWord ++ tailWord_1523871) baseStart_1523871 baseEnd_1523871 := by
    simpa [prefixWord, tailWord_1523871, baseEnd_1523871] using wordTrace_append hprefix tailTrace_1523871
  have hstable : (prefixWord ++ tailWord_1523871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523871).length < 2 ^ (prefixWord ++ tailWord_1523871).sum := by decide
  have hdescent : baseEnd_1523871 < baseStart_1523871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523921 : List Nat := [1, 2, 2, 1, 2, 2, 4, 3, 2, 1, 3]
def baseStart_1523921 : Nat := 118140960795 + 1523921 * 2 ^ 59
def prefixEnd_1523921 : Nat := 4983230072969 + 3 ^ 40 * 1523921 * 2
def baseEnd_1523921 : Nat := 782503952480437385779121

theorem tailTrace_1523921 : CollatzResearch.WordTrace tailWord_1523921 prefixEnd_1523921 782503952480437385779121 := by
  unfold tailWord_1523921
  simp only [CollatzResearch.WordTrace]
  refine ⟨55581965112101956831155617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37054643408067971220770411 55581965112101956831155617)
  ·
    refine ⟨41686473834076467623366713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55581965112101956831155617 41686473834076467623366713)
    ·
      refine ⟨31264855375557350717525035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41686473834076467623366713 31264855375557350717525035)
      ·
        refine ⟨46897283063336026076287553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31264855375557350717525035 46897283063336026076287553)
        ·
          refine ⟨35172962297502019557215665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46897283063336026076287553 35172962297502019557215665)
          ·
            refine ⟨26379721723126514667911749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35172962297502019557215665 26379721723126514667911749)
            ·
              refine ⟨4946197823086221500233453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26379721723126514667911749 4946197823086221500233453)
              ·
                refine ⟨1854824183657333062587545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4946197823086221500233453 1854824183657333062587545)
                ·
                  refine ⟨1391118137742999796940659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1854824183657333062587545 1391118137742999796940659)
                  ·
                    refine ⟨2086677206614499695410989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1391118137742999796940659 2086677206614499695410989)
                    ·
                      refine ⟨782503952480437385779121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2086677206614499695410989 782503952480437385779121)
                      ·
                        rfl

theorem cell23_1523921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2, 1, 3].length) (baseStart_1523921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523921 prefixEnd_1523921 := by exact prefixLift 1523921
  have htrace : WordTrace (prefixWord ++ tailWord_1523921) baseStart_1523921 baseEnd_1523921 := by
    simpa [prefixWord, tailWord_1523921, baseEnd_1523921] using wordTrace_append hprefix tailTrace_1523921
  have hstable : (prefixWord ++ tailWord_1523921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523921).length < 2 ^ (prefixWord ++ tailWord_1523921).sum := by decide
  have hdescent : baseEnd_1523921 < baseStart_1523921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523927 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 4]
def baseStart_1523927 : Nat := 118140960795 + 1523927 * 2 ^ 59
def prefixEnd_1523927 : Nat := 4983230072969 + 3 ^ 40 * 1523927 * 2
def baseEnd_1523927 : Nat := 782507033364364362304093

theorem tailTrace_1523927 : CollatzResearch.WordTrace tailWord_1523927 prefixEnd_1523927 782507033364364362304093 := by
  unfold tailWord_1523927
  simp only [CollatzResearch.WordTrace]
  refine ⟨55582183950080219855874035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37054789300053479903916023 55582183950080219855874035)
  ·
    refine ⟨83373275925120329783811053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55582183950080219855874035 83373275925120329783811053)
    ·
      refine ⟨31264978471920123668929145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83373275925120329783811053 31264978471920123668929145)
      ·
        refine ⟨23448733853940092751696859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31264978471920123668929145 23448733853940092751696859)
        ·
          refine ⟨35173100780910139127545289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23448733853940092751696859 35173100780910139127545289)
          ·
            refine ⟨26379825585682604345658967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35173100780910139127545289 26379825585682604345658967)
            ·
              refine ⟨39569738378523906518488451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26379825585682604345658967 39569738378523906518488451)
              ·
                refine ⟨59354607567785859777732677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39569738378523906518488451 59354607567785859777732677)
                ·
                  refine ⟨11128988918959848708324877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59354607567785859777732677 11128988918959848708324877)
                  ·
                    refine ⟨4173370844609943265621829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11128988918959848708324877 4173370844609943265621829)
                    ·
                      refine ⟨782507033364364362304093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4173370844609943265621829 782507033364364362304093)
                      ·
                        rfl

theorem cell23_1523927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_1523927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523927 prefixEnd_1523927 := by exact prefixLift 1523927
  have htrace : WordTrace (prefixWord ++ tailWord_1523927) baseStart_1523927 baseEnd_1523927 := by
    simpa [prefixWord, tailWord_1523927, baseEnd_1523927] using wordTrace_append hprefix tailTrace_1523927
  have hstable : (prefixWord ++ tailWord_1523927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523927).length < 2 ^ (prefixWord ++ tailWord_1523927).sum := by decide
  have hdescent : baseEnd_1523927 < baseStart_1523927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523937 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 1, 8]
def baseStart_1523937 : Nat := 118140960795 + 1523937 * 2 ^ 59
def prefixEnd_1523937 : Nat := 4983230072969 + 3 ^ 40 * 1523937 * 2
def baseEnd_1523937 : Nat := 260837389390303107726349

theorem tailTrace_1523937 : CollatzResearch.WordTrace tailWord_1523937 prefixEnd_1523937 260837389390303107726349 := by
  unfold tailWord_1523937
  simp only [CollatzResearch.WordTrace]
  refine ⟨55582548680043991563738065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37055032453362661042492043 55582548680043991563738065)
  ·
    refine ⟨41686911510032993672803549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55582548680043991563738065 41686911510032993672803549)
    ·
      refine ⟨15632591816262372627301331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41686911510032993672803549 15632591816262372627301331)
      ·
        refine ⟨23448887724393558940951997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15632591816262372627301331 23448887724393558940951997)
        ·
          refine ⟨8793332896647584602856999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23448887724393558940951997 8793332896647584602856999)
          ·
            refine ⟨13189999344971376904285499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8793332896647584602856999 13189999344971376904285499)
            ·
              refine ⟨19784999017457065356428249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13189999344971376904285499 19784999017457065356428249)
              ·
                refine ⟨14838749263092799017321187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19784999017457065356428249 14838749263092799017321187)
                ·
                  refine ⟨22258123894639198525981781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14838749263092799017321187 22258123894639198525981781)
                  ·
                    refine ⟨260837389390303107726349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 22258123894639198525981781 260837389390303107726349)
                    ·
                      rfl

theorem cell23_1523937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_1523937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523937 prefixEnd_1523937 := by exact prefixLift 1523937
  have htrace : WordTrace (prefixWord ++ tailWord_1523937) baseStart_1523937 baseEnd_1523937 := by
    simpa [prefixWord, tailWord_1523937, baseEnd_1523937] using wordTrace_append hprefix tailTrace_1523937
  have hstable : (prefixWord ++ tailWord_1523937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523937).length < 2 ^ (prefixWord ++ tailWord_1523937).sum := by decide
  have hdescent : baseEnd_1523937 < baseStart_1523937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523947 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 5]
def baseStart_1523947 : Nat := 118140960795 + 1523947 * 2 ^ 59
def prefixEnd_1523947 : Nat := 4983230072969 + 3 ^ 40 * 1523947 * 2
def baseEnd_1523947 : Nat := 782517302977454284054001

theorem tailTrace_1523947 : CollatzResearch.WordTrace tailWord_1523947 prefixEnd_1523947 782517302977454284054001 := by
  unfold tailWord_1523947
  simp only [CollatzResearch.WordTrace]
  refine ⟨55582913410007763271602095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37055275606671842181068063 55582913410007763271602095)
  ·
    refine ⟨83374370115011644907403143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55582913410007763271602095 83374370115011644907403143)
    ·
      refine ⟨125061555172517467361104715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83374370115011644907403143 125061555172517467361104715)
      ·
        refine ⟨187592332758776201041657073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125061555172517467361104715 187592332758776201041657073)
        ·
          refine ⟨140694249569082150781242805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187592332758776201041657073 140694249569082150781242805)
          ·
            refine ⟨13190085897101451635741513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140694249569082150781242805 13190085897101451635741513)
            ·
              refine ⟨9892564422826088726806135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13190085897101451635741513 9892564422826088726806135)
              ·
                refine ⟨14838846634239133090209203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9892564422826088726806135 14838846634239133090209203)
                ·
                  refine ⟨22258269951358699635313805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14838846634239133090209203 22258269951358699635313805)
                  ·
                    refine ⟨8346851231759512363242677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22258269951358699635313805 8346851231759512363242677)
                    ·
                      refine ⟨782517302977454284054001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8346851231759512363242677 782517302977454284054001)
                      ·
                        rfl

theorem cell23_1523947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 5].length) (baseStart_1523947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523947 prefixEnd_1523947 := by exact prefixLift 1523947
  have htrace : WordTrace (prefixWord ++ tailWord_1523947) baseStart_1523947 baseEnd_1523947 := by
    simpa [prefixWord, tailWord_1523947, baseEnd_1523947] using wordTrace_append hprefix tailTrace_1523947
  have hstable : (prefixWord ++ tailWord_1523947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523947).length < 2 ^ (prefixWord ++ tailWord_1523947).sum := by decide
  have hdescent : baseEnd_1523947 < baseStart_1523947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523954 : List Nat := [3, 2, 1, 3, 2, 1, 1, 2, 2, 6]
def baseStart_1523954 : Nat := 118140960795 + 1523954 * 2 ^ 59
def prefixEnd_1523954 : Nat := 4983230072969 + 3 ^ 40 * 1523954 * 2
def baseEnd_1523954 : Nat := 260840299114011918888823

theorem tailTrace_1523954 : CollatzResearch.WordTrace tailWord_1523954 prefixEnd_1523954 260840299114011918888823 := by
  unfold tailWord_1523954
  simp only [CollatzResearch.WordTrace]
  refine ⟨13895792180245600866776729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37055445813988268978071277 13895792180245600866776729)
  ·
    refine ⟨10421844135184200650082547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13895792180245600866776729 10421844135184200650082547)
    ·
      refine ⟨15632766202776300975123821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10421844135184200650082547 15632766202776300975123821)
      ·
        refine ⟨5862287326041112865671433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15632766202776300975123821 5862287326041112865671433)
        ·
          refine ⟨4396715494530834649253575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5862287326041112865671433 4396715494530834649253575)
          ·
            refine ⟨6595073241796251973880363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4396715494530834649253575 6595073241796251973880363)
            ·
              refine ⟨9892609862694377960820545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6595073241796251973880363 9892609862694377960820545)
              ·
                refine ⟨7419457397020783470615409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9892609862694377960820545 7419457397020783470615409)
                ·
                  refine ⟨5564593047765587602961557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7419457397020783470615409 5564593047765587602961557)
                  ·
                    refine ⟨260840299114011918888823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5564593047765587602961557 260840299114011918888823)
                    ·
                      rfl

theorem cell23_1523954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_1523954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523954 prefixEnd_1523954 := by exact prefixLift 1523954
  have htrace : WordTrace (prefixWord ++ tailWord_1523954) baseStart_1523954 baseEnd_1523954 := by
    simpa [prefixWord, tailWord_1523954, baseEnd_1523954] using wordTrace_append hprefix tailTrace_1523954
  have hstable : (prefixWord ++ tailWord_1523954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523954).length < 2 ^ (prefixWord ++ tailWord_1523954).sum := by decide
  have hdescent : baseEnd_1523954 < baseStart_1523954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523978 : List Nat := [3, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2]
def baseStart_1523978 : Nat := 118140960795 + 1523978 * 2 ^ 59
def prefixEnd_1523978 : Nat := 4983230072969 + 3 ^ 40 * 1523978 * 2
def baseEnd_1523978 : Nat := 782533220877743662766359

theorem tailTrace_1523978 : CollatzResearch.WordTrace tailWord_1523978 prefixEnd_1523978 782533220877743662766359 := by
  unfold tailWord_1523978
  simp only [CollatzResearch.WordTrace]
  refine ⟨13896011018223863891495147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37056029381930303710653725 13896011018223863891495147)
  ·
    refine ⟨20844016527335795837242721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13896011018223863891495147 20844016527335795837242721)
    ·
      refine ⟨15633012395501846877932041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20844016527335795837242721 15633012395501846877932041)
      ·
        refine ⟨11724759296626385158449031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15633012395501846877932041 11724759296626385158449031)
        ·
          refine ⟨17587138944939577737673547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11724759296626385158449031 17587138944939577737673547)
          ·
            refine ⟨26380708417409366606510321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17587138944939577737673547 26380708417409366606510321)
            ·
              refine ⟨19785531313057024954882741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26380708417409366606510321 19785531313057024954882741)
              ·
                refine ⟨1854893560599096089520257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19785531313057024954882741 1854893560599096089520257)
                ·
                  refine ⟨1391170170449322067140193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1854893560599096089520257 1391170170449322067140193)
                  ·
                    refine ⟨1043377627836991550355145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1391170170449322067140193 1043377627836991550355145)
                    ·
                      refine ⟨782533220877743662766359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1043377627836991550355145 782533220877743662766359)
                      ·
                        rfl

theorem cell23_1523978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_1523978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523978 prefixEnd_1523978 := by exact prefixLift 1523978
  have htrace : WordTrace (prefixWord ++ tailWord_1523978) baseStart_1523978 baseEnd_1523978 := by
    simpa [prefixWord, tailWord_1523978, baseEnd_1523978] using wordTrace_append hprefix tailTrace_1523978
  have hstable : (prefixWord ++ tailWord_1523978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523978).length < 2 ^ (prefixWord ++ tailWord_1523978).sum := by decide
  have hdescent : baseEnd_1523978 < baseStart_1523978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523998 : List Nat := [4, 3, 2, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_1523998 : Nat := 118140960795 + 1523998 * 2 ^ 59
def prefixEnd_1523998 : Nat := 4983230072969 + 3 ^ 40 * 1523998 * 2
def baseEnd_1523998 : Nat := 782543490490833584516267

theorem tailTrace_1523998 : CollatzResearch.WordTrace tailWord_1523998 prefixEnd_1523998 782543490490833584516267 := by
  unfold tailWord_1523998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6948096691602874872713581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37056515688548665987805765 6948096691602874872713581)
  ·
    refine ⟨2605536259351078077267593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6948096691602874872713581 2605536259351078077267593)
    ·
      refine ⟨1954152194513308557950695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2605536259351078077267593 1954152194513308557950695)
      ·
        refine ⟨2931228291769962836926043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1954152194513308557950695 2931228291769962836926043)
        ·
          refine ⟨4396842437654944255389065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2931228291769962836926043 4396842437654944255389065)
          ·
            refine ⟨3297631828241208191541799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4396842437654944255389065 3297631828241208191541799)
            ·
              refine ⟨4946447742361812287312699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3297631828241208191541799 4946447742361812287312699)
              ·
                refine ⟨7419671613542718430969049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4946447742361812287312699 7419671613542718430969049)
                ·
                  refine ⟨5564753710157038823226787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7419671613542718430969049 5564753710157038823226787)
                  ·
                    refine ⟨8347130565235558234840181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5564753710157038823226787 8347130565235558234840181)
                    ·
                      refine ⟨782543490490833584516267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8347130565235558234840181 782543490490833584516267)
                      ·
                        rfl

theorem cell23_1523998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_1523998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1523998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1523998 prefixEnd_1523998 := by exact prefixLift 1523998
  have htrace : WordTrace (prefixWord ++ tailWord_1523998) baseStart_1523998 baseEnd_1523998 := by
    simpa [prefixWord, tailWord_1523998, baseEnd_1523998] using wordTrace_append hprefix tailTrace_1523998
  have hstable : (prefixWord ++ tailWord_1523998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523998).length < 2 ^ (prefixWord ++ tailWord_1523998).sum := by decide
  have hdescent : baseEnd_1523998 < baseStart_1523998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524001 : List Nat := [1, 2, 3, 2, 1, 1, 5, 3, 5]
def baseStart_1524001 : Nat := 118140960795 + 1524001 * 2 ^ 59
def prefixEnd_1524001 : Nat := 4983230072969 + 3 ^ 40 * 1524001 * 2
def baseEnd_1524001 : Nat := 86949447881421896975417

theorem tailTrace_1524001 : CollatzResearch.WordTrace tailWord_1524001 prefixEnd_1524001 86949447881421896975417 := by
  unfold tailWord_1524001
  simp only [CollatzResearch.WordTrace]
  refine ⟨55584882951812130494067857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37056588634541420329378571 55584882951812130494067857)
  ·
    refine ⟨41688662213859097870550893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55584882951812130494067857 41688662213859097870550893)
    ·
      refine ⟨15633248330197161701456585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41688662213859097870550893 15633248330197161701456585)
      ·
        refine ⟨11724936247647871276092439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15633248330197161701456585 11724936247647871276092439)
        ·
          refine ⟨17587404371471806914138659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11724936247647871276092439 17587404371471806914138659)
          ·
            refine ⟨26381106557207710371207989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17587404371471806914138659 26381106557207710371207989)
            ·
              refine ⟨2473228739738222847300749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26381106557207710371207989 2473228739738222847300749)
              ·
                refine ⟨927460777401833567737781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2473228739738222847300749 927460777401833567737781)
                ·
                  refine ⟨86949447881421896975417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 927460777401833567737781 86949447881421896975417)
                  ·
                    rfl

theorem cell23_1524001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3, 5].length) (baseStart_1524001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524001 prefixEnd_1524001 := by exact prefixLift 1524001
  have htrace : WordTrace (prefixWord ++ tailWord_1524001) baseStart_1524001 baseEnd_1524001 := by
    simpa [prefixWord, tailWord_1524001, baseEnd_1524001] using wordTrace_append hprefix tailTrace_1524001
  have hstable : (prefixWord ++ tailWord_1524001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524001).length < 2 ^ (prefixWord ++ tailWord_1524001).sum := by decide
  have hdescent : baseEnd_1524001 < baseStart_1524001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524018 : List Nat := [3, 2, 1, 1, 6, 1, 1, 1, 7]
def baseStart_1524018 : Nat := 118140960795 + 1524018 * 2 ^ 59
def prefixEnd_1524018 : Nat := 4983230072969 + 3 ^ 40 * 1524018 * 2
def baseEnd_1524018 : Nat := 86950417789324834029575

theorem tailTrace_1524018 : CollatzResearch.WordTrace tailWord_1524018 prefixEnd_1524018 86950417789324834029575 := by
  unfold tailWord_1524018
  simp only [CollatzResearch.WordTrace]
  refine ⟨13896375748187635599359177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37057001995167028264957805 13896375748187635599359177)
  ·
    refine ⟨10422281811140726699519383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13896375748187635599359177 10422281811140726699519383)
    ·
      refine ⟨15633422716711090049279075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10422281811140726699519383 15633422716711090049279075)
      ·
        refine ⟨23450134075066635073918613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15633422716711090049279075 23450134075066635073918613)
        ·
          refine ⟨1099225034768748519089935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23450134075066635073918613 1099225034768748519089935)
          ·
            refine ⟨1648837552153122778634903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1099225034768748519089935 1648837552153122778634903)
            ·
              refine ⟨2473256328229684167952355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1648837552153122778634903 2473256328229684167952355)
              ·
                refine ⟨3709884492344526251928533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2473256328229684167952355 3709884492344526251928533)
                ·
                  refine ⟨86950417789324834029575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3709884492344526251928533 86950417789324834029575)
                  ·
                    rfl

theorem cell23_1524018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 7].length) (baseStart_1524018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524018 prefixEnd_1524018 := by exact prefixLift 1524018
  have htrace : WordTrace (prefixWord ++ tailWord_1524018) baseStart_1524018 baseEnd_1524018 := by
    simpa [prefixWord, tailWord_1524018, baseEnd_1524018] using wordTrace_append hprefix tailTrace_1524018
  have hstable : (prefixWord ++ tailWord_1524018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524018).length < 2 ^ (prefixWord ++ tailWord_1524018).sum := by decide
  have hdescent : baseEnd_1524018 < baseStart_1524018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524021 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 2, 5, 2]
def baseStart_1524021 : Nat := 118140960795 + 1524021 * 2 ^ 59
def prefixEnd_1524021 : Nat := 4983230072969 + 3 ^ 40 * 1524021 * 2
def baseEnd_1524021 : Nat := 782555300545886994528661

theorem tailTrace_1524021 : CollatzResearch.WordTrace tailWord_1524021 prefixEnd_1524021 782555300545886994528661 := by
  unfold tailWord_1524021
  simp only [CollatzResearch.WordTrace]
  refine ⟨55585612411739673909795917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37057074941159782606530611 55585612411739673909795917)
  ·
    refine ⟨20844604654402377716173469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55585612411739673909795917 20844604654402377716173469)
    ·
      refine ⟨7816726745400891643565051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20844604654402377716173469 7816726745400891643565051)
      ·
        refine ⟨11725090118101337465347577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7816726745400891643565051 11725090118101337465347577)
        ·
          refine ⟨8793817588576003099010683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11725090118101337465347577 8793817588576003099010683)
          ·
            refine ⟨13190726382864004648516025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8793817588576003099010683 13190726382864004648516025)
            ·
              refine ⟨9893044787148003486387019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13190726382864004648516025 9893044787148003486387019)
              ·
                refine ⟨14839567180722005229580529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9893044787148003486387019 14839567180722005229580529)
                ·
                  refine ⟨11129675385541503922185397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14839567180722005229580529 11129675385541503922185397)
                  ·
                    refine ⟨1043407067394515992704881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11129675385541503922185397 1043407067394515992704881)
                    ·
                      refine ⟨782555300545886994528661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1043407067394515992704881 782555300545886994528661)
                      ·
                        rfl

theorem cell23_1524021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_1524021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524021 prefixEnd_1524021 := by exact prefixLift 1524021
  have htrace : WordTrace (prefixWord ++ tailWord_1524021) baseStart_1524021 baseEnd_1524021 := by
    simpa [prefixWord, tailWord_1524021, baseEnd_1524021] using wordTrace_append hprefix tailTrace_1524021
  have hstable : (prefixWord ++ tailWord_1524021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524021).length < 2 ^ (prefixWord ++ tailWord_1524021).sum := by decide
  have hdescent : baseEnd_1524021 < baseStart_1524021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524121 : List Nat := [1, 2, 1, 2, 1, 4, 3, 3, 1, 5]
def baseStart_1524121 : Nat := 118140960795 + 1524121 * 2 ^ 59
def prefixEnd_1524121 : Nat := 4983230072969 + 3 ^ 40 * 1524121 * 2
def baseEnd_1524121 : Nat := 260868882870445534426067

theorem tailTrace_1524121 : CollatzResearch.WordTrace tailWord_1524121 prefixEnd_1524121 260868882870445534426067 := by
  unfold tailWord_1524121
  simp only [CollatzResearch.WordTrace]
  refine ⟨55589259711377390988436217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37059506474251593992290811 55589259711377390988436217)
  ·
    refine ⟨41691944783533043241327163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55589259711377390988436217 41691944783533043241327163)
    ·
      refine ⟨62537917175299564861990745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41691944783533043241327163 62537917175299564861990745)
      ·
        refine ⟨46903437881474673646493059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62537917175299564861990745 46903437881474673646493059)
        ·
          refine ⟨70355156822212010469739589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46903437881474673646493059 70355156822212010469739589)
          ·
            refine ⟨13191591904164751963076173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70355156822212010469739589 13191591904164751963076173)
            ·
              refine ⟨4946846964061781986153565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13191591904164751963076173 4946846964061781986153565)
              ·
                refine ⟨1855067611523168244807587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4946846964061781986153565 1855067611523168244807587)
                ·
                  refine ⟨2782601417284752367211381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1855067611523168244807587 2782601417284752367211381)
                  ·
                    refine ⟨260868882870445534426067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2782601417284752367211381 260868882870445534426067)
                    ·
                      rfl

theorem cell23_1524121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 5].length) (baseStart_1524121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524121 prefixEnd_1524121 := by exact prefixLift 1524121
  have htrace : WordTrace (prefixWord ++ tailWord_1524121) baseStart_1524121 baseEnd_1524121 := by
    simpa [prefixWord, tailWord_1524121, baseEnd_1524121] using wordTrace_append hprefix tailTrace_1524121
  have hstable : (prefixWord ++ tailWord_1524121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524121).length < 2 ^ (prefixWord ++ tailWord_1524121).sum := by decide
  have hdescent : baseEnd_1524121 < baseStart_1524121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524125 : List Nat := [1, 4, 2, 1, 5, 1, 1, 2, 6]
def baseStart_1524125 : Nat := 118140960795 + 1524125 * 2 ^ 59
def prefixEnd_1524125 : Nat := 4983230072969 + 3 ^ 40 * 1524125 * 2
def baseEnd_1524125 : Nat := 86956522503772731958687

theorem tailTrace_1524125 : CollatzResearch.WordTrace tailWord_1524125 prefixEnd_1524125 86956522503772731958687 := by
  unfold tailWord_1524125
  simp only [CollatzResearch.WordTrace]
  refine ⟨55589405603362899671581829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37059603735575266447721219 55589405603362899671581829)
  ·
    refine ⟨10423013550630543688421593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55589405603362899671581829 10423013550630543688421593)
    ·
      refine ⟨7817260162972907766316195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10423013550630543688421593 7817260162972907766316195)
      ·
        refine ⟨11725890244459361649474293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7817260162972907766316195 11725890244459361649474293)
        ·
          refine ⟨1099302210418065154638215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11725890244459361649474293 1099302210418065154638215)
          ·
            refine ⟨1648953315627097731957323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1099302210418065154638215 1648953315627097731957323)
            ·
              refine ⟨2473429973440646597935985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1648953315627097731957323 2473429973440646597935985)
              ·
                refine ⟨1855072480080484948451989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2473429973440646597935985 1855072480080484948451989)
                ·
                  refine ⟨86956522503772731958687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1855072480080484948451989 86956522503772731958687)
                  ·
                    rfl

theorem cell23_1524125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 6].length) (baseStart_1524125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524125 prefixEnd_1524125 := by exact prefixLift 1524125
  have htrace : WordTrace (prefixWord ++ tailWord_1524125) baseStart_1524125 baseEnd_1524125 := by
    simpa [prefixWord, tailWord_1524125, baseEnd_1524125] using wordTrace_append hprefix tailTrace_1524125
  have hstable : (prefixWord ++ tailWord_1524125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524125).length < 2 ^ (prefixWord ++ tailWord_1524125).sum := by decide
  have hdescent : baseEnd_1524125 < baseStart_1524125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524135 : List Nat := [1, 1, 6, 1, 1, 3, 2, 1, 3, 1, 3]
def baseStart_1524135 : Nat := 118140960795 + 1524135 * 2 ^ 59
def prefixEnd_1524135 : Nat := 4983230072969 + 3 ^ 40 * 1524135 * 2
def baseEnd_1524135 : Nat := 782613837340499548503137

theorem tailTrace_1524135 : CollatzResearch.WordTrace tailWord_1524135 prefixEnd_1524135 782613837340499548503137 := by
  unfold tailWord_1524135
  simp only [CollatzResearch.WordTrace]
  refine ⟨55589770333326671379445859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37059846888884447586297239 55589770333326671379445859)
  ·
    refine ⟨83384655499990007069168789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55589770333326671379445859 83384655499990007069168789)
    ·
      refine ⟨3908655726562031581367287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83384655499990007069168789 3908655726562031581367287)
      ·
        refine ⟨5862983589843047372050931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3908655726562031581367287 5862983589843047372050931)
        ·
          refine ⟨8794475384764571058076397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5862983589843047372050931 8794475384764571058076397)
          ·
            refine ⟨3297928269286714146778649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8794475384764571058076397 3297928269286714146778649)
            ·
              refine ⟨2473446201965035610083987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3297928269286714146778649 2473446201965035610083987)
              ·
                refine ⟨3710169302947553415125981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2473446201965035610083987 3710169302947553415125981)
                ·
                  refine ⟨1391313488605332530672243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3710169302947553415125981 1391313488605332530672243)
                  ·
                    refine ⟨2086970232907998796008365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1391313488605332530672243 2086970232907998796008365)
                    ·
                      refine ⟨782613837340499548503137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2086970232907998796008365 782613837340499548503137)
                      ·
                        rfl

theorem cell23_1524135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_1524135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524135 prefixEnd_1524135 := by exact prefixLift 1524135
  have htrace : WordTrace (prefixWord ++ tailWord_1524135) baseStart_1524135 baseEnd_1524135 := by
    simpa [prefixWord, tailWord_1524135, baseEnd_1524135] using wordTrace_append hprefix tailTrace_1524135
  have hstable : (prefixWord ++ tailWord_1524135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524135).length < 2 ^ (prefixWord ++ tailWord_1524135).sum := by decide
  have hdescent : baseEnd_1524135 < baseStart_1524135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524151 : List Nat := [1, 1, 3, 1, 3, 3, 3, 1, 1, 6]
def baseStart_1524151 : Nat := 118140960795 + 1524151 * 2 ^ 59
def prefixEnd_1524151 : Nat := 4983230072969 + 3 ^ 40 * 1524151 * 2
def baseEnd_1524151 : Nat := 260874017676990495301021

theorem tailTrace_1524151 : CollatzResearch.WordTrace tailWord_1524151 prefixEnd_1524151 260874017676990495301021 := by
  unfold tailWord_1524151
  simp only [CollatzResearch.WordTrace]
  refine ⟨55590353901268706112028307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37060235934179137408018871 55590353901268706112028307)
  ·
    refine ⟨83385530851903059168042461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55590353901268706112028307 83385530851903059168042461)
    ·
      refine ⟨31269574069463647188015923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83385530851903059168042461 31269574069463647188015923)
      ·
        refine ⟨46904361104195470782023885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31269574069463647188015923 46904361104195470782023885)
        ·
          refine ⟨17589135414073301543258957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46904361104195470782023885 17589135414073301543258957)
          ·
            refine ⟨6595925780277488078722109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17589135414073301543258957 6595925780277488078722109)
            ·
              refine ⟨2473472167604058029520791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6595925780277488078722109 2473472167604058029520791)
              ·
                refine ⟨3710208251406087044281187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2473472167604058029520791 3710208251406087044281187)
                ·
                  refine ⟨5565312377109130566421781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3710208251406087044281187 5565312377109130566421781)
                  ·
                    refine ⟨260874017676990495301021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5565312377109130566421781 260874017676990495301021)
                    ·
                      rfl

theorem cell23_1524151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 6].length) (baseStart_1524151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524151 prefixEnd_1524151 := by exact prefixLift 1524151
  have htrace : WordTrace (prefixWord ++ tailWord_1524151) baseStart_1524151 baseEnd_1524151 := by
    simpa [prefixWord, tailWord_1524151, baseEnd_1524151] using wordTrace_append hprefix tailTrace_1524151
  have hstable : (prefixWord ++ tailWord_1524151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524151).length < 2 ^ (prefixWord ++ tailWord_1524151).sum := by decide
  have hdescent : baseEnd_1524151 < baseStart_1524151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524158 : List Nat := [4, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4]
def baseStart_1524158 : Nat := 118140960795 + 1524158 * 2 ^ 59
def prefixEnd_1524158 : Nat := 4983230072969 + 3 ^ 40 * 1524158 * 2
def baseEnd_1524158 : Nat := 782625647395552958515531

theorem tailTrace_1524158 : CollatzResearch.WordTrace tailWord_1524158 prefixEnd_1524158 782625647395552958515531 := by
  unfold tailWord_1524158
  simp only [CollatzResearch.WordTrace]
  refine ⟨6948826151530418288441641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37060406141495564205022085 6948826151530418288441641)
  ·
    refine ⟨5211619613647813716331231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6948826151530418288441641 5211619613647813716331231)
    ·
      refine ⟨7817429420471720574496847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5211619613647813716331231 7817429420471720574496847)
      ·
        refine ⟨11726144130707580861745271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7817429420471720574496847 11726144130707580861745271)
        ·
          refine ⟨17589216196061371292617907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11726144130707580861745271 17589216196061371292617907)
          ·
            refine ⟨26383824294092056938926861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17589216196061371292617907 26383824294092056938926861)
            ·
              refine ⟨9893934110284521352097573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26383824294092056938926861 9893934110284521352097573)
              ·
                refine ⟨1855112645678347753518295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9893934110284521352097573 1855112645678347753518295)
                ·
                  refine ⟨2782668968517521630277443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1855112645678347753518295 2782668968517521630277443)
                  ·
                    refine ⟨4174003452776282445416165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2782668968517521630277443 4174003452776282445416165)
                    ·
                      refine ⟨782625647395552958515531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4174003452776282445416165 782625647395552958515531)
                      ·
                        rfl

theorem cell23_1524158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_1524158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524158 prefixEnd_1524158 := by exact prefixLift 1524158
  have htrace : WordTrace (prefixWord ++ tailWord_1524158) baseStart_1524158 baseEnd_1524158 := by
    simpa [prefixWord, tailWord_1524158, baseEnd_1524158] using wordTrace_append hprefix tailTrace_1524158
  have hstable : (prefixWord ++ tailWord_1524158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524158).length < 2 ^ (prefixWord ++ tailWord_1524158).sum := by decide
  have hdescent : baseEnd_1524158 < baseStart_1524158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524181 : List Nat := [1, 3, 2, 3, 1, 4, 9]
def baseStart_1524181 : Nat := 118140960795 + 1524181 * 2 ^ 59
def prefixEnd_1524181 : Nat := 4983230072969 + 3 ^ 40 * 1524181 * 2
def baseEnd_1524181 : Nat := 9662190832723535413925

theorem tailTrace_1524181 : CollatzResearch.WordTrace tailWord_1524181 prefixEnd_1524181 9662190832723535413925 := by
  unfold tailWord_1524181
  simp only [CollatzResearch.WordTrace]
  refine ⟨55591448091160021235620397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37060965394106680823746931 55591448091160021235620397)
  ·
    refine ⟨20846793034185007963357649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55591448091160021235620397 20846793034185007963357649)
    ·
      refine ⟨15635094775638755972518237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20846793034185007963357649 15635094775638755972518237)
      ·
        refine ⟨5863160540864533489694339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15635094775638755972518237 5863160540864533489694339)
        ·
          refine ⟨8794740811296800234541509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5863160540864533489694339 8794740811296800234541509)
          ·
            refine ⟨1649013902118150043976533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8794740811296800234541509 1649013902118150043976533)
            ·
              refine ⟨9662190832723535413925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1649013902118150043976533 9662190832723535413925)
              ·
                rfl

theorem cell23_1524181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 9].length) (baseStart_1524181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524181 prefixEnd_1524181 := by exact prefixLift 1524181
  have htrace : WordTrace (prefixWord ++ tailWord_1524181) baseStart_1524181 baseEnd_1524181 := by
    simpa [prefixWord, tailWord_1524181, baseEnd_1524181] using wordTrace_append hprefix tailTrace_1524181
  have hstable : (prefixWord ++ tailWord_1524181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524181).length < 2 ^ (prefixWord ++ tailWord_1524181).sum := by decide
  have hdescent : baseEnd_1524181 < baseStart_1524181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524202 : List Nat := [3, 1, 3, 1, 3, 3, 2, 1, 2, 4]
def baseStart_1524202 : Nat := 118140960795 + 1524202 * 2 ^ 59
def prefixEnd_1524202 : Nat := 4983230072969 + 3 ^ 40 * 1524202 * 2
def baseEnd_1524202 : Nat := 260882746848116928788443

theorem tailTrace_1524202 : CollatzResearch.WordTrace tailWord_1524202 prefixEnd_1524202 260882746848116928788443 := by
  unfold tailWord_1524202
  simp only [CollatzResearch.WordTrace]
  refine ⟨13898053506020985455533715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37061476016055961214756573 13898053506020985455533715)
  ·
    refine ⟨20847080259031478183300573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13898053506020985455533715 20847080259031478183300573)
    ·
      refine ⟨7817655097136804318737715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20847080259031478183300573 7817655097136804318737715)
      ·
        refine ⟨11726482645705206478106573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7817655097136804318737715 11726482645705206478106573)
        ·
          refine ⟨4397430992139452429289965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11726482645705206478106573 4397430992139452429289965)
          ·
            refine ⟨1649036622052294660983737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4397430992139452429289965 1649036622052294660983737)
            ·
              refine ⟨1236777466539220995737803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1649036622052294660983737 1236777466539220995737803)
              ·
                refine ⟨1855166199808831493606705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1236777466539220995737803 1855166199808831493606705)
                ·
                  refine ⟨1391374649856623620205029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1855166199808831493606705 1391374649856623620205029)
                  ·
                    refine ⟨260882746848116928788443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1391374649856623620205029 260882746848116928788443)
                    ·
                      rfl

theorem cell23_1524202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_1524202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524202 prefixEnd_1524202 := by exact prefixLift 1524202
  have htrace : WordTrace (prefixWord ++ tailWord_1524202) baseStart_1524202 baseEnd_1524202 := by
    simpa [prefixWord, tailWord_1524202, baseEnd_1524202] using wordTrace_append hprefix tailTrace_1524202
  have hstable : (prefixWord ++ tailWord_1524202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524202).length < 2 ^ (prefixWord ++ tailWord_1524202).sum := by decide
  have hdescent : baseEnd_1524202 < baseStart_1524202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524261 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 1, 4, 4]
def baseStart_1524261 : Nat := 118140960795 + 1524261 * 2 ^ 59
def prefixEnd_1524261 : Nat := 4983230072969 + 3 ^ 40 * 1524261 * 2
def baseEnd_1524261 : Nat := 782678535902966055527557

theorem tailTrace_1524261 : CollatzResearch.WordTrace tailWord_1524261 prefixEnd_1524261 782678535902966055527557 := by
  unfold tailWord_1524261
  simp only [CollatzResearch.WordTrace]
  refine ⟨55594365930870194898532637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37062910620580129932355091 55594365930870194898532637)
  ·
    refine ⟨20847887224076323086949739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55594365930870194898532637 20847887224076323086949739)
    ·
      refine ⟨31271830836114484630424609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20847887224076323086949739 31271830836114484630424609)
      ·
        refine ⟨23453873127085863472818457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31271830836114484630424609 23453873127085863472818457)
        ·
          refine ⟨17590404845314397604613843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23453873127085863472818457 17590404845314397604613843)
          ·
            refine ⟨26385607267971596406920765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17590404845314397604613843 26385607267971596406920765)
            ·
              refine ⟨9894602725489348652595287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26385607267971596406920765 9894602725489348652595287)
              ·
                refine ⟨14841904088234022978892931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9894602725489348652595287 14841904088234022978892931)
                ·
                  refine ⟨22262856132351034468339397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14841904088234022978892931 22262856132351034468339397)
                  ·
                    refine ⟨4174285524815818962813637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22262856132351034468339397 4174285524815818962813637)
                    ·
                      refine ⟨782678535902966055527557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4174285524815818962813637 782678535902966055527557)
                      ·
                        rfl

theorem cell23_1524261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_1524261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524261 prefixEnd_1524261 := by exact prefixLift 1524261
  have htrace : WordTrace (prefixWord ++ tailWord_1524261) baseStart_1524261 baseEnd_1524261 := by
    simpa [prefixWord, tailWord_1524261, baseEnd_1524261] using wordTrace_append hprefix tailTrace_1524261
  have hstable : (prefixWord ++ tailWord_1524261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524261).length < 2 ^ (prefixWord ++ tailWord_1524261).sum := by decide
  have hdescent : baseEnd_1524261 < baseStart_1524261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524288 : List Nat := [2, 1, 1, 2, 2, 2, 3, 5, 5]
def baseStart_1524288 : Nat := 118140960795 + 1524288 * 2 ^ 59
def prefixEnd_1524288 : Nat := 4983230072969 + 3 ^ 40 * 1524288 * 2
def baseEnd_1524288 : Nat := 86965822208959716654437

theorem tailTrace_1524288 : CollatzResearch.WordTrace tailWord_1524288 prefixEnd_1524288 86965822208959716654437 := by
  unfold tailWord_1524288
  simp only [CollatzResearch.WordTrace]
  refine ⟨27797675350886189254882759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37063567134514919006510345 27797675350886189254882759)
  ·
    refine ⟨41696513026329283882324139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27797675350886189254882759 41696513026329283882324139)
    ·
      refine ⟨62544769539493925823486209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41696513026329283882324139 62544769539493925823486209)
      ·
        refine ⟨46908577154620444367614657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62544769539493925823486209 46908577154620444367614657)
        ·
          refine ⟨35181432865965333275710993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46908577154620444367614657 35181432865965333275710993)
          ·
            refine ⟨26386074649473999956783245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35181432865965333275710993 26386074649473999956783245)
            ·
              refine ⟨9894777993552749983793717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26386074649473999956783245 9894777993552749983793717)
              ·
                refine ⟨927635436895570310980661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9894777993552749983793717 927635436895570310980661)
                ·
                  refine ⟨86965822208959716654437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 927635436895570310980661 86965822208959716654437)
                  ·
                    rfl

theorem cell23_1524288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5, 5].length) (baseStart_1524288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524288 prefixEnd_1524288 := by exact prefixLift 1524288
  have htrace : WordTrace (prefixWord ++ tailWord_1524288) baseStart_1524288 baseEnd_1524288 := by
    simpa [prefixWord, tailWord_1524288, baseEnd_1524288] using wordTrace_append hprefix tailTrace_1524288
  have hstable : (prefixWord ++ tailWord_1524288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524288).length < 2 ^ (prefixWord ++ tailWord_1524288).sum := by decide
  have hdescent : baseEnd_1524288 < baseStart_1524288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524298 : List Nat := [3, 1, 2, 1, 1, 4, 1, 2, 2, 3, 3]
def baseStart_1524298 : Nat := 118140960795 + 1524298 * 2 ^ 59
def prefixEnd_1524298 : Nat := 4983230072969 + 3 ^ 40 * 1524298 * 2
def baseEnd_1524298 : Nat := 782697534687182410764887

theorem tailTrace_1524298 : CollatzResearch.WordTrace tailWord_1524298 prefixEnd_1524298 782697534687182410764887 := by
  unfold tailWord_1524298
  simp only [CollatzResearch.WordTrace]
  refine ⟨13898928857934037554407387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37063810287824100145086365 13898928857934037554407387)
  ·
    refine ⟨20848393286901056331611081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13898928857934037554407387 20848393286901056331611081)
    ·
      refine ⟨15636294965175792248708311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20848393286901056331611081 15636294965175792248708311)
      ·
        refine ⟨23454442447763688373062467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15636294965175792248708311 23454442447763688373062467)
        ·
          refine ⟨35181663671645532559593701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23454442447763688373062467 35181663671645532559593701)
          ·
            refine ⟨6596561938433537354923819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35181663671645532559593701 6596561938433537354923819)
            ·
              refine ⟨9894842907650306032385729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6596561938433537354923819 9894842907650306032385729)
              ·
                refine ⟨7421132180737729524289297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9894842907650306032385729 7421132180737729524289297)
                ·
                  refine ⟨5565849135553297143216973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7421132180737729524289297 5565849135553297143216973)
                  ·
                    refine ⟨2087193425832486428706365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5565849135553297143216973 2087193425832486428706365)
                    ·
                      refine ⟨782697534687182410764887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2087193425832486428706365 782697534687182410764887)
                      ·
                        rfl

theorem cell23_1524298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_1524298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524298 prefixEnd_1524298 := by exact prefixLift 1524298
  have htrace : WordTrace (prefixWord ++ tailWord_1524298) baseStart_1524298 baseEnd_1524298 := by
    simpa [prefixWord, tailWord_1524298, baseEnd_1524298] using wordTrace_append hprefix tailTrace_1524298
  have hstable : (prefixWord ++ tailWord_1524298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524298).length < 2 ^ (prefixWord ++ tailWord_1524298).sum := by decide
  have hdescent : baseEnd_1524298 < baseStart_1524298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524311 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 7]
def baseStart_1524311 : Nat := 118140960795 + 1524311 * 2 ^ 59
def prefixEnd_1524311 : Nat := 4983230072969 + 3 ^ 40 * 1524311 * 2
def baseEnd_1524311 : Nat := 782704209935690859902327

theorem tailTrace_1524311 : CollatzResearch.WordTrace tailWord_1524311 prefixEnd_1524311 782704209935690859902327 := by
  unfold tailWord_1524311
  simp only [CollatzResearch.WordTrace]
  refine ⟨55596189580689053437852787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37064126387126035625235191 55596189580689053437852787)
  ·
    refine ⟨83394284371033580156779181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55596189580689053437852787 83394284371033580156779181)
    ·
      refine ⟨31272856639137592558792193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83394284371033580156779181 31272856639137592558792193)
      ·
        refine ⟨23454642479353194419094145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31272856639137592558792193 23454642479353194419094145)
        ·
          refine ⟨17590981859514895814320609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23454642479353194419094145 17590981859514895814320609)
          ·
            refine ⟨13193236394636171860740457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17590981859514895814320609 13193236394636171860740457)
            ·
              refine ⟨9894927295977128895555343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13193236394636171860740457 9894927295977128895555343)
              ·
                refine ⟨14842390943965693343333015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9894927295977128895555343 14842390943965693343333015)
                ·
                  refine ⟨22263586415948540014999523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14842390943965693343333015 22263586415948540014999523)
                  ·
                    refine ⟨33395379623922810022499285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22263586415948540014999523 33395379623922810022499285)
                    ·
                      refine ⟨782704209935690859902327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 33395379623922810022499285 782704209935690859902327)
                      ·
                        rfl

theorem cell23_1524311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_1524311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524311 prefixEnd_1524311 := by exact prefixLift 1524311
  have htrace : WordTrace (prefixWord ++ tailWord_1524311) baseStart_1524311 baseEnd_1524311 := by
    simpa [prefixWord, tailWord_1524311, baseEnd_1524311] using wordTrace_append hprefix tailTrace_1524311
  have hstable : (prefixWord ++ tailWord_1524311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524311).length < 2 ^ (prefixWord ++ tailWord_1524311).sum := by decide
  have hdescent : baseEnd_1524311 < baseStart_1524311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524316 : List Nat := [2, 2, 4, 1, 3, 1, 3, 1, 2, 2, 2]
def baseStart_1524316 : Nat := 118140960795 + 1524316 * 2 ^ 59
def prefixEnd_1524316 : Nat := 4983230072969 + 3 ^ 40 * 1524316 * 2
def baseEnd_1524316 : Nat := 782706777338963340339805

theorem tailTrace_1524316 : CollatzResearch.WordTrace tailWord_1524316 prefixEnd_1524316 782706777338963340339805 := by
  unfold tailWord_1524316
  simp only [CollatzResearch.WordTrace]
  refine ⟨27798185972835469645892401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37064247963780626194523201 27798185972835469645892401)
  ·
    refine ⟨20848639479626602234419301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27798185972835469645892401 20848639479626602234419301)
    ·
      refine ⟨3909119902429987918953619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20848639479626602234419301 3909119902429987918953619)
      ·
        refine ⟨5863679853644981878430429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3909119902429987918953619 5863679853644981878430429)
        ·
          refine ⟨2198879945116868204411411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5863679853644981878430429 2198879945116868204411411)
          ·
            refine ⟨3298319917675302306617117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2198879945116868204411411 3298319917675302306617117)
            ·
              refine ⟨1236869969128238364981419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3298319917675302306617117 1236869969128238364981419)
              ·
                refine ⟨1855304953692357547472129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1236869969128238364981419 1855304953692357547472129)
                ·
                  refine ⟨1391478715269268160604097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1855304953692357547472129 1391478715269268160604097)
                  ·
                    refine ⟨1043609036451951120453073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1391478715269268160604097 1043609036451951120453073)
                    ·
                      refine ⟨782706777338963340339805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1043609036451951120453073 782706777338963340339805)
                      ·
                        rfl

theorem cell23_1524316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_1524316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524316 prefixEnd_1524316 := by exact prefixLift 1524316
  have htrace : WordTrace (prefixWord ++ tailWord_1524316) baseStart_1524316 baseEnd_1524316 := by
    simpa [prefixWord, tailWord_1524316, baseEnd_1524316] using wordTrace_append hprefix tailTrace_1524316
  have hstable : (prefixWord ++ tailWord_1524316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524316).length < 2 ^ (prefixWord ++ tailWord_1524316).sum := by decide
  have hdescent : baseEnd_1524316 < baseStart_1524316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524348 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 5, 4]
def baseStart_1524348 : Nat := 118140960795 + 1524348 * 2 ^ 59
def prefixEnd_1524348 : Nat := 4983230072969 + 3 ^ 40 * 1524348 * 2
def baseEnd_1524348 : Nat := 260907736239969071713219

theorem tailTrace_1524348 : CollatzResearch.WordTrace tailWord_1524348 prefixEnd_1524348 260907736239969071713219 := by
  unfold tailWord_1524348
  simp only [CollatzResearch.WordTrace]
  refine ⟨27798769540777504378474849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37065026054370005837966465 27798769540777504378474849)
  ·
    refine ⟨20849077155583128283856137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27798769540777504378474849 20849077155583128283856137)
    ·
      refine ⟨15636807866687346212892103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20849077155583128283856137 15636807866687346212892103)
      ·
        refine ⟨23455211800031019319338155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15636807866687346212892103 23455211800031019319338155)
        ·
          refine ⟨35182817700046528979007233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23455211800031019319338155 35182817700046528979007233)
          ·
            refine ⟨26387113275034896734255425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35182817700046528979007233 26387113275034896734255425)
            ·
              refine ⟨19790334956276172550691569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26387113275034896734255425 19790334956276172550691569)
              ·
                refine ⟨14842751217207129413018677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19790334956276172550691569 14842751217207129413018677)
                ·
                  refine ⟨1391507926613168382470501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14842751217207129413018677 1391507926613168382470501)
                  ·
                    refine ⟨260907736239969071713219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1391507926613168382470501 260907736239969071713219)
                    ·
                      rfl

theorem cell23_1524348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_1524348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524348 prefixEnd_1524348 := by exact prefixLift 1524348
  have htrace : WordTrace (prefixWord ++ tailWord_1524348) baseStart_1524348 baseEnd_1524348 := by
    simpa [prefixWord, tailWord_1524348, baseEnd_1524348] using wordTrace_append hprefix tailTrace_1524348
  have hstable : (prefixWord ++ tailWord_1524348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524348).length < 2 ^ (prefixWord ++ tailWord_1524348).sum := by decide
  have hdescent : baseEnd_1524348 < baseStart_1524348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524351 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 6]
def baseStart_1524351 : Nat := 118140960795 + 1524351 * 2 ^ 59
def prefixEnd_1524351 : Nat := 4983230072969 + 3 ^ 40 * 1524351 * 2
def baseEnd_1524351 : Nat := 782724749161870703402143

theorem tailTrace_1524351 : CollatzResearch.WordTrace tailWord_1524351 prefixEnd_1524351 782724749161870703402143 := by
  unfold tailWord_1524351
  simp only [CollatzResearch.WordTrace]
  refine ⟨55597648500544140269308907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37065099000362760179539271 55597648500544140269308907)
  ·
    refine ⟨83396472750816210403963361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55597648500544140269308907 83396472750816210403963361)
    ·
      refine ⟨62547354563112157802972521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83396472750816210403963361 62547354563112157802972521)
      ·
        refine ⟨46910515922334118352229391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62547354563112157802972521 46910515922334118352229391)
        ·
          refine ⟨70365773883501177528344087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46910515922334118352229391 70365773883501177528344087)
          ·
            refine ⟨105548660825251766292516131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70365773883501177528344087 105548660825251766292516131)
            ·
              refine ⟨158322991237877649438774197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105548660825251766292516131 158322991237877649438774197)
              ·
                refine ⟨14842780428551029634885081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 158322991237877649438774197 14842780428551029634885081)
                ·
                  refine ⟨11132085321413272226163811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14842780428551029634885081 11132085321413272226163811)
                  ·
                    refine ⟨16698127982119908339245717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11132085321413272226163811 16698127982119908339245717)
                    ·
                      refine ⟨782724749161870703402143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16698127982119908339245717 782724749161870703402143)
                      ·
                        rfl

theorem cell23_1524351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_1524351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524351 prefixEnd_1524351 := by exact prefixLift 1524351
  have htrace : WordTrace (prefixWord ++ tailWord_1524351) baseStart_1524351 baseEnd_1524351 := by
    simpa [prefixWord, tailWord_1524351, baseEnd_1524351] using wordTrace_append hprefix tailTrace_1524351
  have hstable : (prefixWord ++ tailWord_1524351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524351).length < 2 ^ (prefixWord ++ tailWord_1524351).sum := by decide
  have hdescent : baseEnd_1524351 < baseStart_1524351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524449 : List Nat := [1, 2, 3, 1, 4, 3, 1, 1, 2, 3, 2]
def baseStart_1524449 : Nat := 118140960795 + 1524449 * 2 ^ 59
def prefixEnd_1524449 : Nat := 4983230072969 + 3 ^ 40 * 1524449 * 2
def baseEnd_1524449 : Nat := 782775070266011319976693

theorem tailTrace_1524449 : CollatzResearch.WordTrace tailWord_1524449 prefixEnd_1524449 782775070266011319976693 := by
  unfold tailWord_1524449
  simp only [CollatzResearch.WordTrace]
  refine ⟨55601222854189103006376401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37067481902792735337584267 55601222854189103006376401)
  ·
    refine ⟨41700917140641827254782301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55601222854189103006376401 41700917140641827254782301)
    ·
      refine ⟨15637843927740685220543363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41700917140641827254782301 15637843927740685220543363)
      ·
        refine ⟨23456765891611027830815045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15637843927740685220543363 23456765891611027830815045)
        ·
          refine ⟨4398143604677067718277821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23456765891611027830815045 4398143604677067718277821)
          ·
            refine ⟨1649303851753900394354183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4398143604677067718277821 1649303851753900394354183)
            ·
              refine ⟨2473955777630850591531275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1649303851753900394354183 2473955777630850591531275)
              ·
                refine ⟨3710933666446275887296913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2473955777630850591531275 3710933666446275887296913)
                ·
                  refine ⟨2783200249834706915472685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3710933666446275887296913 2783200249834706915472685)
                  ·
                    refine ⟨1043700093688015093302257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2783200249834706915472685 1043700093688015093302257)
                    ·
                      refine ⟨782775070266011319976693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1043700093688015093302257 782775070266011319976693)
                      ·
                        rfl

theorem cell23_1524449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 3, 2].length) (baseStart_1524449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524449 prefixEnd_1524449 := by exact prefixLift 1524449
  have htrace : WordTrace (prefixWord ++ tailWord_1524449) baseStart_1524449 baseEnd_1524449 := by
    simpa [prefixWord, tailWord_1524449, baseEnd_1524449] using wordTrace_append hprefix tailTrace_1524449
  have hstable : (prefixWord ++ tailWord_1524449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524449).length < 2 ^ (prefixWord ++ tailWord_1524449).sum := by decide
  have hdescent : baseEnd_1524449 < baseStart_1524449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524456 : List Nat := [2, 1, 4, 1, 4, 1, 2, 3, 1, 1, 3]
def baseStart_1524456 : Nat := 118140960795 + 1524456 * 2 ^ 59
def prefixEnd_1524456 : Nat := 4983230072969 + 3 ^ 40 * 1524456 * 2
def baseEnd_1524456 : Nat := 782778664630592792589161

theorem tailTrace_1524456 : CollatzResearch.WordTrace tailWord_1524456 prefixEnd_1524456 782778664630592792589161 := by
  unfold tailWord_1524456
  simp only [CollatzResearch.WordTrace]
  refine ⟨27800739082581871600940611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37067652110109162134587481 27800739082581871600940611)
  ·
    refine ⟨41701108623872807401410917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27800739082581871600940611 41701108623872807401410917)
    ·
      refine ⟨7818957866976151387764547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41701108623872807401410917 7818957866976151387764547)
      ·
        refine ⟨11728436800464227081646821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7818957866976151387764547 11728436800464227081646821)
        ·
          refine ⟨2199081900087042577808779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11728436800464227081646821 2199081900087042577808779)
          ·
            refine ⟨3298622850130563866713169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2199081900087042577808779 3298622850130563866713169)
            ·
              refine ⟨2473967137597922900034877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3298622850130563866713169 2473967137597922900034877)
              ·
                refine ⟨927737676599221087513079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2473967137597922900034877 927737676599221087513079)
                ·
                  refine ⟨1391606514898831631269619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 927737676599221087513079 1391606514898831631269619)
                  ·
                    refine ⟨2087409772348247446904429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1391606514898831631269619 2087409772348247446904429)
                    ·
                      refine ⟨782778664630592792589161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2087409772348247446904429 782778664630592792589161)
                      ·
                        rfl

theorem cell23_1524456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_1524456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524456 prefixEnd_1524456 := by exact prefixLift 1524456
  have htrace : WordTrace (prefixWord ++ tailWord_1524456) baseStart_1524456 baseEnd_1524456 := by
    simpa [prefixWord, tailWord_1524456, baseEnd_1524456] using wordTrace_append hprefix tailTrace_1524456
  have hstable : (prefixWord ++ tailWord_1524456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524456).length < 2 ^ (prefixWord ++ tailWord_1524456).sum := by decide
  have hdescent : baseEnd_1524456 < baseStart_1524456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524458 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_1524458 : Nat := 118140960795 + 1524458 * 2 ^ 59
def prefixEnd_1524458 : Nat := 4983230072969 + 3 ^ 40 * 1524458 * 2
def baseEnd_1524458 : Nat := 782779691591901784764151

theorem tailTrace_1524458 : CollatzResearch.WordTrace tailWord_1524458 prefixEnd_1524458 782779691591901784764151 := by
  unfold tailWord_1524458
  simp only [CollatzResearch.WordTrace]
  refine ⟨13900387777789124385863507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37067700740770998362302685 13900387777789124385863507)
  ·
    refine ⟨20850581666683686578795261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13900387777789124385863507 20850581666683686578795261)
    ·
      refine ⟨7818968125006382467048223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20850581666683686578795261 7818968125006382467048223)
      ·
        refine ⟨11728452187509573700572335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7818968125006382467048223 11728452187509573700572335)
        ·
          refine ⟨17592678281264360550858503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11728452187509573700572335 17592678281264360550858503)
          ·
            refine ⟨26389017421896540826287755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17592678281264360550858503 26389017421896540826287755)
            ·
              refine ⟨39583526132844811239431633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26389017421896540826287755 39583526132844811239431633)
              ·
                refine ⟨29687644599633608429573725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39583526132844811239431633 29687644599633608429573725)
                ·
                  refine ⟨11132866724862603161090147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29687644599633608429573725 11132866724862603161090147)
                  ·
                    refine ⟨16699300087293904741635221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11132866724862603161090147 16699300087293904741635221)
                    ·
                      refine ⟨782779691591901784764151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16699300087293904741635221 782779691591901784764151)
                      ·
                        rfl

theorem cell23_1524458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_1524458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524458 prefixEnd_1524458 := by exact prefixLift 1524458
  have htrace : WordTrace (prefixWord ++ tailWord_1524458) baseStart_1524458 baseEnd_1524458 := by
    simpa [prefixWord, tailWord_1524458, baseEnd_1524458] using wordTrace_append hprefix tailTrace_1524458
  have hstable : (prefixWord ++ tailWord_1524458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524458).length < 2 ^ (prefixWord ++ tailWord_1524458).sum := by decide
  have hdescent : baseEnd_1524458 < baseStart_1524458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524462 : List Nat := [4, 1, 2, 1, 1, 4, 1, 3, 1, 1, 4]
def baseStart_1524462 : Nat := 118140960795 + 1524462 * 2 ^ 59
def prefixEnd_1524462 : Nat := 4983230072969 + 3 ^ 40 * 1524462 * 2
def baseEnd_1524462 : Nat := 782781745514519769114133

theorem tailTrace_1524462 : CollatzResearch.WordTrace tailWord_1524462 prefixEnd_1524462 782781745514519769114133 := by
  unfold tailWord_1524462
  simp only [CollatzResearch.WordTrace]
  refine ⟨6950212125392750778324955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37067798002094670817733093 6950212125392750778324955)
  ·
    refine ⟨10425318188089126167487433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6950212125392750778324955 10425318188089126167487433)
    ·
      refine ⟨7818988641066844625615575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10425318188089126167487433 7818988641066844625615575)
      ·
        refine ⟨11728482961600266938423363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7818988641066844625615575 11728482961600266938423363)
        ·
          refine ⟨17592724442400400407635045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11728482961600266938423363 17592724442400400407635045)
          ·
            refine ⟨3298635832950075076431571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17592724442400400407635045 3298635832950075076431571)
            ·
              refine ⟨4947953749425112614647357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3298635832950075076431571 4947953749425112614647357)
              ·
                refine ⟨1855482656034417230492759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4947953749425112614647357 1855482656034417230492759)
                ·
                  refine ⟨2783223984051625845739139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1855482656034417230492759 2783223984051625845739139)
                  ·
                    refine ⟨4174835976077438768608709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2783223984051625845739139 4174835976077438768608709)
                    ·
                      refine ⟨782781745514519769114133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4174835976077438768608709 782781745514519769114133)
                      ·
                        rfl

theorem cell23_1524462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_1524462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524462 prefixEnd_1524462 := by exact prefixLift 1524462
  have htrace : WordTrace (prefixWord ++ tailWord_1524462) baseStart_1524462 baseEnd_1524462 := by
    simpa [prefixWord, tailWord_1524462, baseEnd_1524462] using wordTrace_append hprefix tailTrace_1524462
  have hstable : (prefixWord ++ tailWord_1524462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524462).length < 2 ^ (prefixWord ++ tailWord_1524462).sum := by decide
  have hdescent : baseEnd_1524462 < baseStart_1524462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524482 : List Nat := [3, 4, 1, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_1524482 : Nat := 118140960795 + 1524482 * 2 ^ 59
def prefixEnd_1524482 : Nat := 4983230072969 + 3 ^ 40 * 1524482 * 2
def baseEnd_1524482 : Nat := 782792015127609690864041

theorem tailTrace_1524482 : CollatzResearch.WordTrace tailWord_1524482 prefixEnd_1524482 782792015127609690864041 := by
  unfold tailWord_1524482
  simp only [CollatzResearch.WordTrace]
  refine ⟨13900606615767387410581925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37068284308713033094885133 13900606615767387410581925)
  ·
    refine ⟨2606363740456385139484111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13900606615767387410581925 2606363740456385139484111)
    ·
      refine ⟨3909545610684577709226167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2606363740456385139484111 3909545610684577709226167)
      ·
        refine ⟨5864318416026866563839251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3909545610684577709226167 5864318416026866563839251)
        ·
          refine ⟨8796477624040299845758877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5864318416026866563839251 8796477624040299845758877)
          ·
            refine ⟨3298679109015112442159579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8796477624040299845758877 3298679109015112442159579)
            ·
              refine ⟨4948018663522668663239369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3298679109015112442159579 4948018663522668663239369)
              ·
                refine ⟨3711013997642001497429527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4948018663522668663239369 3711013997642001497429527)
                ·
                  refine ⟨5566520996463002246144291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3711013997642001497429527 5566520996463002246144291)
                  ·
                    refine ⟨8349781494694503369216437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5566520996463002246144291 8349781494694503369216437)
                    ·
                      refine ⟨782792015127609690864041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8349781494694503369216437 782792015127609690864041)
                      ·
                        rfl

theorem cell23_1524482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_1524482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524482 prefixEnd_1524482 := by exact prefixLift 1524482
  have htrace : WordTrace (prefixWord ++ tailWord_1524482) baseStart_1524482 baseEnd_1524482 := by
    simpa [prefixWord, tailWord_1524482, baseEnd_1524482] using wordTrace_append hprefix tailTrace_1524482
  have hstable : (prefixWord ++ tailWord_1524482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524482).length < 2 ^ (prefixWord ++ tailWord_1524482).sum := by decide
  have hdescent : baseEnd_1524482 < baseStart_1524482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524512 : List Nat := [2, 1, 1, 5, 1, 2, 1, 2, 4, 1, 3]
def baseStart_1524512 : Nat := 118140960795 + 1524512 * 2 ^ 59
def prefixEnd_1524512 : Nat := 4983230072969 + 3 ^ 40 * 1524512 * 2
def baseEnd_1524512 : Nat := 782807419547244573488903

theorem tailTrace_1524512 : CollatzResearch.WordTrace tailWord_1524512 prefixEnd_1524512 782807419547244573488903 := by
  unfold tailWord_1524512
  simp only [CollatzResearch.WordTrace]
  refine ⟨27801760326480432382959895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37069013768640576510613193 27801760326480432382959895)
  ·
    refine ⟨41702640489720648574439843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27801760326480432382959895 41702640489720648574439843)
    ·
      refine ⟨62553960734580972861659765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41702640489720648574439843 62553960734580972861659765)
      ·
        refine ⟨5864433818866966205780603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62553960734580972861659765 5864433818866966205780603)
        ·
          refine ⟨8796650728300449308670905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5864433818866966205780603 8796650728300449308670905)
          ·
            refine ⟨6597488046225336981503179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8796650728300449308670905 6597488046225336981503179)
            ·
              refine ⟨9896232069338005472254769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6597488046225336981503179 9896232069338005472254769)
              ·
                refine ⟨7422174052003504104191077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9896232069338005472254769 7422174052003504104191077)
                ·
                  refine ⟨1391657634750657019535827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7422174052003504104191077 1391657634750657019535827)
                  ·
                    refine ⟨2087486452125985529303741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1391657634750657019535827 2087486452125985529303741)
                    ·
                      refine ⟨782807419547244573488903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2087486452125985529303741 782807419547244573488903)
                      ·
                        rfl

theorem cell23_1524512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_1524512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524512 prefixEnd_1524512 := by exact prefixLift 1524512
  have htrace : WordTrace (prefixWord ++ tailWord_1524512) baseStart_1524512 baseEnd_1524512 := by
    simpa [prefixWord, tailWord_1524512, baseEnd_1524512] using wordTrace_append hprefix tailTrace_1524512
  have hstable : (prefixWord ++ tailWord_1524512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524512).length < 2 ^ (prefixWord ++ tailWord_1524512).sum := by decide
  have hdescent : baseEnd_1524512 < baseStart_1524512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524528 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 4, 6]
def baseStart_1524528 : Nat := 118140960795 + 1524528 * 2 ^ 59
def prefixEnd_1524528 : Nat := 4983230072969 + 3 ^ 40 * 1524528 * 2
def baseEnd_1524528 : Nat := 260938545079238836962943

theorem tailTrace_1524528 : CollatzResearch.WordTrace tailWord_1524528 prefixEnd_1524528 260938545079238836962943 := by
  unfold tailWord_1524528
  simp only [CollatzResearch.WordTrace]
  refine ⟨27802052110451449749251119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37069402813935266332334825 27802052110451449749251119)
  ·
    refine ⟨41703078165677174623876679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27802052110451449749251119 41703078165677174623876679)
    ·
      refine ⟨62554617248515761935815019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41703078165677174623876679 62554617248515761935815019)
      ·
        refine ⟨93831925872773642903722529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62554617248515761935815019 93831925872773642903722529)
        ·
          refine ⟨70373944404580232177791897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93831925872773642903722529 70373944404580232177791897)
          ·
            refine ⟨52780458303435174133343923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70373944404580232177791897 52780458303435174133343923)
            ·
              refine ⟨79170687455152761200015885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52780458303435174133343923 79170687455152761200015885)
              ·
                refine ⟨29689007795682285450005957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79170687455152761200015885 29689007795682285450005957)
                ·
                  refine ⟨5566688961690428521876117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29689007795682285450005957 5566688961690428521876117)
                  ·
                    refine ⟨260938545079238836962943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5566688961690428521876117 260938545079238836962943)
                    ·
                      rfl

theorem cell23_1524528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 4, 6].length) (baseStart_1524528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524528 prefixEnd_1524528 := by exact prefixLift 1524528
  have htrace : WordTrace (prefixWord ++ tailWord_1524528) baseStart_1524528 baseEnd_1524528 := by
    simpa [prefixWord, tailWord_1524528, baseEnd_1524528] using wordTrace_append hprefix tailTrace_1524528
  have hstable : (prefixWord ++ tailWord_1524528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524528).length < 2 ^ (prefixWord ++ tailWord_1524528).sum := by decide
  have hdescent : baseEnd_1524528 < baseStart_1524528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524550 : List Nat := [6, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3]
def baseStart_1524550 : Nat := 118140960795 + 1524550 * 2 ^ 59
def prefixEnd_1524550 : Nat := 4983230072969 + 3 ^ 40 * 1524550 * 2
def baseEnd_1524550 : Nat := 782826931812115424813729

theorem tailTrace_1524550 : CollatzResearch.WordTrace tailWord_1524550 prefixEnd_1524550 782826931812115424813729 := by
  unfold tailWord_1524550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1737653332088224914243847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37069937751215464837202069 1737653332088224914243847)
  ·
    refine ⟨2606479998132337371365771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1737653332088224914243847 2606479998132337371365771)
    ·
      refine ⟨3909719997198506057048657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2606479998132337371365771 3909719997198506057048657)
      ·
        refine ⟨2932289997898879542786493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3909719997198506057048657 2932289997898879542786493)
        ·
          refine ⟨1099608749212079828544935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2932289997898879542786493 1099608749212079828544935)
          ·
            refine ⟨1649413123818119742817403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1099608749212079828544935 1649413123818119742817403)
            ·
              refine ⟨2474119685727179614226105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1649413123818119742817403 2474119685727179614226105)
              ·
                refine ⟨1855589764295384710669579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2474119685727179614226105 1855589764295384710669579)
                ·
                  refine ⟨2783384646443077066004369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1855589764295384710669579 2783384646443077066004369)
                  ·
                    refine ⟨2087538484832307799503277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2783384646443077066004369 2087538484832307799503277)
                    ·
                      refine ⟨782826931812115424813729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2087538484832307799503277 782826931812115424813729)
                      ·
                        rfl

theorem cell23_1524550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_1524550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524550 prefixEnd_1524550 := by exact prefixLift 1524550
  have htrace : WordTrace (prefixWord ++ tailWord_1524550) baseStart_1524550 baseEnd_1524550 := by
    simpa [prefixWord, tailWord_1524550, baseEnd_1524550] using wordTrace_append hprefix tailTrace_1524550
  have hstable : (prefixWord ++ tailWord_1524550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524550).length < 2 ^ (prefixWord ++ tailWord_1524550).sum := by decide
  have hdescent : baseEnd_1524550 < baseStart_1524550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524552 : List Nat := [2, 1, 3, 1, 1, 3, 2, 3, 1, 4, 2]
def baseStart_1524552 : Nat := 118140960795 + 1524552 * 2 ^ 59
def prefixEnd_1524552 : Nat := 4983230072969 + 3 ^ 40 * 1524552 * 2
def baseEnd_1524552 : Nat := 782827958773424416988719

theorem tailTrace_1524552 : CollatzResearch.WordTrace tailWord_1524552 prefixEnd_1524552 782827958773424416988719 := by
  unfold tailWord_1524552
  simp only [CollatzResearch.WordTrace]
  refine ⟨27802489786407975798687955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37069986381877301064917273 27802489786407975798687955)
  ·
    refine ⟨41703734679611963698031933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27802489786407975798687955 41703734679611963698031933)
    ·
      refine ⟨15638900504854486386761975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41703734679611963698031933 15638900504854486386761975)
      ·
        refine ⟨23458350757281729580142963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15638900504854486386761975 23458350757281729580142963)
        ·
          refine ⟨35187526135922594370214445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23458350757281729580142963 35187526135922594370214445)
          ·
            refine ⟨13195322300970972888830417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35187526135922594370214445 13195322300970972888830417)
            ·
              refine ⟨9896491725728229666622813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13195322300970972888830417 9896491725728229666622813)
              ·
                refine ⟨3711184397148086124983555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9896491725728229666622813 3711184397148086124983555)
                ·
                  refine ⟨5566776595722129187475333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3711184397148086124983555 5566776595722129187475333)
                  ·
                    refine ⟨1043770611697899222651625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5566776595722129187475333 1043770611697899222651625)
                    ·
                      refine ⟨782827958773424416988719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1043770611697899222651625 782827958773424416988719)
                      ·
                        rfl

theorem cell23_1524552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 1, 4, 2].length) (baseStart_1524552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524552 prefixEnd_1524552 := by exact prefixLift 1524552
  have htrace : WordTrace (prefixWord ++ tailWord_1524552) baseStart_1524552 baseEnd_1524552 := by
    simpa [prefixWord, tailWord_1524552, baseEnd_1524552] using wordTrace_append hprefix tailTrace_1524552
  have hstable : (prefixWord ++ tailWord_1524552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524552).length < 2 ^ (prefixWord ++ tailWord_1524552).sum := by decide
  have hdescent : baseEnd_1524552 < baseStart_1524552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524556 : List Nat := [2, 2, 1, 3, 3, 3, 1, 2, 1, 3, 2]
def baseStart_1524556 : Nat := 118140960795 + 1524556 * 2 ^ 59
def prefixEnd_1524556 : Nat := 4983230072969 + 3 ^ 40 * 1524556 * 2
def baseEnd_1524556 : Nat := 782830012696042401338701

theorem tailTrace_1524556 : CollatzResearch.WordTrace tailWord_1524556 prefixEnd_1524556 782830012696042401338701 := by
  unfold tailWord_1524556
  simp only [CollatzResearch.WordTrace]
  refine ⟨27802562732400730140260761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37070083643200973520347681 27802562732400730140260761)
  ·
    refine ⟨20851922049300547605195571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27802562732400730140260761 20851922049300547605195571)
    ·
      refine ⟨31277883073950821407793357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20851922049300547605195571 31277883073950821407793357)
      ·
        refine ⟨11729206152731558027922509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31277883073950821407793357 11729206152731558027922509)
        ·
          refine ⟨4398452307274334260470941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11729206152731558027922509 4398452307274334260470941)
          ·
            refine ⟨1649419615227875347676603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4398452307274334260470941 1649419615227875347676603)
            ·
              refine ⟨2474129422841813021514905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1649419615227875347676603 2474129422841813021514905)
              ·
                refine ⟨1855597067131359766136179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2474129422841813021514905 1855597067131359766136179)
                ·
                  refine ⟨2783395600697039649204269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1855597067131359766136179 2783395600697039649204269)
                  ·
                    refine ⟨1043773350261389868451601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2783395600697039649204269 1043773350261389868451601)
                    ·
                      refine ⟨782830012696042401338701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1043773350261389868451601 782830012696042401338701)
                      ·
                        rfl

theorem cell23_1524556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_1524556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524556 prefixEnd_1524556 := by exact prefixLift 1524556
  have htrace : WordTrace (prefixWord ++ tailWord_1524556) baseStart_1524556 baseEnd_1524556 := by
    simpa [prefixWord, tailWord_1524556, baseEnd_1524556] using wordTrace_append hprefix tailTrace_1524556
  have hstable : (prefixWord ++ tailWord_1524556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524556).length < 2 ^ (prefixWord ++ tailWord_1524556).sum := by decide
  have hdescent : baseEnd_1524556 < baseStart_1524556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524572 : List Nat := [2, 2, 4, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_1524572 : Nat := 118140960795 + 1524572 * 2 ^ 59
def prefixEnd_1524572 : Nat := 4983230072969 + 3 ^ 40 * 1524572 * 2
def baseEnd_1524572 : Nat := 782838228386514338738627

theorem tailTrace_1524572 : CollatzResearch.WordTrace tailWord_1524572 prefixEnd_1524572 782838228386514338738627 := by
  unfold tailWord_1524572
  simp only [CollatzResearch.WordTrace]
  refine ⟨27802854516371747506551985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37070472688495663342069313 27802854516371747506551985)
  ·
    refine ⟨20852140887278810629913989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27802854516371747506551985 20852140887278810629913989)
    ·
      refine ⟨3909776416364776993108873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20852140887278810629913989 3909776416364776993108873)
      ·
        refine ⟨2932332312273582744831655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3909776416364776993108873 2932332312273582744831655)
        ·
          refine ⟨4398498468410374117247483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2932332312273582744831655 4398498468410374117247483)
          ·
            refine ⟨6597747702615561175871225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4398498468410374117247483 6597747702615561175871225)
            ·
              refine ⟨4948310776961670881903419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6597747702615561175871225 4948310776961670881903419)
              ·
                refine ⟨7422466165442506322855129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4948310776961670881903419 7422466165442506322855129)
                ·
                  refine ⟨5566849624081879742141347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7422466165442506322855129 5566849624081879742141347)
                  ·
                    refine ⟨8350274436122819613212021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5566849624081879742141347 8350274436122819613212021)
                    ·
                      refine ⟨782838228386514338738627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8350274436122819613212021 782838228386514338738627)
                      ·
                        rfl

theorem cell23_1524572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_1524572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524572 prefixEnd_1524572 := by exact prefixLift 1524572
  have htrace : WordTrace (prefixWord ++ tailWord_1524572) baseStart_1524572 baseEnd_1524572 := by
    simpa [prefixWord, tailWord_1524572, baseEnd_1524572] using wordTrace_append hprefix tailTrace_1524572
  have hstable : (prefixWord ++ tailWord_1524572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524572).length < 2 ^ (prefixWord ++ tailWord_1524572).sum := by decide
  have hdescent : baseEnd_1524572 < baseStart_1524572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524605 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 4, 5]
def baseStart_1524605 : Nat := 118140960795 + 1524605 * 2 ^ 59
def prefixEnd_1524605 : Nat := 4983230072969 + 3 ^ 40 * 1524605 * 2
def baseEnd_1524605 : Nat := 260951724416037569875325

theorem tailTrace_1524605 : CollatzResearch.WordTrace tailWord_1524605 prefixEnd_1524605 260951724416037569875325 := by
  unfold tailWord_1524605
  simp only [CollatzResearch.WordTrace]
  refine ⟨55606912641623941649055269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37071275094415961099370179 55606912641623941649055269)
  ·
    refine ⟨10426296120304489059197863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55606912641623941649055269 10426296120304489059197863)
    ·
      refine ⟨15639444180456733588796795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10426296120304489059197863 15639444180456733588796795)
      ·
        refine ⟨23459166270685100383195193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15639444180456733588796795 23459166270685100383195193)
        ·
          refine ⟨17594374703013825287396395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23459166270685100383195193 17594374703013825287396395)
          ·
            refine ⟨26391562054520737931094593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17594374703013825287396395 26391562054520737931094593)
            ·
              refine ⟨19793671540890553448320945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26391562054520737931094593 19793671540890553448320945)
              ·
                refine ⟨14845253655667915086240709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19793671540890553448320945 14845253655667915086240709)
                ·
                  refine ⟨2783485060437734078670133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14845253655667915086240709 2783485060437734078670133)
                  ·
                    refine ⟨260951724416037569875325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2783485060437734078670133 260951724416037569875325)
                    ·
                      rfl

theorem cell23_1524605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_1524605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524605 prefixEnd_1524605 := by exact prefixLift 1524605
  have htrace : WordTrace (prefixWord ++ tailWord_1524605) baseStart_1524605 baseEnd_1524605 := by
    simpa [prefixWord, tailWord_1524605, baseEnd_1524605] using wordTrace_append hprefix tailTrace_1524605
  have hstable : (prefixWord ++ tailWord_1524605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524605).length < 2 ^ (prefixWord ++ tailWord_1524605).sum := by decide
  have hdescent : baseEnd_1524605 < baseStart_1524605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524612 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 4, 5, 2]
def baseStart_1524612 : Nat := 118140960795 + 1524612 * 2 ^ 59
def prefixEnd_1524612 : Nat := 4983230072969 + 3 ^ 40 * 1524612 * 2
def baseEnd_1524612 : Nat := 782858767612694182238443

theorem tailTrace_1524612 : CollatzResearch.WordTrace tailWord_1524612 prefixEnd_1524612 782858767612694182238443 := by
  unfold tailWord_1524612
  simp only [CollatzResearch.WordTrace]
  refine ⟨27803583976299290922280045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37071445301732387896373393 27803583976299290922280045)
  ·
    refine ⟨10426343991112234095855017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27803583976299290922280045 10426343991112234095855017)
    ·
      refine ⟨7819757993334175571891263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10426343991112234095855017 7819757993334175571891263)
      ·
        refine ⟨11729636990001263357836895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7819757993334175571891263 11729636990001263357836895)
        ·
          refine ⟨17594455485001895036755343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11729636990001263357836895 17594455485001895036755343)
          ·
            refine ⟨26391683227502842555133015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17594455485001895036755343 26391683227502842555133015)
            ·
              refine ⟨39587524841254263832699523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26391683227502842555133015 39587524841254263832699523)
              ·
                refine ⟨59381287261881395749049285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39587524841254263832699523 59381287261881395749049285)
                ·
                  refine ⟨11133991361602761702946741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59381287261881395749049285 11133991361602761702946741)
                  ·
                    refine ⟨1043811690150258909651257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11133991361602761702946741 1043811690150258909651257)
                    ·
                      refine ⟨782858767612694182238443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1043811690150258909651257 782858767612694182238443)
                      ·
                        rfl

theorem cell23_1524612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_1524612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524612 prefixEnd_1524612 := by exact prefixLift 1524612
  have htrace : WordTrace (prefixWord ++ tailWord_1524612) baseStart_1524612 baseEnd_1524612 := by
    simpa [prefixWord, tailWord_1524612, baseEnd_1524612] using wordTrace_append hprefix tailTrace_1524612
  have hstable : (prefixWord ++ tailWord_1524612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524612).length < 2 ^ (prefixWord ++ tailWord_1524612).sum := by decide
  have hdescent : baseEnd_1524612 < baseStart_1524612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524626 : List Nat := [3, 2, 3, 2, 2, 1, 2, 3, 5]
def baseStart_1524626 : Nat := 118140960795 + 1524626 * 2 ^ 59
def prefixEnd_1524626 : Nat := 4983230072969 + 3 ^ 40 * 1524626 * 2
def baseEnd_1524626 : Nat := 86985106260206347495931

theorem tailTrace_1524626 : CollatzResearch.WordTrace tailWord_1524626 prefixEnd_1524626 86985106260206347495931 := by
  unfold tailWord_1524626
  simp only [CollatzResearch.WordTrace]
  refine ⟨13901919643636965558892433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37071785716365241490379821 13901919643636965558892433)
  ·
    refine ⟨10426439732727724169169325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13901919643636965558892433 10426439732727724169169325)
    ·
      refine ⟨3909914899772896563438497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10426439732727724169169325 3909914899772896563438497)
      ·
        refine ⟨2932436174829672422578873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3909914899772896563438497 2932436174829672422578873)
        ·
          refine ⟨2199327131122254316934155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2932436174829672422578873 2199327131122254316934155)
          ·
            refine ⟨3298990696683381475401233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2199327131122254316934155 3298990696683381475401233)
            ·
              refine ⟨2474243022512536106550925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3298990696683381475401233 2474243022512536106550925)
              ·
                refine ⟨927841133442201039956597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2474243022512536106550925 927841133442201039956597)
                ·
                  refine ⟨86985106260206347495931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 927841133442201039956597 86985106260206347495931)
                  ·
                    rfl

theorem cell23_1524626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3, 5].length) (baseStart_1524626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524626 prefixEnd_1524626 := by exact prefixLift 1524626
  have htrace : WordTrace (prefixWord ++ tailWord_1524626) baseStart_1524626 baseEnd_1524626 := by
    simpa [prefixWord, tailWord_1524626, baseEnd_1524626] using wordTrace_append hprefix tailTrace_1524626
  have hstable : (prefixWord ++ tailWord_1524626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524626).length < 2 ^ (prefixWord ++ tailWord_1524626).sum := by decide
  have hdescent : baseEnd_1524626 < baseStart_1524626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524686 : List Nat := [4, 1, 1, 1, 2, 3, 3, 3, 1, 4]
def baseStart_1524686 : Nat := 118140960795 + 1524686 * 2 ^ 59
def prefixEnd_1524686 : Nat := 4983230072969 + 3 ^ 40 * 1524686 * 2
def baseEnd_1524686 : Nat := 260965588393708964237701

theorem tailTrace_1524686 : CollatzResearch.WordTrace tailWord_1524686 prefixEnd_1524686 260965588393708964237701 := by
  unfold tailWord_1524686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6951233369291311560344239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37073244636220328321835941 6951233369291311560344239)
  ·
    refine ⟨10426850053936967340516359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6951233369291311560344239 10426850053936967340516359)
    ·
      refine ⟨15640275080905451010774539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10426850053936967340516359 15640275080905451010774539)
      ·
        refine ⟨23460412621358176516161809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15640275080905451010774539 23460412621358176516161809)
        ·
          refine ⟨17595309466018632387121357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23460412621358176516161809 17595309466018632387121357)
          ·
            refine ⟨6598241049756987145170509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17595309466018632387121357 6598241049756987145170509)
            ·
              refine ⟨2474340393658870179438941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6598241049756987145170509 2474340393658870179438941)
              ·
                refine ⟨927877647622076317289603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2474340393658870179438941 927877647622076317289603)
                ·
                  refine ⟨1391816471433114475934405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 927877647622076317289603 1391816471433114475934405)
                  ·
                    refine ⟨260965588393708964237701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1391816471433114475934405 260965588393708964237701)
                    ·
                      rfl

theorem cell23_1524686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_1524686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524686 prefixEnd_1524686 := by exact prefixLift 1524686
  have htrace : WordTrace (prefixWord ++ tailWord_1524686) baseStart_1524686 baseEnd_1524686 := by
    simpa [prefixWord, tailWord_1524686, baseEnd_1524686] using wordTrace_append hprefix tailTrace_1524686
  have hstable : (prefixWord ++ tailWord_1524686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524686).length < 2 ^ (prefixWord ++ tailWord_1524686).sum := by decide
  have hdescent : baseEnd_1524686 < baseStart_1524686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524703 : List Nat := [1, 1, 2, 3, 5, 1, 3, 2, 1, 4]
def baseStart_1524703 : Nat := 118140960795 + 1524703 * 2 ^ 59
def prefixEnd_1524703 : Nat := 4983230072969 + 3 ^ 40 * 1524703 * 2
def baseEnd_1524703 : Nat := 260968498117417775400175

theorem tailTrace_1524703 : CollatzResearch.WordTrace tailWord_1524703 prefixEnd_1524703 260968498117417775400175 := by
  unfold tailWord_1524703
  simp only [CollatzResearch.WordTrace]
  refine ⟨55610486995268904386122763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37073657996845936257415175 55610486995268904386122763)
  ·
    refine ⟨83415730492903356579184145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55610486995268904386122763 83415730492903356579184145)
    ·
      refine ⟨62561797869677517434388109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83415730492903356579184145 62561797869677517434388109)
      ·
        refine ⟨23460674201129069037895541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62561797869677517434388109 23460674201129069037895541)
        ·
          refine ⟨2199438206355850222302707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23460674201129069037895541 2199438206355850222302707)
          ·
            refine ⟨3299157309533775333454061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2199438206355850222302707 3299157309533775333454061)
            ·
              refine ⟨1237183991075165750045273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3299157309533775333454061 1237183991075165750045273)
              ·
                refine ⟨927887993306374312533955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1237183991075165750045273 927887993306374312533955)
                ·
                  refine ⟨1391831989959561468800933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 927887993306374312533955 1391831989959561468800933)
                  ·
                    refine ⟨260968498117417775400175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1391831989959561468800933 260968498117417775400175)
                    ·
                      rfl

theorem cell23_1524703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2, 1, 4].length) (baseStart_1524703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524703 prefixEnd_1524703 := by exact prefixLift 1524703
  have htrace : WordTrace (prefixWord ++ tailWord_1524703) baseStart_1524703 baseEnd_1524703 := by
    simpa [prefixWord, tailWord_1524703, baseEnd_1524703] using wordTrace_append hprefix tailTrace_1524703
  have hstable : (prefixWord ++ tailWord_1524703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524703).length < 2 ^ (prefixWord ++ tailWord_1524703).sum := by decide
  have hdescent : baseEnd_1524703 < baseStart_1524703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524705 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 2, 1, 7]
def baseStart_1524705 : Nat := 118140960795 + 1524705 * 2 ^ 59
def prefixEnd_1524705 : Nat := 4983230072969 + 3 ^ 40 * 1524705 * 2
def baseEnd_1524705 : Nat := 782906521313562318375515

theorem tailTrace_1524705 : CollatzResearch.WordTrace tailWord_1524705 prefixEnd_1524705 782906521313562318375515 := by
  unfold tailWord_1524705
  simp only [CollatzResearch.WordTrace]
  refine ⟨55610559941261658727695569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37073706627507772485130379 55610559941261658727695569)
  ·
    refine ⟨41707919955946244045771677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55610559941261658727695569 41707919955946244045771677)
    ·
      refine ⟨15640469983479841517164379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41707919955946244045771677 15640469983479841517164379)
      ·
        refine ⟨23460704975219762275746569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15640469983479841517164379 23460704975219762275746569)
        ·
          refine ⟨17595528731414821706809927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23460704975219762275746569 17595528731414821706809927)
          ·
            refine ⟨26393293097122232560214891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17595528731414821706809927 26393293097122232560214891)
            ·
              refine ⟨39589939645683348840322337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26393293097122232560214891 39589939645683348840322337)
              ·
                refine ⟨29692454734262511630241753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39589939645683348840322337 29692454734262511630241753)
                ·
                  refine ⟨22269341050696883722681315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29692454734262511630241753 22269341050696883722681315)
                  ·
                    refine ⟨33404011576045325584021973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22269341050696883722681315 33404011576045325584021973)
                    ·
                      refine ⟨782906521313562318375515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 33404011576045325584021973 782906521313562318375515)
                      ·
                        rfl

theorem cell23_1524705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_1524705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524705 prefixEnd_1524705 := by exact prefixLift 1524705
  have htrace : WordTrace (prefixWord ++ tailWord_1524705) baseStart_1524705 baseEnd_1524705 := by
    simpa [prefixWord, tailWord_1524705, baseEnd_1524705] using wordTrace_append hprefix tailTrace_1524705
  have hstable : (prefixWord ++ tailWord_1524705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524705).length < 2 ^ (prefixWord ++ tailWord_1524705).sum := by decide
  have hdescent : baseEnd_1524705 < baseStart_1524705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524715 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 4]
def baseStart_1524715 : Nat := 118140960795 + 1524715 * 2 ^ 59
def prefixEnd_1524715 : Nat := 4983230072969 + 3 ^ 40 * 1524715 * 2
def baseEnd_1524715 : Nat := 782911656120107279250469

theorem tailTrace_1524715 : CollatzResearch.WordTrace tailWord_1524715 prefixEnd_1524715 782911656120107279250469 := by
  unfold tailWord_1524715
  simp only [CollatzResearch.WordTrace]
  refine ⟨55610924671225430435559599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37073949780816953623706399 55610924671225430435559599)
  ·
    refine ⟨83416387006838145653339399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55610924671225430435559599 83416387006838145653339399)
    ·
      refine ⟨125124580510257218480009099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83416387006838145653339399 125124580510257218480009099)
      ·
        refine ⟨187686870765385827720013649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125124580510257218480009099 187686870765385827720013649)
        ·
          refine ⟨140765153074039370790010237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187686870765385827720013649 140765153074039370790010237)
          ·
            refine ⟨52786932402764764046253839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140765153074039370790010237 52786932402764764046253839)
            ·
              refine ⟨79180398604147146069380759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52786932402764764046253839 79180398604147146069380759)
              ·
                refine ⟨118770597906220719104071139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79180398604147146069380759 118770597906220719104071139)
                ·
                  refine ⟨178155896859331078656106709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118770597906220719104071139 178155896859331078656106709)
                  ·
                    refine ⟨4175528832640572156002501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 178155896859331078656106709 4175528832640572156002501)
                    ·
                      refine ⟨782911656120107279250469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4175528832640572156002501 782911656120107279250469)
                      ·
                        rfl

theorem cell23_1524715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 4].length) (baseStart_1524715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524715 prefixEnd_1524715 := by exact prefixLift 1524715
  have htrace : WordTrace (prefixWord ++ tailWord_1524715) baseStart_1524715 baseEnd_1524715 := by
    simpa [prefixWord, tailWord_1524715, baseEnd_1524715] using wordTrace_append hprefix tailTrace_1524715
  have hstable : (prefixWord ++ tailWord_1524715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524715).length < 2 ^ (prefixWord ++ tailWord_1524715).sum := by decide
  have hdescent : baseEnd_1524715 < baseStart_1524715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524735 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 5]
def baseStart_1524735 : Nat := 118140960795 + 1524735 * 2 ^ 59
def prefixEnd_1524735 : Nat := 4983230072969 + 3 ^ 40 * 1524735 * 2
def baseEnd_1524735 : Nat := 782921925733197201000377

theorem tailTrace_1524735 : CollatzResearch.WordTrace tailWord_1524735 prefixEnd_1524735 782921925733197201000377 := by
  unfold tailWord_1524735
  simp only [CollatzResearch.WordTrace]
  refine ⟨55611654131152973851287659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37074436087435315900858439 55611654131152973851287659)
  ·
    refine ⟨83417481196729460776931489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55611654131152973851287659 83417481196729460776931489)
    ·
      refine ⟨62563110897547095582698617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83417481196729460776931489 62563110897547095582698617)
      ·
        refine ⟨46922333173160321687023963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62563110897547095582698617 46922333173160321687023963)
        ·
          refine ⟨70383499759740482530535945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46922333173160321687023963 70383499759740482530535945)
          ·
            refine ⟨52787624819805361897901959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70383499759740482530535945 52787624819805361897901959)
            ·
              refine ⟨79181437229708042846852939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52787624819805361897901959 79181437229708042846852939)
              ·
                refine ⟨118772155844562064270279409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79181437229708042846852939 118772155844562064270279409)
                ·
                  refine ⟨89079116883421548202709557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118772155844562064270279409 89079116883421548202709557)
                  ·
                    refine ⟨8351167207820770144004021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 89079116883421548202709557 8351167207820770144004021)
                    ·
                      refine ⟨782921925733197201000377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8351167207820770144004021 782921925733197201000377)
                      ·
                        rfl

theorem cell23_1524735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_1524735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524735 prefixEnd_1524735 := by exact prefixLift 1524735
  have htrace : WordTrace (prefixWord ++ tailWord_1524735) baseStart_1524735 baseEnd_1524735 := by
    simpa [prefixWord, tailWord_1524735, baseEnd_1524735] using wordTrace_append hprefix tailTrace_1524735
  have hstable : (prefixWord ++ tailWord_1524735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524735).length < 2 ^ (prefixWord ++ tailWord_1524735).sum := by decide
  have hdescent : baseEnd_1524735 < baseStart_1524735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524746 : List Nat := [3, 1, 2, 2, 3, 2, 3, 1, 1, 5]
def baseStart_1524746 : Nat := 118140960795 + 1524746 * 2 ^ 59
def prefixEnd_1524746 : Nat := 4983230072969 + 3 ^ 40 * 1524746 * 2
def baseEnd_1524746 : Nat := 260975858006798885987609

theorem tailTrace_1524746 : CollatzResearch.WordTrace tailWord_1524746 prefixEnd_1524746 260975858006798885987609 := by
  unfold tailWord_1524746
  simp only [CollatzResearch.WordTrace]
  refine ⟨13903013833528280682484523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37074703556075415153292061 13903013833528280682484523)
  ·
    refine ⟨20854520750292421023726785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13903013833528280682484523 20854520750292421023726785)
    ·
      refine ⟨15640890562719315767795089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20854520750292421023726785 15640890562719315767795089)
      ·
        refine ⟨11730667922039486825846317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15640890562719315767795089 11730667922039486825846317)
        ·
          refine ⟨4399000470764807559692369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11730667922039486825846317 4399000470764807559692369)
          ·
            refine ⟨3299250353073605669769277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4399000470764807559692369 3299250353073605669769277)
            ·
              refine ⟨1237218882402602126163479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3299250353073605669769277 1237218882402602126163479)
              ·
                refine ⟨1855828323603903189245219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1237218882402602126163479 1855828323603903189245219)
                ·
                  refine ⟨2783742485405854783867829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1855828323603903189245219 2783742485405854783867829)
                  ·
                    refine ⟨260975858006798885987609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2783742485405854783867829 260975858006798885987609)
                    ·
                      rfl

theorem cell23_1524746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_1524746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524746 prefixEnd_1524746 := by exact prefixLift 1524746
  have htrace : WordTrace (prefixWord ++ tailWord_1524746) baseStart_1524746 baseEnd_1524746 := by
    simpa [prefixWord, tailWord_1524746, baseEnd_1524746] using wordTrace_append hprefix tailTrace_1524746
  have hstable : (prefixWord ++ tailWord_1524746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524746).length < 2 ^ (prefixWord ++ tailWord_1524746).sum := by decide
  have hdescent : baseEnd_1524746 < baseStart_1524746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524752 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 3]
def baseStart_1524752 : Nat := 118140960795 + 1524752 * 2 ^ 59
def prefixEnd_1524752 : Nat := 4983230072969 + 3 ^ 40 * 1524752 * 2
def baseEnd_1524752 : Nat := 782930654904323634487799

theorem tailTrace_1524752 : CollatzResearch.WordTrace tailWord_1524752 prefixEnd_1524752 782930654904323634487799 := by
  unfold tailWord_1524752
  simp only [CollatzResearch.WordTrace]
  refine ⟨27806137086045692877328255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37074849448060923836437673 27806137086045692877328255)
  ·
    refine ⟨41709205629068539315992383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27806137086045692877328255 41709205629068539315992383)
    ·
      refine ⟨62563808443602808973988575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41709205629068539315992383 62563808443602808973988575)
      ·
        refine ⟨93845712665404213460982863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62563808443602808973988575 93845712665404213460982863)
        ·
          refine ⟨140768568998106320191474295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93845712665404213460982863 140768568998106320191474295)
          ·
            refine ⟨211152853497159480287211443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140768568998106320191474295 211152853497159480287211443)
            ·
              refine ⟨316729280245739220430817165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211152853497159480287211443 316729280245739220430817165)
              ·
                refine ⟨118773480092152207661556437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 316729280245739220430817165 118773480092152207661556437)
                ·
                  refine ⟨2783753439659817367067729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 118773480092152207661556437 2783753439659817367067729)
                  ·
                    refine ⟨2087815079744863025300797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2783753439659817367067729 2087815079744863025300797)
                    ·
                      refine ⟨782930654904323634487799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2087815079744863025300797 782930654904323634487799)
                      ·
                        rfl

theorem cell23_1524752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 3].length) (baseStart_1524752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524752 prefixEnd_1524752 := by exact prefixLift 1524752
  have htrace : WordTrace (prefixWord ++ tailWord_1524752) baseStart_1524752 baseEnd_1524752 := by
    simpa [prefixWord, tailWord_1524752, baseEnd_1524752] using wordTrace_append hprefix tailTrace_1524752
  have hstable : (prefixWord ++ tailWord_1524752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524752).length < 2 ^ (prefixWord ++ tailWord_1524752).sum := by decide
  have hdescent : baseEnd_1524752 < baseStart_1524752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524754 : List Nat := [3, 2, 5, 1, 1, 2, 2, 2, 1, 4]
def baseStart_1524754 : Nat := 118140960795 + 1524754 * 2 ^ 59
def prefixEnd_1524754 : Nat := 4983230072969 + 3 ^ 40 * 1524754 * 2
def baseEnd_1524754 : Nat := 260977227288544208887597

theorem tailTrace_1524754 : CollatzResearch.WordTrace tailWord_1524754 prefixEnd_1524754 260977227288544208887597 := by
  unfold tailWord_1524754
  simp only [CollatzResearch.WordTrace]
  refine ⟨13903086779521035024057329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37074898078722760064152877 13903086779521035024057329)
  ·
    refine ⟨10427315084640776268042997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13903086779521035024057329 10427315084640776268042997)
    ·
      refine ⟨977560789185072775129031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10427315084640776268042997 977560789185072775129031)
      ·
        refine ⟨1466341183777609162693547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 977560789185072775129031 1466341183777609162693547)
        ·
          refine ⟨2199511775666413744040321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1466341183777609162693547 2199511775666413744040321)
          ·
            refine ⟨1649633831749810308030241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2199511775666413744040321 1649633831749810308030241)
            ·
              refine ⟨1237225373812357731022681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1649633831749810308030241 1237225373812357731022681)
              ·
                refine ⟨927919030359268298267011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1237225373812357731022681 927919030359268298267011)
                ·
                  refine ⟨1391878545538902447400517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 927919030359268298267011 1391878545538902447400517)
                  ·
                    refine ⟨260977227288544208887597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1391878545538902447400517 260977227288544208887597)
                    ·
                      rfl

theorem cell23_1524754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_1524754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524754 prefixEnd_1524754 := by exact prefixLift 1524754
  have htrace : WordTrace (prefixWord ++ tailWord_1524754) baseStart_1524754 baseEnd_1524754 := by
    simpa [prefixWord, tailWord_1524754, baseEnd_1524754] using wordTrace_append hprefix tailTrace_1524754
  have hstable : (prefixWord ++ tailWord_1524754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524754).length < 2 ^ (prefixWord ++ tailWord_1524754).sum := by decide
  have hdescent : baseEnd_1524754 < baseStart_1524754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524760 : List Nat := [2, 1, 2, 3, 2, 4, 2, 2, 1, 1, 3]
def baseStart_1524760 : Nat := 118140960795 + 1524760 * 2 ^ 59
def prefixEnd_1524760 : Nat := 4983230072969 + 3 ^ 40 * 1524760 * 2
def baseEnd_1524760 : Nat := 782934762749559603187763

theorem tailTrace_1524760 : CollatzResearch.WordTrace tailWord_1524760 prefixEnd_1524760 782934762749559603187763 := by
  unfold tailWord_1524760
  simp only [CollatzResearch.WordTrace]
  refine ⟨27806282978031201560473867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37075043970708268747298489 27806282978031201560473867)
  ·
    refine ⟨41709424467046802340710801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27806282978031201560473867 41709424467046802340710801)
    ·
      refine ⟨31282068350285101755533101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41709424467046802340710801 31282068350285101755533101)
      ·
        refine ⟨11730775631356913158324913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31282068350285101755533101 11730775631356913158324913)
        ·
          refine ⟨8798081723517684868743685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11730775631356913158324913 8798081723517684868743685)
          ·
            refine ⟨1649640323159565912889441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8798081723517684868743685 1649640323159565912889441)
            ·
              refine ⟨1237230242369674434667081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1649640323159565912889441 1237230242369674434667081)
              ·
                refine ⟨927922681777255826000311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1237230242369674434667081 927922681777255826000311)
                ·
                  refine ⟨1391884022665883739000467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 927922681777255826000311 1391884022665883739000467)
                  ·
                    refine ⟨2087826033998825608500701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1391884022665883739000467 2087826033998825608500701)
                    ·
                      refine ⟨782934762749559603187763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2087826033998825608500701 782934762749559603187763)
                      ·
                        rfl

theorem cell23_1524760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_1524760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524760 prefixEnd_1524760 := by exact prefixLift 1524760
  have htrace : WordTrace (prefixWord ++ tailWord_1524760) baseStart_1524760 baseEnd_1524760 := by
    simpa [prefixWord, tailWord_1524760, baseEnd_1524760] using wordTrace_append hprefix tailTrace_1524760
  have hstable : (prefixWord ++ tailWord_1524760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524760).length < 2 ^ (prefixWord ++ tailWord_1524760).sum := by decide
  have hdescent : baseEnd_1524760 < baseStart_1524760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524762 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4]
def baseStart_1524762 : Nat := 118140960795 + 1524762 * 2 ^ 59
def prefixEnd_1524762 : Nat := 4983230072969 + 3 ^ 40 * 1524762 * 2
def baseEnd_1524762 : Nat := 782935789710868595362753

theorem tailTrace_1524762 : CollatzResearch.WordTrace tailWord_1524762 prefixEnd_1524762 782935789710868595362753 := by
  unfold tailWord_1524762
  simp only [CollatzResearch.WordTrace]
  refine ⟨13903159725513789365630135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37075092601370104975013693 13903159725513789365630135)
  ·
    refine ⟨20854739588270684048445203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13903159725513789365630135 20854739588270684048445203)
    ·
      refine ⟨31282109382406026072667805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20854739588270684048445203 31282109382406026072667805)
      ·
        refine ⟨11730791018402259777250427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31282109382406026072667805 11730791018402259777250427)
        ·
          refine ⟨17596186527603389665875641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11730791018402259777250427 17596186527603389665875641)
          ·
            refine ⟨13197139895702542249406731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17596186527603389665875641 13197139895702542249406731)
            ·
              refine ⟨19795709843553813374110097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13197139895702542249406731 19795709843553813374110097)
              ·
                refine ⟨14846782382665360030582573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19795709843553813374110097 14846782382665360030582573)
                ·
                  refine ⟨5567543393499510011468465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14846782382665360030582573 5567543393499510011468465)
                  ·
                    refine ⟨4175657545124632508601349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5567543393499510011468465 4175657545124632508601349)
                    ·
                      refine ⟨782935789710868595362753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4175657545124632508601349 782935789710868595362753)
                      ·
                        rfl

theorem cell23_1524762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_1524762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524762 prefixEnd_1524762 := by exact prefixLift 1524762
  have htrace : WordTrace (prefixWord ++ tailWord_1524762) baseStart_1524762 baseEnd_1524762 := by
    simpa [prefixWord, tailWord_1524762, baseEnd_1524762] using wordTrace_append hprefix tailTrace_1524762
  have hstable : (prefixWord ++ tailWord_1524762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524762).length < 2 ^ (prefixWord ++ tailWord_1524762).sum := by decide
  have hdescent : baseEnd_1524762 < baseStart_1524762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524769 : List Nat := [1, 2, 3, 2, 3, 1, 1, 2, 3, 2, 3]
def baseStart_1524769 : Nat := 118140960795 + 1524769 * 2 ^ 59
def prefixEnd_1524769 : Nat := 4983230072969 + 3 ^ 40 * 1524769 * 2
def baseEnd_1524769 : Nat := 782939384075450067975221

theorem tailTrace_1524769 : CollatzResearch.WordTrace tailWord_1524769 prefixEnd_1524769 782939384075450067975221 := by
  unfold tailWord_1524769
  simp only [CollatzResearch.WordTrace]
  refine ⟨55612894213029797658025361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37075262808686531772016907 55612894213029797658025361)
  ·
    refine ⟨41709670659772348243519021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55612894213029797658025361 41709670659772348243519021)
    ·
      refine ⟨15641126497414630591319633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41709670659772348243519021 15641126497414630591319633)
      ·
        refine ⟨11730844873060972943489725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15641126497414630591319633 11730844873060972943489725)
        ·
          refine ⟨4399066827397864853808647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11730844873060972943489725 4399066827397864853808647)
          ·
            refine ⟨6598600241096797280712971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4399066827397864853808647 6598600241096797280712971)
            ·
              refine ⟨9897900361645195921069457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6598600241096797280712971 9897900361645195921069457)
              ·
                refine ⟨7423425271233896940802093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9897900361645195921069457 7423425271233896940802093)
                ·
                  refine ⟨2783784476712711352800785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7423425271233896940802093 2783784476712711352800785)
                  ·
                    refine ⟨2087838357534533514600589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2783784476712711352800785 2087838357534533514600589)
                    ·
                      refine ⟨782939384075450067975221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2087838357534533514600589 782939384075450067975221)
                      ·
                        rfl

theorem cell23_1524769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_1524769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524769 prefixEnd_1524769 := by exact prefixLift 1524769
  have htrace : WordTrace (prefixWord ++ tailWord_1524769) baseStart_1524769 baseEnd_1524769 := by
    simpa [prefixWord, tailWord_1524769, baseEnd_1524769] using wordTrace_append hprefix tailTrace_1524769
  have hstable : (prefixWord ++ tailWord_1524769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524769).length < 2 ^ (prefixWord ++ tailWord_1524769).sum := by decide
  have hdescent : baseEnd_1524769 < baseStart_1524769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524799 : List Nat := [1, 1, 2, 2, 3, 1, 1, 4, 4, 1, 3]
def baseStart_1524799 : Nat := 118140960795 + 1524799 * 2 ^ 59
def prefixEnd_1524799 : Nat := 4983230072969 + 3 ^ 40 * 1524799 * 2
def baseEnd_1524799 : Nat := 782954788495084950600083

theorem tailTrace_1524799 : CollatzResearch.WordTrace tailWord_1524799 prefixEnd_1524799 782954788495084950600083 := by
  unfold tailWord_1524799
  simp only [CollatzResearch.WordTrace]
  refine ⟨55613988402921112781617451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37075992268614075187744967 55613988402921112781617451)
  ·
    refine ⟨83420982604381669172426177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55613988402921112781617451 83420982604381669172426177)
    ·
      refine ⟨62565736953286251879319633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83420982604381669172426177 62565736953286251879319633)
      ·
        refine ⟨46924302714964688909489725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62565736953286251879319633 46924302714964688909489725)
        ·
          refine ⟨17596613518111758341058647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46924302714964688909489725 17596613518111758341058647)
          ·
            refine ⟨26394920277167637511587971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17596613518111758341058647 26394920277167637511587971)
            ·
              refine ⟨39592380415751456267381957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26394920277167637511587971 39592380415751456267381957)
              ·
                refine ⟨7423571327953398050134117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39592380415751456267381957 7423571327953398050134117)
                ·
                  refine ⟨1391919623991262134400147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7423571327953398050134117 1391919623991262134400147)
                  ·
                    refine ⟨2087879435986893201600221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1391919623991262134400147 2087879435986893201600221)
                    ·
                      refine ⟨782954788495084950600083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2087879435986893201600221 782954788495084950600083)
                      ·
                        rfl

theorem cell23_1524799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4, 1, 3].length) (baseStart_1524799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524799 prefixEnd_1524799 := by exact prefixLift 1524799
  have htrace : WordTrace (prefixWord ++ tailWord_1524799) baseStart_1524799 baseEnd_1524799 := by
    simpa [prefixWord, tailWord_1524799, baseEnd_1524799] using wordTrace_append hprefix tailTrace_1524799
  have hstable : (prefixWord ++ tailWord_1524799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524799).length < 2 ^ (prefixWord ++ tailWord_1524799).sum := by decide
  have hdescent : baseEnd_1524799 < baseStart_1524799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524809 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 5, 3, 2]
def baseStart_1524809 : Nat := 118140960795 + 1524809 * 2 ^ 59
def prefixEnd_1524809 : Nat := 4983230072969 + 3 ^ 40 * 1524809 * 2
def baseEnd_1524809 : Nat := 782959923301629911475037

theorem tailTrace_1524809 : CollatzResearch.WordTrace tailWord_1524809 prefixEnd_1524809 782959923301629911475037 := by
  unfold tailWord_1524809
  simp only [CollatzResearch.WordTrace]
  refine ⟨55614353132884884489481481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37076235421923256326320987 55614353132884884489481481)
  ·
    refine ⟨41710764849663663367111111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55614353132884884489481481 41710764849663663367111111)
    ·
      refine ⟨62566147274495495050666667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41710764849663663367111111 62566147274495495050666667)
      ·
        refine ⟨93849220911743242576000001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62566147274495495050666667 93849220911743242576000001)
        ·
          refine ⟨70386915683807431932000001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93849220911743242576000001 70386915683807431932000001)
          ·
            refine ⟨52790186762855573949000001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70386915683807431932000001 52790186762855573949000001)
            ·
              refine ⟨39592640072141680461750001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52790186762855573949000001 39592640072141680461750001)
              ·
                refine ⟨29694480054106260346312501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39592640072141680461750001 29694480054106260346312501)
                ·
                  refine ⟨2783857505072461907466797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29694480054106260346312501 2783857505072461907466797)
                  ·
                    refine ⟨1043946564402173215300049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2783857505072461907466797 1043946564402173215300049)
                    ·
                      refine ⟨782959923301629911475037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1043946564402173215300049 782959923301629911475037)
                      ·
                        rfl

theorem cell23_1524809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 3, 2].length) (baseStart_1524809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524809 prefixEnd_1524809 := by exact prefixLift 1524809
  have htrace : WordTrace (prefixWord ++ tailWord_1524809) baseStart_1524809 baseEnd_1524809 := by
    simpa [prefixWord, tailWord_1524809, baseEnd_1524809] using wordTrace_append hprefix tailTrace_1524809
  have hstable : (prefixWord ++ tailWord_1524809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524809).length < 2 ^ (prefixWord ++ tailWord_1524809).sum := by decide
  have hdescent : baseEnd_1524809 < baseStart_1524809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524830 : List Nat := [4, 4, 1, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_1524830 : Nat := 118140960795 + 1524830 * 2 ^ 59
def prefixEnd_1524830 : Nat := 4983230072969 + 3 ^ 40 * 1524830 * 2
def baseEnd_1524830 : Nat := 782970706395374329312441

theorem tailTrace_1524830 : CollatzResearch.WordTrace tailWord_1524830 prefixEnd_1524830 782970706395374329312441 := by
  unfold tailWord_1524830
  simp only [CollatzResearch.WordTrace]
  refine ⟨6951889883226100634499493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37076746043872536717330629 6951889883226100634499493)
  ·
    refine ⟨1303479353104893868968655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6951889883226100634499493 1303479353104893868968655)
    ·
      refine ⟨1955219029657340803452983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1303479353104893868968655 1955219029657340803452983)
      ·
        refine ⟨2932828544486011205179475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1955219029657340803452983 2932828544486011205179475)
        ·
          refine ⟨4399242816729016807769213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2932828544486011205179475 4399242816729016807769213)
          ·
            refine ⟨1649716056273381302913455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4399242816729016807769213 1649716056273381302913455)
            ·
              refine ⟨2474574084410071954370183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1649716056273381302913455 2474574084410071954370183)
              ·
                refine ⟨3711861126615107931555275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2474574084410071954370183 3711861126615107931555275)
                ·
                  refine ⟨5567791689922661897332913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3711861126615107931555275 5567791689922661897332913)
                  ·
                    refine ⟨4175843767441996422999685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5567791689922661897332913 4175843767441996422999685)
                    ·
                      refine ⟨782970706395374329312441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4175843767441996422999685 782970706395374329312441)
                      ·
                        rfl

theorem cell23_1524830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_1524830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524830 prefixEnd_1524830 := by exact prefixLift 1524830
  have htrace : WordTrace (prefixWord ++ tailWord_1524830) baseStart_1524830 baseEnd_1524830 := by
    simpa [prefixWord, tailWord_1524830, baseEnd_1524830] using wordTrace_append hprefix tailTrace_1524830
  have hstable : (prefixWord ++ tailWord_1524830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524830).length < 2 ^ (prefixWord ++ tailWord_1524830).sum := by decide
  have hdescent : baseEnd_1524830 < baseStart_1524830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524832 : List Nat := [2, 1, 1, 3, 2, 2, 1, 3, 2, 6]
def baseStart_1524832 : Nat := 118140960795 + 1524832 * 2 ^ 59
def prefixEnd_1524832 : Nat := 4983230072969 + 3 ^ 40 * 1524832 * 2
def baseEnd_1524832 : Nat := 260990577785561107162477

theorem tailTrace_1524832 : CollatzResearch.WordTrace tailWord_1524832 prefixEnd_1524832 260990577785561107162477 := by
  unfold tailWord_1524832
  simp only [CollatzResearch.WordTrace]
  refine ⟨27807596005900779708784375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37076794674534372945045833 27807596005900779708784375)
  ·
    refine ⟨41711394008851169563176563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27807596005900779708784375 41711394008851169563176563)
    ·
      refine ⟨62567091013276754344764845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41711394008851169563176563 62567091013276754344764845)
      ·
        refine ⟨23462659129978782879286817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62567091013276754344764845 23462659129978782879286817)
        ·
          refine ⟨17596994347484087159465113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23462659129978782879286817 17596994347484087159465113)
          ·
            refine ⟨13197745760613065369598835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17596994347484087159465113 13197745760613065369598835)
            ·
              refine ⟨19796618640919598054398253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13197745760613065369598835 19796618640919598054398253)
              ·
                refine ⟨7423731990344849270399345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19796618640919598054398253 7423731990344849270399345)
                ·
                  refine ⟨5567798992758636952799509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7423731990344849270399345 5567798992758636952799509)
                  ·
                    refine ⟨260990577785561107162477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5567798992758636952799509 260990577785561107162477)
                    ·
                      rfl

theorem cell23_1524832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 2, 6].length) (baseStart_1524832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524832 prefixEnd_1524832 := by exact prefixLift 1524832
  have htrace : WordTrace (prefixWord ++ tailWord_1524832) baseStart_1524832 baseEnd_1524832 := by
    simpa [prefixWord, tailWord_1524832, baseEnd_1524832] using wordTrace_append hprefix tailTrace_1524832
  have hstable : (prefixWord ++ tailWord_1524832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524832).length < 2 ^ (prefixWord ++ tailWord_1524832).sum := by decide
  have hdescent : baseEnd_1524832 < baseStart_1524832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524856 : List Nat := [2, 1, 2, 1, 1, 1, 5, 2, 4, 2, 2]
def baseStart_1524856 : Nat := 118140960795 + 1524856 * 2 ^ 59
def prefixEnd_1524856 : Nat := 4983230072969 + 3 ^ 40 * 1524856 * 2
def baseEnd_1524856 : Nat := 782984056892391227587321

theorem tailTrace_1524856 : CollatzResearch.WordTrace tailWord_1524856 prefixEnd_1524856 782984056892391227587321 := by
  unfold tailWord_1524856
  simp only [CollatzResearch.WordTrace]
  refine ⟨27808033681857305758221211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37077378242476407677628281 27808033681857305758221211)
  ·
    refine ⟨41712050522785958637331817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27808033681857305758221211 41712050522785958637331817)
    ·
      refine ⟨31284037892089468977998863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41712050522785958637331817 31284037892089468977998863)
      ·
        refine ⟨46926056838134203466998295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31284037892089468977998863 46926056838134203466998295)
        ·
          refine ⟨70389085257201305200497443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46926056838134203466998295 70389085257201305200497443)
          ·
            refine ⟨105583627885801957800746165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70389085257201305200497443 105583627885801957800746165)
            ·
              refine ⟨9898465114293933543819953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105583627885801957800746165 9898465114293933543819953)
              ·
                refine ⟨7423848835720450157864965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9898465114293933543819953 7423848835720450157864965)
                ·
                  refine ⟨1391971656697584404599681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7423848835720450157864965 1391971656697584404599681)
                  ·
                    refine ⟨1043978742523188303449761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1391971656697584404599681 1043978742523188303449761)
                    ·
                      refine ⟨782984056892391227587321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1043978742523188303449761 782984056892391227587321)
                      ·
                        rfl

theorem cell23_1524856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 4, 2, 2].length) (baseStart_1524856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524856 prefixEnd_1524856 := by exact prefixLift 1524856
  have htrace : WordTrace (prefixWord ++ tailWord_1524856) baseStart_1524856 baseEnd_1524856 := by
    simpa [prefixWord, tailWord_1524856, baseEnd_1524856] using wordTrace_append hprefix tailTrace_1524856
  have hstable : (prefixWord ++ tailWord_1524856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524856).length < 2 ^ (prefixWord ++ tailWord_1524856).sum := by decide
  have hdescent : baseEnd_1524856 < baseStart_1524856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524890 : List Nat := [3, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2]
def baseStart_1524890 : Nat := 118140960795 + 1524890 * 2 ^ 59
def prefixEnd_1524890 : Nat := 4983230072969 + 3 ^ 40 * 1524890 * 2
def baseEnd_1524890 : Nat := 783001515234644094562165

theorem tailTrace_1524890 : CollatzResearch.WordTrace tailWord_1524890 prefixEnd_1524890 783001515234644094562165 := by
  unfold tailWord_1524890
  simp only [CollatzResearch.WordTrace]
  refine ⟨13904326861397858830795031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37078204963727623548786749 13904326861397858830795031)
  ·
    refine ⟨20856490292096788246192547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13904326861397858830795031 20856490292096788246192547)
    ·
      refine ⟨31284735438145182369288821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20856490292096788246192547 31284735438145182369288821)
      ·
        refine ⟨2932943947326110847120827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31284735438145182369288821 2932943947326110847120827)
        ·
          refine ⟨4399415920989166270681241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2932943947326110847120827 4399415920989166270681241)
          ·
            refine ⟨3299561940741874703010931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4399415920989166270681241 3299561940741874703010931)
            ·
              refine ⟨4949342911112812054516397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3299561940741874703010931 4949342911112812054516397)
              ·
                refine ⟨1856003591667304520443649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4949342911112812054516397 1856003591667304520443649)
                ·
                  refine ⟨1392002693750478390332737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1856003591667304520443649 1392002693750478390332737)
                  ·
                    refine ⟨1044002020312858792749553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1392002693750478390332737 1044002020312858792749553)
                    ·
                      refine ⟨783001515234644094562165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1044002020312858792749553 783001515234644094562165)
                      ·
                        rfl

theorem cell23_1524890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_1524890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524890 prefixEnd_1524890 := by exact prefixLift 1524890
  have htrace : WordTrace (prefixWord ++ tailWord_1524890) baseStart_1524890 baseEnd_1524890 := by
    simpa [prefixWord, tailWord_1524890, baseEnd_1524890] using wordTrace_append hprefix tailTrace_1524890
  have hstable : (prefixWord ++ tailWord_1524890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524890).length < 2 ^ (prefixWord ++ tailWord_1524890).sum := by decide
  have hdescent : baseEnd_1524890 < baseStart_1524890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524926 : List Nat := [4, 2, 1, 1, 3, 1, 2, 2, 2, 5]
def baseStart_1524926 : Nat := 118140960795 + 1524926 * 2 ^ 59
def prefixEnd_1524926 : Nat := 4983230072969 + 3 ^ 40 * 1524926 * 2
def baseEnd_1524926 : Nat := 261006666846068651237333

theorem tailTrace_1524926 : CollatzResearch.WordTrace tailWord_1524926 prefixEnd_1524926 261006666846068651237333 := by
  unfold tailWord_1524926
  simp only [CollatzResearch.WordTrace]
  refine ⟨6952327559182626683936329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37079080315640675647660421 6952327559182626683936329)
  ·
    refine ⟨5214245669386970012952247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6952327559182626683936329 5214245669386970012952247)
    ·
      refine ⟨7821368504080455019428371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5214245669386970012952247 7821368504080455019428371)
      ·
        refine ⟨11732052756120682529142557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7821368504080455019428371 11732052756120682529142557)
        ·
          refine ⟨4399519783545255948428459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11732052756120682529142557 4399519783545255948428459)
          ·
            refine ⟨6599279675317883922642689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4399519783545255948428459 6599279675317883922642689)
            ·
              refine ⟨4949459756488412941982017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6599279675317883922642689 4949459756488412941982017)
              ·
                refine ⟨3712094817366309706486513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4949459756488412941982017 3712094817366309706486513)
                ·
                  refine ⟨2784071113024732279864885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3712094817366309706486513 2784071113024732279864885)
                  ·
                    refine ⟨261006666846068651237333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2784071113024732279864885 261006666846068651237333)
                    ·
                      rfl

theorem cell23_1524926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_1524926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524926 prefixEnd_1524926 := by exact prefixLift 1524926
  have htrace : WordTrace (prefixWord ++ tailWord_1524926) baseStart_1524926 baseEnd_1524926 := by
    simpa [prefixWord, tailWord_1524926, baseEnd_1524926] using wordTrace_append hprefix tailTrace_1524926
  have hstable : (prefixWord ++ tailWord_1524926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524926).length < 2 ^ (prefixWord ++ tailWord_1524926).sum := by decide
  have hdescent : baseEnd_1524926 < baseStart_1524926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524990 : List Nat := [4, 2, 2, 1, 1, 2, 2, 4, 1, 4]
def baseStart_1524990 : Nat := 118140960795 + 1524990 * 2 ^ 59
def prefixEnd_1524990 : Nat := 4983230072969 + 3 ^ 40 * 1524990 * 2
def baseEnd_1524990 : Nat := 261017621100031234437235

theorem tailTrace_1524990 : CollatzResearch.WordTrace tailWord_1524990 prefixEnd_1524990 261017621100031234437235 := by
  unfold tailWord_1524990
  simp only [CollatzResearch.WordTrace]
  refine ⟨6952619343153644050227553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37080636496819434934546949 6952619343153644050227553)
  ·
    refine ⟨5214464507365233037670665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6952619343153644050227553 5214464507365233037670665)
    ·
      refine ⟨3910848380523924778252999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5214464507365233037670665 3910848380523924778252999)
      ·
        refine ⟨5866272570785887167379499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3910848380523924778252999 5866272570785887167379499)
        ·
          refine ⟨8799408856178830751069249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5866272570785887167379499 8799408856178830751069249)
          ·
            refine ⟨6599556642134123063301937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8799408856178830751069249 6599556642134123063301937)
            ·
              refine ⟨4949667481600592297476453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6599556642134123063301937 4949667481600592297476453)
              ·
                refine ⟨928062652800111055776835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4949667481600592297476453 928062652800111055776835)
                ·
                  refine ⟨1392093979200166583665253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 928062652800111055776835 1392093979200166583665253)
                  ·
                    refine ⟨261017621100031234437235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1392093979200166583665253 261017621100031234437235)
                    ·
                      rfl

theorem cell23_1524990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_1524990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1524990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1524990 prefixEnd_1524990 := by exact prefixLift 1524990
  have htrace : WordTrace (prefixWord ++ tailWord_1524990) baseStart_1524990 baseEnd_1524990 := by
    simpa [prefixWord, tailWord_1524990, baseEnd_1524990] using wordTrace_append hprefix tailTrace_1524990
  have hstable : (prefixWord ++ tailWord_1524990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524990).length < 2 ^ (prefixWord ++ tailWord_1524990).sum := by decide
  have hdescent : baseEnd_1524990 < baseStart_1524990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525016 : List Nat := [2, 1, 2, 3, 1, 3, 1, 4, 1, 5]
def baseStart_1525016 : Nat := 118140960795 + 1525016 * 2 ^ 59
def prefixEnd_1525016 : Nat := 4983230072969 + 3 ^ 40 * 1525016 * 2
def baseEnd_1525016 : Nat := 261022071265703533862195

theorem tailTrace_1525016 : CollatzResearch.WordTrace tailWord_1525016 prefixEnd_1525016 261022071265703533862195 := by
  unfold tailWord_1525016
  simp only [CollatzResearch.WordTrace]
  refine ⟨27810951521567479421133451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37081268695423305894844601 27810951521567479421133451)
  ·
    refine ⟨41716427282351219131700177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27810951521567479421133451 41716427282351219131700177)
    ·
      refine ⟨31287320461763414348775133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41716427282351219131700177 31287320461763414348775133)
      ·
        refine ⟨11732745173161280380790675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31287320461763414348775133 11732745173161280380790675)
        ·
          refine ⟨17599117759741920571186013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11732745173161280380790675 17599117759741920571186013)
          ·
            refine ⟨6599669159903220214194755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17599117759741920571186013 6599669159903220214194755)
            ·
              refine ⟨9899503739854830321292133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6599669159903220214194755 9899503739854830321292133)
              ·
                refine ⟨1856156951222780685242275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9899503739854830321292133 1856156951222780685242275)
                ·
                  refine ⟨2784235426834171027863413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1856156951222780685242275 2784235426834171027863413)
                  ·
                    refine ⟨261022071265703533862195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2784235426834171027863413 261022071265703533862195)
                    ·
                      rfl

theorem cell23_1525016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 1, 5].length) (baseStart_1525016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525016 prefixEnd_1525016 := by exact prefixLift 1525016
  have htrace : WordTrace (prefixWord ++ tailWord_1525016) baseStart_1525016 baseEnd_1525016 := by
    simpa [prefixWord, tailWord_1525016, baseEnd_1525016] using wordTrace_append hprefix tailTrace_1525016
  have hstable : (prefixWord ++ tailWord_1525016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525016).length < 2 ^ (prefixWord ++ tailWord_1525016).sum := by decide
  have hdescent : baseEnd_1525016 < baseStart_1525016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525056 : List Nat := [2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 3]
def baseStart_1525056 : Nat := 118140960795 + 1525056 * 2 ^ 59
def prefixEnd_1525056 : Nat := 4983230072969 + 3 ^ 40 * 1525056 * 2
def baseEnd_1525056 : Nat := 783086753023290445086401

theorem tailTrace_1525056 : CollatzResearch.WordTrace tailWord_1525056 prefixEnd_1525056 783086753023290445086401 := by
  unfold tailWord_1525056
  simp only [CollatzResearch.WordTrace]
  refine ⟨27811680981495022836861511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37082241308660030449148681 27811680981495022836861511)
  ·
    refine ⟨41717521472242534255292267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27811680981495022836861511 41717521472242534255292267)
    ·
      refine ⟨62576282208363801382938401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41717521472242534255292267 62576282208363801382938401)
      ·
        refine ⟨46932211656272851037203801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62576282208363801382938401 46932211656272851037203801)
        ·
          refine ⟨35199158742204638277902851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46932211656272851037203801 35199158742204638277902851)
          ·
            refine ⟨52798738113306957416854277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35199158742204638277902851 52798738113306957416854277)
            ·
              refine ⟨9899763396245054515660177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52798738113306957416854277 9899763396245054515660177)
              ·
                refine ⟨7424822547183790886745133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9899763396245054515660177 7424822547183790886745133)
                ·
                  refine ⟨2784308455193921582529425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7424822547183790886745133 2784308455193921582529425)
                  ·
                    refine ⟨2088231341395441186897069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2784308455193921582529425 2088231341395441186897069)
                    ·
                      refine ⟨783086753023290445086401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2088231341395441186897069 783086753023290445086401)
                      ·
                        rfl

theorem cell23_1525056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 3].length) (baseStart_1525056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525056 prefixEnd_1525056 := by exact prefixLift 1525056
  have htrace : WordTrace (prefixWord ++ tailWord_1525056) baseStart_1525056 baseEnd_1525056 := by
    simpa [prefixWord, tailWord_1525056, baseEnd_1525056] using wordTrace_append hprefix tailTrace_1525056
  have hstable : (prefixWord ++ tailWord_1525056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525056).length < 2 ^ (prefixWord ++ tailWord_1525056).sum := by decide
  have hdescent : baseEnd_1525056 < baseStart_1525056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525063 : List Nat := [1, 1, 4, 1, 2, 4, 1, 3, 2, 4]
def baseStart_1525063 : Nat := 118140960795 + 1525063 * 2 ^ 59
def prefixEnd_1525063 : Nat := 4983230072969 + 3 ^ 40 * 1525063 * 2
def baseEnd_1525063 : Nat := 261030115795957305899623

theorem tailTrace_1525063 : CollatzResearch.WordTrace tailWord_1525063 prefixEnd_1525063 261030115795957305899623 := by
  unfold tailWord_1525063
  simp only [CollatzResearch.WordTrace]
  refine ⟨55623617273964685869227843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37082411515976457246151895 55623617273964685869227843)
  ·
    refine ⟨83435425910947028803841765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55623617273964685869227843 83435425910947028803841765)
    ·
      refine ⟨15644142358302567900720331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83435425910947028803841765 15644142358302567900720331)
      ·
        refine ⟨23466213537453851851080497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15644142358302567900720331 23466213537453851851080497)
        ·
          refine ⟨17599660153090388888310373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23466213537453851851080497 17599660153090388888310373)
          ·
            refine ⟨3299936278704447916558195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17599660153090388888310373 3299936278704447916558195)
            ·
              refine ⟨4949904418056671874837293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3299936278704447916558195 4949904418056671874837293)
              ·
                refine ⟨1856214156771251953063985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4949904418056671874837293 1856214156771251953063985)
                ·
                  refine ⟨1392160617578438964797989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1856214156771251953063985 1392160617578438964797989)
                  ·
                    refine ⟨261030115795957305899623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1392160617578438964797989 261030115795957305899623)
                    ·
                      rfl

theorem cell23_1525063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_1525063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525063 prefixEnd_1525063 := by exact prefixLift 1525063
  have htrace : WordTrace (prefixWord ++ tailWord_1525063) baseStart_1525063 baseEnd_1525063 := by
    simpa [prefixWord, tailWord_1525063, baseEnd_1525063] using wordTrace_append hprefix tailTrace_1525063
  have hstable : (prefixWord ++ tailWord_1525063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525063).length < 2 ^ (prefixWord ++ tailWord_1525063).sum := by decide
  have hdescent : baseEnd_1525063 < baseStart_1525063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525089 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 4, 7]
def baseStart_1525089 : Nat := 118140960795 + 1525089 * 2 ^ 59
def prefixEnd_1525089 : Nat := 4983230072969 + 3 ^ 40 * 1525089 * 2
def baseEnd_1525089 : Nat := 261034565961629605324583

theorem tailTrace_1525089 : CollatzResearch.WordTrace tailWord_1525089 prefixEnd_1525089 261034565961629605324583 := by
  unfold tailWord_1525089
  simp only [CollatzResearch.WordTrace]
  refine ⟨55624565571870492309674321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37083043714580328206449547 55624565571870492309674321)
  ·
    refine ⟨41718424178902869232255741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55624565571870492309674321 41718424178902869232255741)
    ·
      refine ⟨15644409067088575962095903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41718424178902869232255741 15644409067088575962095903)
      ·
        refine ⟨23466613600632863943143855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15644409067088575962095903 23466613600632863943143855)
        ·
          refine ⟨35199920400949295914715783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23466613600632863943143855 35199920400949295914715783)
          ·
            refine ⟨52799880601423943872073675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35199920400949295914715783 52799880601423943872073675)
            ·
              refine ⟨79199820902135915808110513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52799880601423943872073675 79199820902135915808110513)
              ·
                refine ⟨59399865676601936856082885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79199820902135915808110513 59399865676601936856082885)
                ·
                  refine ⟨11137474814362863160515541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59399865676601936856082885 11137474814362863160515541)
                  ·
                    refine ⟨261034565961629605324583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11137474814362863160515541 261034565961629605324583)
                    ·
                      rfl

theorem cell23_1525089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_1525089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525089 prefixEnd_1525089 := by exact prefixLift 1525089
  have htrace : WordTrace (prefixWord ++ tailWord_1525089) baseStart_1525089 baseEnd_1525089 := by
    simpa [prefixWord, tailWord_1525089, baseEnd_1525089] using wordTrace_append hprefix tailTrace_1525089
  have hstable : (prefixWord ++ tailWord_1525089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525089).length < 2 ^ (prefixWord ++ tailWord_1525089).sum := by decide
  have hdescent : baseEnd_1525089 < baseStart_1525089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525113 : List Nat := [1, 2, 1, 3, 2, 1, 3, 2, 3, 3, 2]
def baseStart_1525113 : Nat := 118140960795 + 1525113 * 2 ^ 59
def prefixEnd_1525113 : Nat := 4983230072969 + 3 ^ 40 * 1525113 * 2
def baseEnd_1525113 : Nat := 783116021420596722073639

theorem tailTrace_1525113 : CollatzResearch.WordTrace tailWord_1525113 prefixEnd_1525113 783116021420596722073639 := by
  unfold tailWord_1525113
  simp only [CollatzResearch.WordTrace]
  refine ⟨55625440923783544408547993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37083627282522362939031995 55625440923783544408547993)
  ·
    refine ⟨41719080692837658306410995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55625440923783544408547993 41719080692837658306410995)
    ·
      refine ⟨62578621039256487459616493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41719080692837658306410995 62578621039256487459616493)
      ·
        refine ⟨23466982889721182797356185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62578621039256487459616493 23466982889721182797356185)
        ·
          refine ⟨17600237167290887098017139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23466982889721182797356185 17600237167290887098017139)
          ·
            refine ⟨26400355750936330647025709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17600237167290887098017139 26400355750936330647025709)
            ·
              refine ⟨9900133406601123992634641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26400355750936330647025709 9900133406601123992634641)
              ·
                refine ⟨7425100054950842994475981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9900133406601123992634641 7425100054950842994475981)
                ·
                  refine ⟨2784412520606566122928493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7425100054950842994475981 2784412520606566122928493)
                  ·
                    refine ⟨1044154695227462296098185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2784412520606566122928493 1044154695227462296098185)
                    ·
                      refine ⟨783116021420596722073639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1044154695227462296098185 783116021420596722073639)
                      ·
                        rfl

theorem cell23_1525113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 3, 2].length) (baseStart_1525113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525113 prefixEnd_1525113 := by exact prefixLift 1525113
  have htrace : WordTrace (prefixWord ++ tailWord_1525113) baseStart_1525113 baseEnd_1525113 := by
    simpa [prefixWord, tailWord_1525113, baseEnd_1525113] using wordTrace_append hprefix tailTrace_1525113
  have hstable : (prefixWord ++ tailWord_1525113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525113).length < 2 ^ (prefixWord ++ tailWord_1525113).sum := by decide
  have hdescent : baseEnd_1525113 < baseStart_1525113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525146 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5]
def baseStart_1525146 : Nat := 118140960795 + 1525146 * 2 ^ 59
def prefixEnd_1525146 : Nat := 4983230072969 + 3 ^ 40 * 1525146 * 2
def baseEnd_1525146 : Nat := 783132966282195092960987

theorem tailTrace_1525146 : CollatzResearch.WordTrace tailWord_1525146 prefixEnd_1525146 783132966282195092960987 := by
  unfold tailWord_1525146
  simp only [CollatzResearch.WordTrace]
  refine ⟨13906661133165997761124823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37084429688442660696332861 13906661133165997761124823)
  ·
    refine ⟨20859991699748996641687235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13906661133165997761124823 20859991699748996641687235)
    ·
      refine ⟨31289987549623494962530853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20859991699748996641687235 31289987549623494962530853)
      ·
        refine ⟨5866872665554405305474535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31289987549623494962530853 5866872665554405305474535)
        ·
          refine ⟨8800308998331607958211803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5866872665554405305474535 8800308998331607958211803)
          ·
            refine ⟨13200463497497411937317705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8800308998331607958211803 13200463497497411937317705)
            ·
              refine ⟨9900347623123058952988279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13200463497497411937317705 9900347623123058952988279)
              ·
                refine ⟨14850521434684588429482419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9900347623123058952988279 14850521434684588429482419)
                ·
                  refine ⟨22275782152026882644223629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14850521434684588429482419 22275782152026882644223629)
                  ·
                    refine ⟨8353418307010080991583861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22275782152026882644223629 8353418307010080991583861)
                    ·
                      refine ⟨783132966282195092960987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8353418307010080991583861 783132966282195092960987)
                      ·
                        rfl

theorem cell23_1525146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_1525146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525146 prefixEnd_1525146 := by exact prefixLift 1525146
  have htrace : WordTrace (prefixWord ++ tailWord_1525146) baseStart_1525146 baseEnd_1525146 := by
    simpa [prefixWord, tailWord_1525146, baseEnd_1525146] using wordTrace_append hprefix tailTrace_1525146
  have hstable : (prefixWord ++ tailWord_1525146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525146).length < 2 ^ (prefixWord ++ tailWord_1525146).sum := by decide
  have hdescent : baseEnd_1525146 < baseStart_1525146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525173 : List Nat := [1, 3, 3, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_1525173 : Nat := 118140960795 + 1525173 * 2 ^ 59
def prefixEnd_1525173 : Nat := 4983230072969 + 3 ^ 40 * 1525173 * 2
def baseEnd_1525173 : Nat := 783146830259866487323363

theorem tailTrace_1525173 : CollatzResearch.WordTrace tailWord_1525173 prefixEnd_1525173 783146830259866487323363 := by
  unfold tailWord_1525173
  simp only [CollatzResearch.WordTrace]
  refine ⟨55627629303566174655732173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37085086202377449770488115 55627629303566174655732173)
  ·
    refine ⟨20860360988837315495899565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55627629303566174655732173 20860360988837315495899565)
    ·
      refine ⟨7822635370813993310962337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20860360988837315495899565 7822635370813993310962337)
      ·
        refine ⟨5866976528110494983221753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7822635370813993310962337 5866976528110494983221753)
        ·
          refine ⟨4400232396082871237416315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5866976528110494983221753 4400232396082871237416315)
          ·
            refine ⟨6600348594124306856124473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4400232396082871237416315 6600348594124306856124473)
            ·
              refine ⟨4950261445593230142093355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6600348594124306856124473 4950261445593230142093355)
              ·
                refine ⟨7425392168389845213140033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4950261445593230142093355 7425392168389845213140033)
                ·
                  refine ⟨5569044126292383909855025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7425392168389845213140033 5569044126292383909855025)
                  ·
                    refine ⟨4176783094719287932391269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5569044126292383909855025 4176783094719287932391269)
                    ·
                      refine ⟨783146830259866487323363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4176783094719287932391269 783146830259866487323363)
                      ·
                        rfl

theorem cell23_1525173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_1525173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525173 prefixEnd_1525173 := by exact prefixLift 1525173
  have htrace : WordTrace (prefixWord ++ tailWord_1525173) baseStart_1525173 baseEnd_1525173 := by
    simpa [prefixWord, tailWord_1525173, baseEnd_1525173] using wordTrace_append hprefix tailTrace_1525173
  have hstable : (prefixWord ++ tailWord_1525173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525173).length < 2 ^ (prefixWord ++ tailWord_1525173).sum := by decide
  have hdescent : baseEnd_1525173 < baseStart_1525173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525177 : List Nat := [1, 2, 1, 4, 4, 2, 1, 1, 1, 4, 2]
def baseStart_1525177 : Nat := 118140960795 + 1525177 * 2 ^ 59
def prefixEnd_1525177 : Nat := 4983230072969 + 3 ^ 40 * 1525177 * 2
def baseEnd_1525177 : Nat := 783148884182484471673345

theorem tailTrace_1525177 : CollatzResearch.WordTrace tailWord_1525177 prefixEnd_1525177 783148884182484471673345 := by
  unfold tailWord_1525177
  simp only [CollatzResearch.WordTrace]
  refine ⟨55627775195551683338877785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37085183463701122225918523 55627775195551683338877785)
  ·
    refine ⟨41720831396663762504158339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55627775195551683338877785 41720831396663762504158339)
    ·
      refine ⟨62581247094995643756237509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41720831396663762504158339 62581247094995643756237509)
      ·
        refine ⟨11733983830311683204294533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62581247094995643756237509 11733983830311683204294533)
        ·
          refine ⟨2200121968183440600805225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11733983830311683204294533 2200121968183440600805225)
          ·
            refine ⟨1650091476137580450603919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2200121968183440600805225 1650091476137580450603919)
            ·
              refine ⟨2475137214206370675905879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1650091476137580450603919 2475137214206370675905879)
              ·
                refine ⟨3712705821309556013858819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2475137214206370675905879 3712705821309556013858819)
                ·
                  refine ⟨5569058731964334020788229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3712705821309556013858819 5569058731964334020788229)
                  ·
                    refine ⟨1044198512243312628897793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5569058731964334020788229 1044198512243312628897793)
                    ·
                      refine ⟨783148884182484471673345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1044198512243312628897793 783148884182484471673345)
                      ·
                        rfl

theorem cell23_1525177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_1525177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525177 prefixEnd_1525177 := by exact prefixLift 1525177
  have htrace : WordTrace (prefixWord ++ tailWord_1525177) baseStart_1525177 baseEnd_1525177 := by
    simpa [prefixWord, tailWord_1525177, baseEnd_1525177] using wordTrace_append hprefix tailTrace_1525177
  have hstable : (prefixWord ++ tailWord_1525177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525177).length < 2 ^ (prefixWord ++ tailWord_1525177).sum := by decide
  have hdescent : baseEnd_1525177 < baseStart_1525177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525213 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 4, 5]
def baseStart_1525213 : Nat := 118140960795 + 1525213 * 2 ^ 59
def prefixEnd_1525213 : Nat := 4983230072969 + 3 ^ 40 * 1525213 * 2
def baseEnd_1525213 : Nat := 261055789828682110274393

theorem tailTrace_1525213 : CollatzResearch.WordTrace tailWord_1525213 prefixEnd_1525213 261055789828682110274393 := by
  unfold tailWord_1525213
  simp only [CollatzResearch.WordTrace]
  refine ⟨55629088223421261487188293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37086058815614174324792195 55629088223421261487188293)
  ·
    refine ⟨10430454041891486528847805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55629088223421261487188293 10430454041891486528847805)
    ·
      refine ⟨3911420265709307448317927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10430454041891486528847805 3911420265709307448317927)
      ·
        refine ⟨5867130398563961172476891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3911420265709307448317927 5867130398563961172476891)
        ·
          refine ⟨8800695597845941758715337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5867130398563961172476891 8800695597845941758715337)
          ·
            refine ⟨6600521698384456319036503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8800695597845941758715337 6600521698384456319036503)
            ·
              refine ⟨9900782547576684478554755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6600521698384456319036503 9900782547576684478554755)
              ·
                refine ⟨14851173821365026717832133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9900782547576684478554755 14851173821365026717832133)
                ·
                  refine ⟨2784595091505942509593525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14851173821365026717832133 2784595091505942509593525)
                  ·
                    refine ⟨261055789828682110274393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2784595091505942509593525 261055789828682110274393)
                    ·
                      rfl

theorem cell23_1525213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_1525213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525213 prefixEnd_1525213 := by exact prefixLift 1525213
  have htrace : WordTrace (prefixWord ++ tailWord_1525213) baseStart_1525213 baseEnd_1525213 := by
    simpa [prefixWord, tailWord_1525213, baseEnd_1525213] using wordTrace_append hprefix tailTrace_1525213
  have hstable : (prefixWord ++ tailWord_1525213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525213).length < 2 ^ (prefixWord ++ tailWord_1525213).sum := by decide
  have hdescent : baseEnd_1525213 < baseStart_1525213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525216 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 4]
def baseStart_1525216 : Nat := 118140960795 + 1525216 * 2 ^ 59
def prefixEnd_1525216 : Nat := 4983230072969 + 3 ^ 40 * 1525216 * 2
def baseEnd_1525216 : Nat := 783168909928009819085665

theorem tailTrace_1525216 : CollatzResearch.WordTrace tailWord_1525216 prefixEnd_1525216 783168909928009819085665 := by
  unfold tailWord_1525216
  simp only [CollatzResearch.WordTrace]
  refine ⟨27814598821205196499773751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37086131761606928666365001 27814598821205196499773751)
  ·
    refine ⟨41721898231807794749660627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27814598821205196499773751 41721898231807794749660627)
    ·
      refine ⟨62582847347711692124490941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41721898231807794749660627 62582847347711692124490941)
      ·
        refine ⟨23468567755391884546684103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62582847347711692124490941 23468567755391884546684103)
        ·
          refine ⟨35202851633087826820026155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23468567755391884546684103 35202851633087826820026155)
          ·
            refine ⟨52804277449631740230039233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35202851633087826820026155 52804277449631740230039233)
            ·
              refine ⟨39603208087223805172529425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52804277449631740230039233 39603208087223805172529425)
              ·
                refine ⟨29702406065417853879397069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39603208087223805172529425 29702406065417853879397069)
                ·
                  refine ⟨11138402274531695204773901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29702406065417853879397069 11138402274531695204773901)
                  ·
                    refine ⟨4176900852949385701790213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11138402274531695204773901 4176900852949385701790213)
                    ·
                      refine ⟨783168909928009819085665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4176900852949385701790213 783168909928009819085665)
                      ·
                        rfl

theorem cell23_1525216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_1525216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525216 prefixEnd_1525216 := by exact prefixLift 1525216
  have htrace : WordTrace (prefixWord ++ tailWord_1525216) baseStart_1525216 baseEnd_1525216 := by
    simpa [prefixWord, tailWord_1525216, baseEnd_1525216] using wordTrace_append hprefix tailTrace_1525216
  have hstable : (prefixWord ++ tailWord_1525216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525216).length < 2 ^ (prefixWord ++ tailWord_1525216).sum := by decide
  have hdescent : baseEnd_1525216 < baseStart_1525216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525223 : List Nat := [1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 5]
def baseStart_1525223 : Nat := 118140960795 + 1525223 * 2 ^ 59
def prefixEnd_1525223 : Nat := 4983230072969 + 3 ^ 40 * 1525223 * 2
def baseEnd_1525223 : Nat := 783172504292591291698133

theorem tailTrace_1525223 : CollatzResearch.WordTrace tailWord_1525223 prefixEnd_1525223 783172504292591291698133 := by
  unfold tailWord_1525223
  simp only [CollatzResearch.WordTrace]
  refine ⟨55629452953385033195052323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37086301968923355463368215 55629452953385033195052323)
  ·
    refine ⟨83444179430077549792578485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55629452953385033195052323 83444179430077549792578485)
    ·
      refine ⟨7822891821569770293054233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83444179430077549792578485 7822891821569770293054233)
      ·
        refine ⟨5867168866177327719790675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7822891821569770293054233 5867168866177327719790675)
        ·
          refine ⟨8800753299265991579686013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5867168866177327719790675 8800753299265991579686013)
          ·
            refine ⟨3300282487224746842382255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8800753299265991579686013 3300282487224746842382255)
            ·
              refine ⟨4950423730837120263573383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3300282487224746842382255 4950423730837120263573383)
              ·
                refine ⟨7425635596255680395360075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4950423730837120263573383 7425635596255680395360075)
                ·
                  refine ⟨11138453394383520593040113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7425635596255680395360075 11138453394383520593040113)
                  ·
                    refine ⟨8353840045787640444780085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11138453394383520593040113 8353840045787640444780085)
                    ·
                      refine ⟨783172504292591291698133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8353840045787640444780085 783172504292591291698133)
                      ·
                        rfl

theorem cell23_1525223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_1525223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525223 prefixEnd_1525223 := by exact prefixLift 1525223
  have htrace : WordTrace (prefixWord ++ tailWord_1525223) baseStart_1525223 baseEnd_1525223 := by
    simpa [prefixWord, tailWord_1525223, baseEnd_1525223] using wordTrace_append hprefix tailTrace_1525223
  have hstable : (prefixWord ++ tailWord_1525223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525223).length < 2 ^ (prefixWord ++ tailWord_1525223).sum := by decide
  have hdescent : baseEnd_1525223 < baseStart_1525223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525256 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 10]
def baseStart_1525256 : Nat := 118140960795 + 1525256 * 2 ^ 59
def prefixEnd_1525256 : Nat := 4983230072969 + 3 ^ 40 * 1525256 * 2
def baseEnd_1525256 : Nat := 87021049906021073620609

theorem tailTrace_1525256 : CollatzResearch.WordTrace tailWord_1525256 prefixEnd_1525256 87021049906021073620609 := by
  unfold tailWord_1525256
  simp only [CollatzResearch.WordTrace]
  refine ⟨27815328281132739915501811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37087104374843653220669081 27815328281132739915501811)
  ·
    refine ⟨41722992421699109873252717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27815328281132739915501811 41722992421699109873252717)
    ·
      refine ⟨15646122158137166202469769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41722992421699109873252717 15646122158137166202469769)
      ·
        refine ⟨11734591618602874651852327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15646122158137166202469769 11734591618602874651852327)
        ·
          refine ⟨17601887427904311977778491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11734591618602874651852327 17601887427904311977778491)
          ·
            refine ⟨26402831141856467966667737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17601887427904311977778491 26402831141856467966667737)
            ·
              refine ⟨19802123356392350975000803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26402831141856467966667737 19802123356392350975000803)
              ·
                refine ⟨29703185034588526462501205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19802123356392350975000803 29703185034588526462501205)
                ·
                  refine ⟨87021049906021073620609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 29703185034588526462501205 87021049906021073620609)
                  ·
                    rfl

theorem cell23_1525256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 10].length) (baseStart_1525256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525256 prefixEnd_1525256 := by exact prefixLift 1525256
  have htrace : WordTrace (prefixWord ++ tailWord_1525256) baseStart_1525256 baseEnd_1525256 := by
    simpa [prefixWord, tailWord_1525256, baseEnd_1525256] using wordTrace_append hprefix tailTrace_1525256
  have hstable : (prefixWord ++ tailWord_1525256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525256).length < 2 ^ (prefixWord ++ tailWord_1525256).sum := by decide
  have hdescent : baseEnd_1525256 < baseStart_1525256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525277 : List Nat := [1, 4, 2, 2, 1, 1, 3, 4, 1, 4]
def baseStart_1525277 : Nat := 118140960795 + 1525277 * 2 ^ 59
def prefixEnd_1525277 : Nat := 4983230072969 + 3 ^ 40 * 1525277 * 2
def baseEnd_1525277 : Nat := 261066744082644693474295

theorem tailTrace_1525277 : CollatzResearch.WordTrace tailWord_1525277 prefixEnd_1525277 261066744082644693474295 := by
  unfold tailWord_1525277
  simp only [CollatzResearch.WordTrace]
  refine ⟨55631422495189400417518085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37087614996792933611678723 55631422495189400417518085)
  ·
    refine ⟨10430891717848012578284641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55631422495189400417518085 10430891717848012578284641)
    ·
      refine ⟨7823168788386009433713481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10430891717848012578284641 7823168788386009433713481)
      ·
        refine ⟨5867376591289507075285111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7823168788386009433713481 5867376591289507075285111)
        ·
          refine ⟨8801064886934260612927667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5867376591289507075285111 8801064886934260612927667)
          ·
            refine ⟨13201597330401390919391501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8801064886934260612927667 13201597330401390919391501)
            ·
              refine ⟨4950598998900521594771813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13201597330401390919391501 4950598998900521594771813)
              ·
                refine ⟨928237312293847799019715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4950598998900521594771813 928237312293847799019715)
                ·
                  refine ⟨1392355968440771698529573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 928237312293847799019715 1392355968440771698529573)
                  ·
                    refine ⟨261066744082644693474295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1392355968440771698529573 261066744082644693474295)
                    ·
                      rfl

theorem cell23_1525277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_1525277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525277 prefixEnd_1525277 := by exact prefixLift 1525277
  have htrace : WordTrace (prefixWord ++ tailWord_1525277) baseStart_1525277 baseEnd_1525277 := by
    simpa [prefixWord, tailWord_1525277, baseEnd_1525277] using wordTrace_append hprefix tailTrace_1525277
  have hstable : (prefixWord ++ tailWord_1525277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525277).length < 2 ^ (prefixWord ++ tailWord_1525277).sum := by decide
  have hdescent : baseEnd_1525277 < baseStart_1525277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525296 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 7]
def baseStart_1525296 : Nat := 118140960795 + 1525296 * 2 ^ 59
def prefixEnd_1525296 : Nat := 4983230072969 + 3 ^ 40 * 1525296 * 2
def baseEnd_1525296 : Nat := 783209988380369506085297

theorem tailTrace_1525296 : CollatzResearch.WordTrace tailWord_1525296 prefixEnd_1525296 783209988380369506085297 := by
  unfold tailWord_1525296
  simp only [CollatzResearch.WordTrace]
  refine ⟨27816057741060283331229871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37088076988080377774973161 27816057741060283331229871)
  ·
    refine ⟨41724086611590424996844807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27816057741060283331229871 41724086611590424996844807)
    ·
      refine ⟨62586129917385637495267211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41724086611590424996844807 62586129917385637495267211)
      ·
        refine ⟨93879194876078456242900817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62586129917385637495267211 93879194876078456242900817)
        ·
          refine ⟨70409396157058842182175613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93879194876078456242900817 70409396157058842182175613)
          ·
            refine ⟨26403523558897065818315855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70409396157058842182175613 26403523558897065818315855)
            ·
              refine ⟨39605285338345598727473783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26403523558897065818315855 39605285338345598727473783)
              ·
                refine ⟨59407928007518398091210675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39605285338345598727473783 59407928007518398091210675)
                ·
                  refine ⟨89111892011277597136816013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59407928007518398091210675 89111892011277597136816013)
                  ·
                    refine ⟨33416959504229098926306005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89111892011277597136816013 33416959504229098926306005)
                    ·
                      refine ⟨783209988380369506085297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 33416959504229098926306005 783209988380369506085297)
                      ·
                        rfl

theorem cell23_1525296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 7].length) (baseStart_1525296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525296 prefixEnd_1525296 := by exact prefixLift 1525296
  have htrace : WordTrace (prefixWord ++ tailWord_1525296) baseStart_1525296 baseEnd_1525296 := by
    simpa [prefixWord, tailWord_1525296, baseEnd_1525296] using wordTrace_append hprefix tailTrace_1525296
  have hstable : (prefixWord ++ tailWord_1525296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525296).length < 2 ^ (prefixWord ++ tailWord_1525296).sum := by decide
  have hdescent : baseEnd_1525296 < baseStart_1525296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525303 : List Nat := [1, 1, 3, 1, 2, 4, 2, 1, 3, 5]
def baseStart_1525303 : Nat := 118140960795 + 1525303 * 2 ^ 59
def prefixEnd_1525303 : Nat := 4983230072969 + 3 ^ 40 * 1525303 * 2
def baseEnd_1525303 : Nat := 261071194248316992899255

theorem tailTrace_1525303 : CollatzResearch.WordTrace tailWord_1525303 prefixEnd_1525303 261071194248316992899255 := by
  unfold tailWord_1525303
  simp only [CollatzResearch.WordTrace]
  refine ⟨55632370793095206857964563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37088247195396804571976375 55632370793095206857964563)
  ·
    refine ⟨83448556189642810286946845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55632370793095206857964563 83448556189642810286946845)
    ·
      refine ⟨31293208571116053857605067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83448556189642810286946845 31293208571116053857605067)
      ·
        refine ⟨46939812856674080786407601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31293208571116053857605067 46939812856674080786407601)
        ·
          refine ⟨35204859642505560589805701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46939812856674080786407601 35204859642505560589805701)
          ·
            refine ⟨6600911182969792610588569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35204859642505560589805701 6600911182969792610588569)
            ·
              refine ⟨4950683387227344457941427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6600911182969792610588569 4950683387227344457941427)
              ·
                refine ⟨7426025080841016686912141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4950683387227344457941427 7426025080841016686912141)
                ·
                  refine ⟨2784759405315381257592053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7426025080841016686912141 2784759405315381257592053)
                  ·
                    refine ⟨261071194248316992899255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2784759405315381257592053 261071194248316992899255)
                    ·
                      rfl

theorem cell23_1525303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 5].length) (baseStart_1525303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525303 prefixEnd_1525303 := by exact prefixLift 1525303
  have htrace : WordTrace (prefixWord ++ tailWord_1525303) baseStart_1525303 baseEnd_1525303 := by
    simpa [prefixWord, tailWord_1525303, baseEnd_1525303] using wordTrace_append hprefix tailTrace_1525303
  have hstable : (prefixWord ++ tailWord_1525303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525303).length < 2 ^ (prefixWord ++ tailWord_1525303).sum := by decide
  have hdescent : baseEnd_1525303 < baseStart_1525303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525377 : List Nat := [1, 2, 4, 2, 1, 2, 2, 3, 1, 2, 3]
def baseStart_1525377 : Nat := 118140960795 + 1525377 * 2 ^ 59
def prefixEnd_1525377 : Nat := 4983230072969 + 3 ^ 40 * 1525377 * 2
def baseEnd_1525377 : Nat := 783251580313383689172425

theorem tailTrace_1525377 : CollatzResearch.WordTrace tailWord_1525377 prefixEnd_1525377 783251580313383689172425 := by
  unfold tailWord_1525377
  simp only [CollatzResearch.WordTrace]
  refine ⟨55635069794827117496158385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37090046529884744997438923 55635069794827117496158385)
  ·
    refine ⟨41726302346120338122118789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55635069794827117496158385 41726302346120338122118789)
    ·
      refine ⟨7823681689897563397897273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41726302346120338122118789 7823681689897563397897273)
      ·
        refine ⟨5867761267423172548422955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7823681689897563397897273 5867761267423172548422955)
        ·
          refine ⟨8801641901134758822634433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5867761267423172548422955 8801641901134758822634433)
          ·
            refine ⟨6601231425851069116975825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8801641901134758822634433 6601231425851069116975825)
            ·
              refine ⟨4950923569388301837731869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6601231425851069116975825 4950923569388301837731869)
              ·
                refine ⟨1856596338520613189149451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4950923569388301837731869 1856596338520613189149451)
                ·
                  refine ⟨2784894507780919783724177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1856596338520613189149451 2784894507780919783724177)
                  ·
                    refine ⟨2088670880835689837793133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2784894507780919783724177 2088670880835689837793133)
                    ·
                      refine ⟨783251580313383689172425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2088670880835689837793133 783251580313383689172425)
                      ·
                        rfl

theorem cell23_1525377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_1525377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525377 prefixEnd_1525377 := by exact prefixLift 1525377
  have htrace : WordTrace (prefixWord ++ tailWord_1525377) baseStart_1525377 baseEnd_1525377 := by
    simpa [prefixWord, tailWord_1525377, baseEnd_1525377] using wordTrace_append hprefix tailTrace_1525377
  have hstable : (prefixWord ++ tailWord_1525377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525377).length < 2 ^ (prefixWord ++ tailWord_1525377).sum := by decide
  have hdescent : baseEnd_1525377 < baseStart_1525377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525380 : List Nat := [2, 3, 2, 1, 4, 2, 9]
def baseStart_1525380 : Nat := 118140960795 + 1525380 * 2 ^ 59
def prefixEnd_1525380 : Nat := 4983230072969 + 3 ^ 40 * 1525380 * 2
def baseEnd_1525380 : Nat := 9669791614263545400431

theorem tailTrace_1525380 : CollatzResearch.WordTrace tailWord_1525380 prefixEnd_1525380 9669791614263545400431 := by
  unfold tailWord_1525380
  simp only [CollatzResearch.WordTrace]
  refine ⟨27817589606908124504258797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37090119475877499339011729 27817589606908124504258797)
  ·
    refine ⟨10431596102590546689097049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27817589606908124504258797 10431596102590546689097049)
    ·
      refine ⟨7823697076942910016822787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10431596102590546689097049 7823697076942910016822787)
      ·
        refine ⟨11735545615414365025234181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7823697076942910016822787 11735545615414365025234181)
        ·
          refine ⟨2200414802890193442231409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11735545615414365025234181 2200414802890193442231409)
          ·
            refine ⟨1650311102167645081673557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2200414802890193442231409 1650311102167645081673557)
            ·
              refine ⟨9669791614263545400431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1650311102167645081673557 9669791614263545400431)
              ·
                rfl

theorem cell23_1525380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 9].length) (baseStart_1525380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525380 prefixEnd_1525380 := by exact prefixLift 1525380
  have htrace : WordTrace (prefixWord ++ tailWord_1525380) baseStart_1525380 baseEnd_1525380 := by
    simpa [prefixWord, tailWord_1525380, baseEnd_1525380] using wordTrace_append hprefix tailTrace_1525380
  have hstable : (prefixWord ++ tailWord_1525380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525380).length < 2 ^ (prefixWord ++ tailWord_1525380).sum := by decide
  have hdescent : baseEnd_1525380 < baseStart_1525380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525442 : List Nat := [3, 5, 1, 2, 1, 1, 1, 4, 1, 2, 2]
def baseStart_1525442 : Nat := 118140960795 + 1525442 * 2 ^ 59
def prefixEnd_1525442 : Nat := 4983230072969 + 3 ^ 40 * 1525442 * 2
def baseEnd_1525442 : Nat := 783284956555925934859627

theorem tailTrace_1525442 : CollatzResearch.WordTrace tailWord_1525442 prefixEnd_1525442 783284956555925934859627 := by
  unfold tailWord_1525442
  simp only [CollatzResearch.WordTrace]
  refine ⟨13909360134897908399318645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37091627026394422398183053 13909360134897908399318645)
  ·
    refine ⟨1304002512646678912436123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13909360134897908399318645 1304002512646678912436123)
    ·
      refine ⟨1956003768970018368654185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1304002512646678912436123 1956003768970018368654185)
      ·
        refine ⟨1467002826727513776490639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1956003768970018368654185 1467002826727513776490639)
        ·
          refine ⟨2200504240091270664735959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1467002826727513776490639 2200504240091270664735959)
          ·
            refine ⟨3300756360136905997103939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2200504240091270664735959 3300756360136905997103939)
            ·
              refine ⟨4951134540205358995655909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3300756360136905997103939 4951134540205358995655909)
              ·
                refine ⟨928337726288504811685483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4951134540205358995655909 928337726288504811685483)
                ·
                  refine ⟨1392506589432757217528225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 928337726288504811685483 1392506589432757217528225)
                  ·
                    refine ⟨1044379942074567913146169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1392506589432757217528225 1044379942074567913146169)
                    ·
                      refine ⟨783284956555925934859627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1044379942074567913146169 783284956555925934859627)
                      ·
                        rfl

theorem cell23_1525442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_1525442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525442 prefixEnd_1525442 := by exact prefixLift 1525442
  have htrace : WordTrace (prefixWord ++ tailWord_1525442) baseStart_1525442 baseEnd_1525442 := by
    simpa [prefixWord, tailWord_1525442, baseEnd_1525442] using wordTrace_append hprefix tailTrace_1525442
  have hstable : (prefixWord ++ tailWord_1525442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525442).length < 2 ^ (prefixWord ++ tailWord_1525442).sum := by decide
  have hdescent : baseEnd_1525442 < baseStart_1525442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525443 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 4]
def baseStart_1525443 : Nat := 118140960795 + 1525443 * 2 ^ 59
def prefixEnd_1525443 : Nat := 4983230072969 + 3 ^ 40 * 1525443 * 2
def baseEnd_1525443 : Nat := 783285470036580430947121

theorem tailTrace_1525443 : CollatzResearch.WordTrace tailWord_1525443 prefixEnd_1525443 783285470036580430947121 := by
  unfold tailWord_1525443
  simp only [CollatzResearch.WordTrace]
  refine ⟨55637477012588010768060983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37091651341725340512040655 55637477012588010768060983)
  ·
    refine ⟨83456215518882016152091475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55637477012588010768060983 83456215518882016152091475)
    ·
      refine ⟨125184323278323024228137213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83456215518882016152091475 125184323278323024228137213)
      ·
        refine ⟨46944121229371134085551455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125184323278323024228137213 46944121229371134085551455)
        ·
          refine ⟨70416181844056701128327183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46944121229371134085551455 70416181844056701128327183)
          ·
            refine ⟨105624272766085051692490775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70416181844056701128327183 105624272766085051692490775)
            ·
              refine ⟨158436409149127577538736163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105624272766085051692490775 158436409149127577538736163)
              ·
                refine ⟨237654613723691366308104245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158436409149127577538736163 237654613723691366308104245)
                ·
                  refine ⟨22280120036596065591384773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 237654613723691366308104245 22280120036596065591384773)
                  ·
                    refine ⟨4177522506861762298384645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22280120036596065591384773 4177522506861762298384645)
                    ·
                      refine ⟨783285470036580430947121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4177522506861762298384645 783285470036580430947121)
                      ·
                        rfl

theorem cell23_1525443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_1525443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525443 prefixEnd_1525443 := by exact prefixLift 1525443
  have htrace : WordTrace (prefixWord ++ tailWord_1525443) baseStart_1525443 baseEnd_1525443 := by
    simpa [prefixWord, tailWord_1525443, baseEnd_1525443] using wordTrace_append hprefix tailTrace_1525443
  have hstable : (prefixWord ++ tailWord_1525443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525443).length < 2 ^ (prefixWord ++ tailWord_1525443).sum := by decide
  have hdescent : baseEnd_1525443 < baseStart_1525443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525464 : List Nat := [2, 1, 2, 2, 3, 1, 1, 5, 2, 2, 2]
def baseStart_1525464 : Nat := 118140960795 + 1525464 * 2 ^ 59
def prefixEnd_1525464 : Nat := 4983230072969 + 3 ^ 40 * 1525464 * 2
def baseEnd_1525464 : Nat := 783296253130324848784525

theorem tailTrace_1525464 : CollatzResearch.WordTrace tailWord_1525464 prefixEnd_1525464 783296253130324848784525 := by
  unfold tailWord_1525464
  simp only [CollatzResearch.WordTrace]
  refine ⟨27819121472755965677287723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37092161963674620903050297 27819121472755965677287723)
  ·
    refine ⟨41728682209133948515931585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27819121472755965677287723 41728682209133948515931585)
    ·
      refine ⟨31296511656850461386948689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41728682209133948515931585 31296511656850461386948689)
      ·
        refine ⟨23472383742637846040211517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31296511656850461386948689 23472383742637846040211517)
        ·
          refine ⟨8802143903489192265079319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23472383742637846040211517 8802143903489192265079319)
          ·
            refine ⟨13203215855233788397618979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8802143903489192265079319 13203215855233788397618979)
            ·
              refine ⟨19804823782850682596428469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13203215855233788397618979 19804823782850682596428469)
              ·
                refine ⟨1856702229642251493415169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19804823782850682596428469 1856702229642251493415169)
                ·
                  refine ⟨1392526672231688620061377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1856702229642251493415169 1392526672231688620061377)
                  ·
                    refine ⟨1044395004173766465046033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1392526672231688620061377 1044395004173766465046033)
                    ·
                      refine ⟨783296253130324848784525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1044395004173766465046033 783296253130324848784525)
                      ·
                        rfl

theorem cell23_1525464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 2, 2, 2].length) (baseStart_1525464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525464 prefixEnd_1525464 := by exact prefixLift 1525464
  have htrace : WordTrace (prefixWord ++ tailWord_1525464) baseStart_1525464 baseEnd_1525464 := by
    simpa [prefixWord, tailWord_1525464, baseEnd_1525464] using wordTrace_append hprefix tailTrace_1525464
  have hstable : (prefixWord ++ tailWord_1525464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525464).length < 2 ^ (prefixWord ++ tailWord_1525464).sum := by decide
  have hdescent : baseEnd_1525464 < baseStart_1525464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525487 : List Nat := [1, 1, 2, 1, 5, 1, 4, 3, 5]
def baseStart_1525487 : Nat := 118140960795 + 1525487 * 2 ^ 59
def prefixEnd_1525487 : Nat := 4983230072969 + 3 ^ 40 * 1525487 * 2
def baseEnd_1525487 : Nat := 87034229242819806532991

theorem tailTrace_1525487 : CollatzResearch.WordTrace tailWord_1525487 prefixEnd_1525487 87034229242819806532991 := by
  unfold tailWord_1525487
  simp only [CollatzResearch.WordTrace]
  refine ⟨55639081824428606282662715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37092721216285737521775143 55639081824428606282662715)
  ·
    refine ⟨83458622736642909423994073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55639081824428606282662715 83458622736642909423994073)
    ·
      refine ⟨62593967052482182067995555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83458622736642909423994073 62593967052482182067995555)
      ·
        refine ⟨93890950578723273101993333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62593967052482182067995555 93890950578723273101993333)
        ·
          refine ⟨8802276616755306853311875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93890950578723273101993333 8802276616755306853311875)
          ·
            refine ⟨13203414925132960279967813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8802276616755306853311875 13203414925132960279967813)
            ·
              refine ⟨2475640298462430052493965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13203414925132960279967813 2475640298462430052493965)
              ·
                refine ⟨928365111923411269685237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2475640298462430052493965 928365111923411269685237)
                ·
                  refine ⟨87034229242819806532991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 928365111923411269685237 87034229242819806532991)
                  ·
                    rfl

theorem cell23_1525487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3, 5].length) (baseStart_1525487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525487 prefixEnd_1525487 := by exact prefixLift 1525487
  have htrace : WordTrace (prefixWord ++ tailWord_1525487) baseStart_1525487 baseEnd_1525487 := by
    simpa [prefixWord, tailWord_1525487, baseEnd_1525487] using wordTrace_append hprefix tailTrace_1525487
  have hstable : (prefixWord ++ tailWord_1525487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525487).length < 2 ^ (prefixWord ++ tailWord_1525487).sum := by decide
  have hdescent : baseEnd_1525487 < baseStart_1525487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525500 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 4, 5]
def baseStart_1525500 : Nat := 118140960795 + 1525500 * 2 ^ 59
def prefixEnd_1525500 : Nat := 4983230072969 + 3 ^ 40 * 1525500 * 2
def baseEnd_1525500 : Nat := 261104912811295569311453

theorem tailTrace_1525500 : CollatzResearch.WordTrace tailWord_1525500 prefixEnd_1525500 261104912811295569311453 := by
  unfold tailWord_1525500
  simp only [CollatzResearch.WordTrace]
  refine ⟨27819777986690754751442977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37093037315587673001923969 27819777986690754751442977)
  ·
    refine ⟨20864833490018066063582233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27819777986690754751442977 20864833490018066063582233)
    ·
      refine ⟨15648625117513549547686675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20864833490018066063582233 15648625117513549547686675)
      ·
        refine ⟨23472937676270324321530013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15648625117513549547686675 23472937676270324321530013)
        ·
          refine ⟨8802351628601371620573755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23472937676270324321530013 8802351628601371620573755)
          ·
            refine ⟨13203527442902057430860633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8802351628601371620573755 13203527442902057430860633)
            ·
              refine ⟨9902645582176543073145475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13203527442902057430860633 9902645582176543073145475)
              ·
                refine ⟨14853968373264814609718213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9902645582176543073145475 14853968373264814609718213)
                ·
                  refine ⟨2785119069987152739322165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14853968373264814609718213 2785119069987152739322165)
                  ·
                    refine ⟨261104912811295569311453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2785119069987152739322165 261104912811295569311453)
                    ·
                      rfl

theorem cell23_1525500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_1525500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525500 prefixEnd_1525500 := by exact prefixLift 1525500
  have htrace : WordTrace (prefixWord ++ tailWord_1525500) baseStart_1525500 baseEnd_1525500 := by
    simpa [prefixWord, tailWord_1525500, baseEnd_1525500] using wordTrace_append hprefix tailTrace_1525500
  have hstable : (prefixWord ++ tailWord_1525500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525500).length < 2 ^ (prefixWord ++ tailWord_1525500).sum := by decide
  have hdescent : baseEnd_1525500 < baseStart_1525500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525560 : List Nat := [2, 1, 2, 1, 3, 3, 2, 1, 8]
def baseStart_1525560 : Nat := 118140960795 + 1525560 * 2 ^ 59
def prefixEnd_1525560 : Nat := 4983230072969 + 3 ^ 40 * 1525560 * 2
def baseEnd_1525560 : Nat := 87038394141461830353787

theorem tailTrace_1525560 : CollatzResearch.WordTrace tailWord_1525560 prefixEnd_1525560 87038394141461830353787 := by
  unfold tailWord_1525560
  simp only [CollatzResearch.WordTrace]
  refine ⟨27820872176582069875035067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37094496235442759833380089 27820872176582069875035067)
  ·
    refine ⟨41731308264873104812552601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27820872176582069875035067 41731308264873104812552601)
    ·
      refine ⟨31298481198654828609414451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41731308264873104812552601 31298481198654828609414451)
      ·
        refine ⟨46947721797982242914121677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31298481198654828609414451 46947721797982242914121677)
        ·
          refine ⟨17605395674243341092795629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46947721797982242914121677 17605395674243341092795629)
          ·
            refine ⟨6602023377841252909798361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17605395674243341092795629 6602023377841252909798361)
            ·
              refine ⟨4951517533380939682348771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6602023377841252909798361 4951517533380939682348771)
              ·
                refine ⟨7427276300071409523523157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4951517533380939682348771 7427276300071409523523157)
                ·
                  refine ⟨87038394141461830353787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7427276300071409523523157 87038394141461830353787)
                  ·
                    rfl

theorem cell23_1525560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 8].length) (baseStart_1525560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525560 prefixEnd_1525560 := by exact prefixLift 1525560
  have htrace : WordTrace (prefixWord ++ tailWord_1525560) baseStart_1525560 baseEnd_1525560 := by
    simpa [prefixWord, tailWord_1525560, baseEnd_1525560] using wordTrace_append hprefix tailTrace_1525560
  have hstable : (prefixWord ++ tailWord_1525560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525560).length < 2 ^ (prefixWord ++ tailWord_1525560).sum := by decide
  have hdescent : baseEnd_1525560 < baseStart_1525560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525564 : List Nat := [2, 2, 2, 2, 1, 1, 2, 6, 1, 4]
def baseStart_1525564 : Nat := 118140960795 + 1525564 * 2 ^ 59
def prefixEnd_1525564 : Nat := 4983230072969 + 3 ^ 40 * 1525564 * 2
def baseEnd_1525564 : Nat := 261115867065258152511355

theorem tailTrace_1525564 : CollatzResearch.WordTrace tailWord_1525564 prefixEnd_1525564 261115867065258152511355 := by
  unfold tailWord_1525564
  simp only [CollatzResearch.WordTrace]
  refine ⟨27820945122574824216607873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37094593496766432288810497 27820945122574824216607873)
  ·
    refine ⟨20865708841931118162455905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27820945122574824216607873 20865708841931118162455905)
    ·
      refine ⟨15649281631448338621841929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20865708841931118162455905 15649281631448338621841929)
      ·
        refine ⟨11736961223586253966381447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15649281631448338621841929 11736961223586253966381447)
        ·
          refine ⟨17605441835379380949572171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11736961223586253966381447 17605441835379380949572171)
          ·
            refine ⟨26408162753069071424358257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17605441835379380949572171 26408162753069071424358257)
            ·
              refine ⟨19806122064801803568268693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26408162753069071424358257 19806122064801803568268693)
              ·
                refine ⟨928411971787584542262595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19806122064801803568268693 928411971787584542262595)
                ·
                  refine ⟨1392617957681376813393893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 928411971787584542262595 1392617957681376813393893)
                  ·
                    refine ⟨261115867065258152511355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1392617957681376813393893 261115867065258152511355)
                    ·
                      rfl

theorem cell23_1525564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_1525564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525564 prefixEnd_1525564 := by exact prefixLift 1525564
  have htrace : WordTrace (prefixWord ++ tailWord_1525564) baseStart_1525564 baseEnd_1525564 := by
    simpa [prefixWord, tailWord_1525564, baseEnd_1525564] using wordTrace_append hprefix tailTrace_1525564
  have hstable : (prefixWord ++ tailWord_1525564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525564).length < 2 ^ (prefixWord ++ tailWord_1525564).sum := by decide
  have hdescent : baseEnd_1525564 < baseStart_1525564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525627 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 2, 6, 2]
def baseStart_1525627 : Nat := 118140960795 + 1525627 * 2 ^ 59
def prefixEnd_1525627 : Nat := 4983230072969 + 3 ^ 40 * 1525627 * 2
def baseEnd_1525627 : Nat := 783379950477007711046275

theorem tailTrace_1525627 : CollatzResearch.WordTrace tailWord_1525627 prefixEnd_1525627 783379950477007711046275 := by
  unfold tailWord_1525627
  simp only [CollatzResearch.WordTrace]
  refine ⟨55644188043921410192759135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37096125362614273461839423 55644188043921410192759135)
  ·
    refine ⟨83466282065882115289138703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55644188043921410192759135 83466282065882115289138703)
    ·
      refine ⟨125199423098823172933708055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83466282065882115289138703 125199423098823172933708055)
      ·
        refine ⟨187799134648234759400562083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125199423098823172933708055 187799134648234759400562083)
        ·
          refine ⟨281698701972352139100843125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187799134648234759400562083 281698701972352139100843125)
          ·
            refine ⟨26409253309908013040704043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 281698701972352139100843125 26409253309908013040704043)
            ·
              refine ⟨39613879964862019561056065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26409253309908013040704043 39613879964862019561056065)
              ·
                refine ⟨29710409973646514670792049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39613879964862019561056065 29710409973646514670792049)
                ·
                  refine ⟨22282807480234886003094037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29710409973646514670792049 22282807480234886003094037)
                  ·
                    refine ⟨1044506600636010281395033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22282807480234886003094037 1044506600636010281395033)
                    ·
                      refine ⟨783379950477007711046275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1044506600636010281395033 783379950477007711046275)
                      ·
                        rfl

theorem cell23_1525627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 6, 2].length) (baseStart_1525627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525627 prefixEnd_1525627 := by exact prefixLift 1525627
  have htrace : WordTrace (prefixWord ++ tailWord_1525627) baseStart_1525627 baseEnd_1525627 := by
    simpa [prefixWord, tailWord_1525627, baseEnd_1525627] using wordTrace_append hprefix tailTrace_1525627
  have hstable : (prefixWord ++ tailWord_1525627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525627).length < 2 ^ (prefixWord ++ tailWord_1525627).sum := by decide
  have hdescent : baseEnd_1525627 < baseStart_1525627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525637 : List Nat := [1, 3, 1, 1, 3, 2, 4, 1, 1, 6]
def baseStart_1525637 : Nat := 118140960795 + 1525637 * 2 ^ 59
def prefixEnd_1525637 : Nat := 4983230072969 + 3 ^ 40 * 1525637 * 2
def baseEnd_1525637 : Nat := 261128361761184223973743

theorem tailTrace_1525637 : CollatzResearch.WordTrace tailWord_1525637 prefixEnd_1525637 261128361761184223973743 := by
  unfold tailWord_1525637
  simp only [CollatzResearch.WordTrace]
  refine ⟨55644552773885181900623165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37096368515923454600415443 55644552773885181900623165)
  ·
    refine ⟨20866707290206943212733687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55644552773885181900623165 20866707290206943212733687)
    ·
      refine ⟨31300060935310414819100531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20866707290206943212733687 31300060935310414819100531)
      ·
        refine ⟨46950091402965622228650797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31300060935310414819100531 46950091402965622228650797)
        ·
          refine ⟨17606284276112108335744049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46950091402965622228650797 17606284276112108335744049)
          ·
            refine ⟨13204713207084081251808037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17606284276112108335744049 13204713207084081251808037)
            ·
              refine ⟨2475883726328265234714007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13204713207084081251808037 2475883726328265234714007)
              ·
                refine ⟨3713825589492397852071011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2475883726328265234714007 3713825589492397852071011)
                ·
                  refine ⟨5570738384238596778106517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3713825589492397852071011 5570738384238596778106517)
                  ·
                    refine ⟨261128361761184223973743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5570738384238596778106517 261128361761184223973743)
                    ·
                      rfl

theorem cell23_1525637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 6].length) (baseStart_1525637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525637 prefixEnd_1525637 := by exact prefixLift 1525637
  have htrace : WordTrace (prefixWord ++ tailWord_1525637) baseStart_1525637 baseEnd_1525637 := by
    simpa [prefixWord, tailWord_1525637, baseEnd_1525637] using wordTrace_append hprefix tailTrace_1525637
  have hstable : (prefixWord ++ tailWord_1525637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525637).length < 2 ^ (prefixWord ++ tailWord_1525637).sum := by decide
  have hdescent : baseEnd_1525637 < baseStart_1525637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525657 : List Nat := [1, 2, 1, 2, 1, 3, 4, 2, 1, 2, 4]
def baseStart_1525657 : Nat := 118140960795 + 1525657 * 2 ^ 59
def prefixEnd_1525657 : Nat := 4983230072969 + 3 ^ 40 * 1525657 * 2
def baseEnd_1525657 : Nat := 783395354896642593671137

theorem tailTrace_1525657 : CollatzResearch.WordTrace tailWord_1525657 prefixEnd_1525657 783395354896642593671137 := by
  unfold tailWord_1525657
  simp only [CollatzResearch.WordTrace]
  refine ⟨55645282233812725316351225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37096854822541816877567483 55645282233812725316351225)
  ·
    refine ⟨41733961675359543987263419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55645282233812725316351225 41733961675359543987263419)
    ·
      refine ⟨62600942513039315980895129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41733961675359543987263419 62600942513039315980895129)
      ·
        refine ⟨46950706884779486985671347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62600942513039315980895129 46950706884779486985671347)
        ·
          refine ⟨70426060327169230478507021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46950706884779486985671347 70426060327169230478507021)
          ·
            refine ⟨26409772622688461429440133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70426060327169230478507021 26409772622688461429440133)
            ·
              refine ⟨4951832366754086518020025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26409772622688461429440133 4951832366754086518020025)
              ·
                refine ⟨3713874275065564888515019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4951832366754086518020025 3713874275065564888515019)
                ·
                  refine ⟨5570811412598347332772529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3713874275065564888515019 5570811412598347332772529)
                  ·
                    refine ⟨4178108559448760499579397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5570811412598347332772529 4178108559448760499579397)
                    ·
                      refine ⟨783395354896642593671137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4178108559448760499579397 783395354896642593671137)
                      ·
                        rfl

theorem cell23_1525657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_1525657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525657 prefixEnd_1525657 := by exact prefixLift 1525657
  have htrace : WordTrace (prefixWord ++ tailWord_1525657) baseStart_1525657 baseEnd_1525657 := by
    simpa [prefixWord, tailWord_1525657, baseEnd_1525657] using wordTrace_append hprefix tailTrace_1525657
  have hstable : (prefixWord ++ tailWord_1525657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525657).length < 2 ^ (prefixWord ++ tailWord_1525657).sum := by decide
  have hdescent : baseEnd_1525657 < baseStart_1525657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525661 : List Nat := [1, 4, 2, 1, 2, 2, 4, 1, 1, 1, 4]
def baseStart_1525661 : Nat := 118140960795 + 1525661 * 2 ^ 59
def prefixEnd_1525661 : Nat := 4983230072969 + 3 ^ 40 * 1525661 * 2
def baseEnd_1525661 : Nat := 783397408819260578021119

theorem tailTrace_1525661 : CollatzResearch.WordTrace tailWord_1525661 prefixEnd_1525661 783397408819260578021119 := by
  unfold tailWord_1525661
  simp only [CollatzResearch.WordTrace]
  refine ⟨55645428125798233999496837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37096952083865489332997891 55645428125798233999496837)
  ·
    refine ⟨10433517773587168874905657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55645428125798233999496837 10433517773587168874905657)
    ·
      refine ⟨7825138330190376656179243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10433517773587168874905657 7825138330190376656179243)
      ·
        refine ⟨11737707495285564984268865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7825138330190376656179243 11737707495285564984268865)
        ·
          refine ⟨8803280621464173738201649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11737707495285564984268865 8803280621464173738201649)
          ·
            refine ⟨6602460466098130303651237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8803280621464173738201649 6602460466098130303651237)
            ·
              refine ⟨1237961337393399431934607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6602460466098130303651237 1237961337393399431934607)
              ·
                refine ⟨1856942006090099147901911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1237961337393399431934607 1856942006090099147901911)
                ·
                  refine ⟨2785413009135148721852867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1856942006090099147901911 2785413009135148721852867)
                  ·
                    refine ⟨4178119513702723082779301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2785413009135148721852867 4178119513702723082779301)
                    ·
                      refine ⟨783397408819260578021119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4178119513702723082779301 783397408819260578021119)
                      ·
                        rfl

theorem cell23_1525661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_1525661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525661 prefixEnd_1525661 := by exact prefixLift 1525661
  have htrace : WordTrace (prefixWord ++ tailWord_1525661) baseStart_1525661 baseEnd_1525661 := by
    simpa [prefixWord, tailWord_1525661, baseEnd_1525661] using wordTrace_append hprefix tailTrace_1525661
  have hstable : (prefixWord ++ tailWord_1525661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525661).length < 2 ^ (prefixWord ++ tailWord_1525661).sum := by decide
  have hdescent : baseEnd_1525661 < baseStart_1525661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525671 : List Nat := [1, 1, 6, 1, 2, 1, 3, 2, 2, 4]
def baseStart_1525671 : Nat := 118140960795 + 1525671 * 2 ^ 59
def prefixEnd_1525671 : Nat := 4983230072969 + 3 ^ 40 * 1525671 * 2
def baseEnd_1525671 : Nat := 261134181208601846298691

theorem tailTrace_1525671 : CollatzResearch.WordTrace tailWord_1525671 prefixEnd_1525671 261134181208601846298691 := by
  unfold tailWord_1525671
  simp only [CollatzResearch.WordTrace]
  refine ⟨55645792855762005707360867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37097195237174670471573911 55645792855762005707360867)
  ·
    refine ⟨83468689283643008561041301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55645792855762005707360867 83468689283643008561041301)
    ·
      refine ⟨3912594810170766026298811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83468689283643008561041301 3912594810170766026298811)
      ·
        refine ⟨5868892215256149039448217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3912594810170766026298811 5868892215256149039448217)
        ·
          refine ⟨4401669161442111779586163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5868892215256149039448217 4401669161442111779586163)
          ·
            refine ⟨6602503742163167669379245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4401669161442111779586163 6602503742163167669379245)
            ·
              refine ⟨2475938903311187876017217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6602503742163167669379245 2475938903311187876017217)
              ·
                refine ⟨1856954177483390907012913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2475938903311187876017217 1856954177483390907012913)
                ·
                  refine ⟨1392715633112543180259685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1856954177483390907012913 1392715633112543180259685)
                  ·
                    refine ⟨261134181208601846298691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1392715633112543180259685 261134181208601846298691)
                    ·
                      rfl

theorem cell23_1525671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_1525671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525671 prefixEnd_1525671 := by exact prefixLift 1525671
  have htrace : WordTrace (prefixWord ++ tailWord_1525671) baseStart_1525671 baseEnd_1525671 := by
    simpa [prefixWord, tailWord_1525671, baseEnd_1525671] using wordTrace_append hprefix tailTrace_1525671
  have hstable : (prefixWord ++ tailWord_1525671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525671).length < 2 ^ (prefixWord ++ tailWord_1525671).sum := by decide
  have hdescent : baseEnd_1525671 < baseStart_1525671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525745 : List Nat := [1, 2, 2, 2, 5, 2, 2, 1, 2, 1, 3]
def baseStart_1525745 : Nat := 118140960795 + 1525745 * 2 ^ 59
def prefixEnd_1525745 : Nat := 4983230072969 + 3 ^ 40 * 1525745 * 2
def baseEnd_1525745 : Nat := 783440541194238249370733

theorem tailTrace_1525745 : CollatzResearch.WordTrace tailWord_1525745 prefixEnd_1525745 783440541194238249370733 := by
  unfold tailWord_1525745
  simp only [CollatzResearch.WordTrace]
  refine ⟨55648491857493916345554689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37098994571662610897036459 55648491857493916345554689)
  ·
    refine ⟨41736368893120437259166017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55648491857493916345554689 41736368893120437259166017)
    ·
      refine ⟨31302276669840327944374513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41736368893120437259166017 31302276669840327944374513)
      ·
        refine ⟨23476707502380245958280885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31302276669840327944374513 23476707502380245958280885)
        ·
          refine ⟨2200941328348148058588833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23476707502380245958280885 2200941328348148058588833)
          ·
            refine ⟨1650705996261111043941625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2200941328348148058588833 1650705996261111043941625)
            ·
              refine ⟨1238029497195833282956219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1650705996261111043941625 1238029497195833282956219)
              ·
                refine ⟨1857044245793749924434329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1238029497195833282956219 1857044245793749924434329)
                ·
                  refine ⟨1392783184345312443325747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1857044245793749924434329 1392783184345312443325747)
                  ·
                    refine ⟨2089174776517968664988621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1392783184345312443325747 2089174776517968664988621)
                    ·
                      refine ⟨783440541194238249370733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2089174776517968664988621 783440541194238249370733)
                      ·
                        rfl

theorem cell23_1525745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 2, 1, 3].length) (baseStart_1525745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525745 prefixEnd_1525745 := by exact prefixLift 1525745
  have htrace : WordTrace (prefixWord ++ tailWord_1525745) baseStart_1525745 baseEnd_1525745 := by
    simpa [prefixWord, tailWord_1525745, baseEnd_1525745] using wordTrace_append hprefix tailTrace_1525745
  have hstable : (prefixWord ++ tailWord_1525745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525745).length < 2 ^ (prefixWord ++ tailWord_1525745).sum := by decide
  have hdescent : baseEnd_1525745 < baseStart_1525745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525747 : List Nat := [1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 4]
def baseStart_1525747 : Nat := 118140960795 + 1525747 * 2 ^ 59
def prefixEnd_1525747 : Nat := 4983230072969 + 3 ^ 40 * 1525747 * 2
def baseEnd_1525747 : Nat := 783441568155547241545723

theorem tailTrace_1525747 : CollatzResearch.WordTrace tailWord_1525747 prefixEnd_1525747 783441568155547241545723 := by
  unfold tailWord_1525747
  simp only [CollatzResearch.WordTrace]
  refine ⟨55648564803486670687127495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37099043202324447124751663 55648564803486670687127495)
  ·
    refine ⟨83472847205230006030691243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55648564803486670687127495 83472847205230006030691243)
    ·
      refine ⟨125209270807845009046036865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83472847205230006030691243 125209270807845009046036865)
      ·
        refine ⟨93906953105883756784527649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125209270807845009046036865 93906953105883756784527649)
        ·
          refine ⟨70430214829412817588395737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93906953105883756784527649 70430214829412817588395737)
          ·
            refine ⟨52822661122059613191296803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70430214829412817588395737 52822661122059613191296803)
            ·
              refine ⟨79233991683089419786945205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52822661122059613191296803 79233991683089419786945205)
              ·
                refine ⟨7428186720289633105026113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79233991683089419786945205 7428186720289633105026113)
                ·
                  refine ⟨5571140040217224828769585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7428186720289633105026113 5571140040217224828769585)
                  ·
                    refine ⟨4178355030162918621577189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5571140040217224828769585 4178355030162918621577189)
                    ·
                      refine ⟨783441568155547241545723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4178355030162918621577189 783441568155547241545723)
                      ·
                        rfl

theorem cell23_1525747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 4].length) (baseStart_1525747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525747 prefixEnd_1525747 := by exact prefixLift 1525747
  have htrace : WordTrace (prefixWord ++ tailWord_1525747) baseStart_1525747 baseEnd_1525747 := by
    simpa [prefixWord, tailWord_1525747, baseEnd_1525747] using wordTrace_append hprefix tailTrace_1525747
  have hstable : (prefixWord ++ tailWord_1525747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525747).length < 2 ^ (prefixWord ++ tailWord_1525747).sum := by decide
  have hdescent : baseEnd_1525747 < baseStart_1525747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525757 : List Nat := [1, 4, 1, 1, 1, 2, 2, 4, 7]
def baseStart_1525757 : Nat := 118140960795 + 1525757 * 2 ^ 59
def prefixEnd_1525757 : Nat := 4983230072969 + 3 ^ 40 * 1525757 * 2
def baseEnd_1525757 : Nat := 87049633662454689157853

theorem tailTrace_1525757 : CollatzResearch.WordTrace tailWord_1525757 prefixEnd_1525757 87049633662454689157853 := by
  unfold tailWord_1525757
  simp only [CollatzResearch.WordTrace]
  refine ⟨55648929533450442394991525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37099286355633628263327683 55648929533450442394991525)
  ·
    refine ⟨10434174287521957949060911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55648929533450442394991525 10434174287521957949060911)
    ·
      refine ⟨15651261431282936923591367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10434174287521957949060911 15651261431282936923591367)
      ·
        refine ⟨23476892146924405385387051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15651261431282936923591367 23476892146924405385387051)
        ·
          refine ⟨35215338220386608078080577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23476892146924405385387051 35215338220386608078080577)
          ·
            refine ⟨26411503665289956058560433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35215338220386608078080577 26411503665289956058560433)
            ·
              refine ⟨19808627748967467043920325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26411503665289956058560433 19808627748967467043920325)
              ·
                refine ⟨3714117702931400070735061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19808627748967467043920325 3714117702931400070735061)
                ·
                  refine ⟨87049633662454689157853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3714117702931400070735061 87049633662454689157853)
                  ·
                    rfl

theorem cell23_1525757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 7].length) (baseStart_1525757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525757 prefixEnd_1525757 := by exact prefixLift 1525757
  have htrace : WordTrace (prefixWord ++ tailWord_1525757) baseStart_1525757 baseEnd_1525757 := by
    simpa [prefixWord, tailWord_1525757, baseEnd_1525757] using wordTrace_append hprefix tailTrace_1525757
  have hstable : (prefixWord ++ tailWord_1525757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525757).length < 2 ^ (prefixWord ++ tailWord_1525757).sum := by decide
  have hdescent : baseEnd_1525757 < baseStart_1525757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525784 : List Nat := [2, 1, 2, 3, 2, 1, 2, 2, 2, 3, 3]
def baseStart_1525784 : Nat := 118140960795 + 1525784 * 2 ^ 59
def prefixEnd_1525784 : Nat := 4983230072969 + 3 ^ 40 * 1525784 * 2
def baseEnd_1525784 : Nat := 783460566939763596783053

theorem tailTrace_1525784 : CollatzResearch.WordTrace tailWord_1525784 prefixEnd_1525784 783460566939763596783053 := by
  unfold tailWord_1525784
  simp only [CollatzResearch.WordTrace]
  refine ⟨27824957152176313003112203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37099942869568417337482937 27824957152176313003112203)
  ·
    refine ⟨41737435728264469504668305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27824957152176313003112203 41737435728264469504668305)
    ·
      refine ⟨31303076796198352128501229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41737435728264469504668305 31303076796198352128501229)
      ·
        refine ⟨11738653798574382048187961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31303076796198352128501229 11738653798574382048187961)
        ·
          refine ⟨8803990348930786536140971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11738653798574382048187961 8803990348930786536140971)
          ·
            refine ⟨13205985523396179804211457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8803990348930786536140971 13205985523396179804211457)
            ·
              refine ⟨9904489142547134853158593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13205985523396179804211457 9904489142547134853158593)
              ·
                refine ⟨7428366856910351139868945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9904489142547134853158593 7428366856910351139868945)
                ·
                  refine ⟨5571275142682763354901709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7428366856910351139868945 5571275142682763354901709)
                  ·
                    refine ⟨2089228178506036258088141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5571275142682763354901709 2089228178506036258088141)
                    ·
                      refine ⟨783460566939763596783053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2089228178506036258088141 783460566939763596783053)
                      ·
                        rfl

theorem cell23_1525784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_1525784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525784 prefixEnd_1525784 := by exact prefixLift 1525784
  have htrace : WordTrace (prefixWord ++ tailWord_1525784) baseStart_1525784 baseEnd_1525784 := by
    simpa [prefixWord, tailWord_1525784, baseEnd_1525784] using wordTrace_append hprefix tailTrace_1525784
  have hstable : (prefixWord ++ tailWord_1525784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525784).length < 2 ^ (prefixWord ++ tailWord_1525784).sum := by decide
  have hdescent : baseEnd_1525784 < baseStart_1525784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525787 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 4, 5]
def baseStart_1525787 : Nat := 118140960795 + 1525787 * 2 ^ 59
def prefixEnd_1525787 : Nat := 4983230072969 + 3 ^ 40 * 1525787 * 2
def baseEnd_1525787 : Nat := 261154035793909028348513

theorem tailTrace_1525787 : CollatzResearch.WordTrace tailWord_1525787 prefixEnd_1525787 261154035793909028348513 := by
  unfold tailWord_1525787
  simp only [CollatzResearch.WordTrace]
  refine ⟨55650023723341757518583615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37100015815561171679055743 55650023723341757518583615)
  ·
    refine ⟨83475035585012636277875423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55650023723341757518583615 83475035585012636277875423)
    ·
      refine ⟨125212553377518954416813135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83475035585012636277875423 125212553377518954416813135)
      ·
        refine ⟨187818830066278431625219703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125212553377518954416813135 187818830066278431625219703)
        ·
          refine ⟨281728245099417647437829555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187818830066278431625219703 281728245099417647437829555)
          ·
            refine ⟨422592367649126471156744333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281728245099417647437829555 422592367649126471156744333)
            ·
              refine ⟨158472137868422426683779125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 422592367649126471156744333 158472137868422426683779125)
              ·
                refine ⟨14856762925164602501604293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 158472137868422426683779125 14856762925164602501604293)
                ·
                  refine ⟨2785643048468362969050805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14856762925164602501604293 2785643048468362969050805)
                  ·
                    refine ⟨261154035793909028348513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2785643048468362969050805 261154035793909028348513)
                    ·
                      rfl

theorem cell23_1525787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 5].length) (baseStart_1525787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525787 prefixEnd_1525787 := by exact prefixLift 1525787
  have htrace : WordTrace (prefixWord ++ tailWord_1525787) baseStart_1525787 baseEnd_1525787 := by
    simpa [prefixWord, tailWord_1525787, baseEnd_1525787] using wordTrace_append hprefix tailTrace_1525787
  have hstable : (prefixWord ++ tailWord_1525787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525787).length < 2 ^ (prefixWord ++ tailWord_1525787).sum := by decide
  have hdescent : baseEnd_1525787 < baseStart_1525787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525824 : List Nat := [2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 4]
def baseStart_1525824 : Nat := 118140960795 + 1525824 * 2 ^ 59
def prefixEnd_1525824 : Nat := 4983230072969 + 3 ^ 40 * 1525824 * 2
def baseEnd_1525824 : Nat := 783481106165943440282869

theorem tailTrace_1525824 : CollatzResearch.WordTrace tailWord_1525824 prefixEnd_1525824 783481106165943440282869 := by
  unfold tailWord_1525824
  simp only [CollatzResearch.WordTrace]
  refine ⟨27825686612103856418840263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37100915482805141891787017 27825686612103856418840263)
  ·
    refine ⟨41738529918155784628260395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27825686612103856418840263 41738529918155784628260395)
    ·
      refine ⟨62607794877233676942390593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41738529918155784628260395 62607794877233676942390593)
      ·
        refine ⟨46955846157925257706792945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62607794877233676942390593 46955846157925257706792945)
        ·
          refine ⟨35216884618443943280094709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46955846157925257706792945 35216884618443943280094709)
          ·
            refine ⟨3301582932979119682508879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35216884618443943280094709 3301582932979119682508879)
            ·
              refine ⟨4952374399468679523763319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3301582932979119682508879 4952374399468679523763319)
              ·
                refine ⟨7428561599203019285644979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4952374399468679523763319 7428561599203019285644979)
                ·
                  refine ⟨11142842398804528928467469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7428561599203019285644979 11142842398804528928467469)
                  ·
                    refine ⟨4178565899551698348175301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11142842398804528928467469 4178565899551698348175301)
                    ·
                      refine ⟨783481106165943440282869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4178565899551698348175301 783481106165943440282869)
                      ·
                        rfl

theorem cell23_1525824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_1525824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525824 prefixEnd_1525824 := by exact prefixLift 1525824
  have htrace : WordTrace (prefixWord ++ tailWord_1525824) baseStart_1525824 baseEnd_1525824 := by
    simpa [prefixWord, tailWord_1525824, baseEnd_1525824] using wordTrace_append hprefix tailTrace_1525824
  have hstable : (prefixWord ++ tailWord_1525824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525824).length < 2 ^ (prefixWord ++ tailWord_1525824).sum := by decide
  have hdescent : baseEnd_1525824 < baseStart_1525824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525827 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 5]
def baseStart_1525827 : Nat := 118140960795 + 1525827 * 2 ^ 59
def prefixEnd_1525827 : Nat := 4983230072969 + 3 ^ 40 * 1525827 * 2
def baseEnd_1525827 : Nat := 783482646607906928545355

theorem tailTrace_1525827 : CollatzResearch.WordTrace tailWord_1525827 prefixEnd_1525827 783482646607906928545355 := by
  unfold tailWord_1525827
  simp only [CollatzResearch.WordTrace]
  refine ⟨55651482643196844350039735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37100988428797896233359823 55651482643196844350039735)
  ·
    refine ⟨83477223964795266525059603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55651482643196844350039735 83477223964795266525059603)
    ·
      refine ⟨125215835947192899787589405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83477223964795266525059603 125215835947192899787589405)
      ·
        refine ⟨46955938480197337420346027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125215835947192899787589405 46955938480197337420346027)
        ·
          refine ⟨70433907720296006130519041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46955938480197337420346027 70433907720296006130519041)
          ·
            refine ⟨52825430790222004597889281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70433907720296006130519041 52825430790222004597889281)
            ·
              refine ⟨39619073092666503448416961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52825430790222004597889281 39619073092666503448416961)
              ·
                refine ⟨29714304819499877586312721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39619073092666503448416961 29714304819499877586312721)
                ·
                  refine ⟨22285728614624908189734541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29714304819499877586312721 22285728614624908189734541)
                  ·
                    refine ⟨8357148230484340571150453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22285728614624908189734541 8357148230484340571150453)
                    ·
                      refine ⟨783482646607906928545355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8357148230484340571150453 783482646607906928545355)
                      ·
                        rfl

theorem cell23_1525827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_1525827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525827 prefixEnd_1525827 := by exact prefixLift 1525827
  have htrace : WordTrace (prefixWord ++ tailWord_1525827) baseStart_1525827 baseEnd_1525827 := by
    simpa [prefixWord, tailWord_1525827, baseEnd_1525827] using wordTrace_append hprefix tailTrace_1525827
  have hstable : (prefixWord ++ tailWord_1525827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525827).length < 2 ^ (prefixWord ++ tailWord_1525827).sum := by decide
  have hdescent : baseEnd_1525827 < baseStart_1525827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525834 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 7, 4]
def baseStart_1525834 : Nat := 118140960795 + 1525834 * 2 ^ 59
def prefixEnd_1525834 : Nat := 4983230072969 + 3 ^ 40 * 1525834 * 2
def baseEnd_1525834 : Nat := 261162080324162800385941

theorem tailTrace_1525834 : CollatzResearch.WordTrace tailWord_1525834 prefixEnd_1525834 261162080324162800385941 := by
  unfold tailWord_1525834
  simp only [CollatzResearch.WordTrace]
  refine ⟨13912934488542871136386139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37101158636114323030363037 13912934488542871136386139)
  ·
    refine ⟨20869401732814306704579209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13912934488542871136386139 20869401732814306704579209)
    ·
      refine ⟨15652051299610730028434407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20869401732814306704579209 15652051299610730028434407)
      ·
        refine ⟨23478076949416095042651611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15652051299610730028434407 23478076949416095042651611)
        ·
          refine ⟨35217115424124142563977417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23478076949416095042651611 35217115424124142563977417)
          ·
            refine ⟨26412836568093106922983063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35217115424124142563977417 26412836568093106922983063)
            ·
              refine ⟨39619254852139660384474595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26412836568093106922983063 39619254852139660384474595)
              ·
                refine ⟨59428882278209490576711893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39619254852139660384474595 59428882278209490576711893)
                ·
                  refine ⟨1392864428395534935391685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 59428882278209490576711893 1392864428395534935391685)
                  ·
                    refine ⟨261162080324162800385941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1392864428395534935391685 261162080324162800385941)
                    ·
                      rfl

theorem cell23_1525834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_1525834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525834 prefixEnd_1525834 := by exact prefixLift 1525834
  have htrace : WordTrace (prefixWord ++ tailWord_1525834) baseStart_1525834 baseEnd_1525834 := by
    simpa [prefixWord, tailWord_1525834, baseEnd_1525834] using wordTrace_append hprefix tailTrace_1525834
  have hstable : (prefixWord ++ tailWord_1525834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525834).length < 2 ^ (prefixWord ++ tailWord_1525834).sum := by decide
  have hdescent : baseEnd_1525834 < baseStart_1525834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525885 : List Nat := [1, 4, 1, 1, 3, 4, 1, 3, 1, 4]
def baseStart_1525885 : Nat := 118140960795 + 1525885 * 2 ^ 59
def prefixEnd_1525885 : Nat := 4983230072969 + 3 ^ 40 * 1525885 * 2
def baseEnd_1525885 : Nat := 261170809495289233873363

theorem tailTrace_1525885 : CollatzResearch.WordTrace tailWord_1525885 prefixEnd_1525885 261170809495289233873363 := by
  unfold tailWord_1525885
  simp only [CollatzResearch.WordTrace]
  refine ⟨55653598076986720255651109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37102398717991146837100739 55653598076986720255651109)
  ·
    refine ⟨10435049639435010047934583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55653598076986720255651109 10435049639435010047934583)
    ·
      refine ⟨15652574459152515071901875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10435049639435010047934583 15652574459152515071901875)
      ·
        refine ⟨23478861688728772607852813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15652574459152515071901875 23478861688728772607852813)
        ·
          refine ⟨8804573133273289727944805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23478861688728772607852813 8804573133273289727944805)
          ·
            refine ⟨1650857462488741823989651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8804573133273289727944805 1650857462488741823989651)
            ·
              refine ⟨2476286193733112735984477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1650857462488741823989651 2476286193733112735984477)
              ·
                refine ⟨928607322649917275994179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2476286193733112735984477 928607322649917275994179)
                ·
                  refine ⟨1392910983974875913991269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 928607322649917275994179 1392910983974875913991269)
                  ·
                    refine ⟨261170809495289233873363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1392910983974875913991269 261170809495289233873363)
                    ·
                      rfl

theorem cell23_1525885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_1525885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525885 prefixEnd_1525885 := by exact prefixLift 1525885
  have htrace : WordTrace (prefixWord ++ tailWord_1525885) baseStart_1525885 baseEnd_1525885 := by
    simpa [prefixWord, tailWord_1525885, baseEnd_1525885] using wordTrace_append hprefix tailTrace_1525885
  have hstable : (prefixWord ++ tailWord_1525885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525885).length < 2 ^ (prefixWord ++ tailWord_1525885).sum := by decide
  have hdescent : baseEnd_1525885 < baseStart_1525885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525902 : List Nat := [4, 1, 1, 3, 3, 1, 3, 2, 1, 4]
def baseStart_1525902 : Nat := 118140960795 + 1525902 * 2 ^ 59
def prefixEnd_1525902 : Nat := 4983230072969 + 3 ^ 40 * 1525902 * 2
def baseEnd_1525902 : Nat := 261173719218998045035837

theorem tailTrace_1525902 : CollatzResearch.WordTrace tailWord_1525902 prefixEnd_1525902 261173719218998045035837 := by
  unfold tailWord_1525902
  simp only [CollatzResearch.WordTrace]
  refine ⟨6956777264740641519877495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37102812078616754772679973 6956777264740641519877495)
  ·
    refine ⟨10435165897110962279816243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6956777264740641519877495 10435165897110962279816243)
    ·
      refine ⟨15652748845666443419724365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10435165897110962279816243 15652748845666443419724365)
      ·
        refine ⟨5869780817124916282396637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15652748845666443419724365 5869780817124916282396637)
        ·
          refine ⟨2201167806421843605898739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5869780817124916282396637 2201167806421843605898739)
          ·
            refine ⟨3301751709632765408848109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2201167806421843605898739 3301751709632765408848109)
            ·
              refine ⟨1238156891112287028318041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3301751709632765408848109 1238156891112287028318041)
              ·
                refine ⟨928617668334215271238531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1238156891112287028318041 928617668334215271238531)
                ·
                  refine ⟨1392926502501322906857797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 928617668334215271238531 1392926502501322906857797)
                  ·
                    refine ⟨261173719218998045035837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1392926502501322906857797 261173719218998045035837)
                    ·
                      rfl

theorem cell23_1525902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_1525902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525902 prefixEnd_1525902 := by exact prefixLift 1525902
  have htrace : WordTrace (prefixWord ++ tailWord_1525902) baseStart_1525902 baseEnd_1525902 := by
    simpa [prefixWord, tailWord_1525902, baseEnd_1525902] using wordTrace_append hprefix tailTrace_1525902
  have hstable : (prefixWord ++ tailWord_1525902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525902).length < 2 ^ (prefixWord ++ tailWord_1525902).sum := by decide
  have hdescent : baseEnd_1525902 < baseStart_1525902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525984 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 2, 7]
def baseStart_1525984 : Nat := 118140960795 + 1525984 * 2 ^ 59
def prefixEnd_1525984 : Nat := 4983230072969 + 3 ^ 40 * 1525984 * 2
def baseEnd_1525984 : Nat := 261187754356887604760711

theorem tailTrace_1525984 : CollatzResearch.WordTrace tailWord_1525984 prefixEnd_1525984 261187754356887604760711 := by
  unfold tailWord_1525984
  simp only [CollatzResearch.WordTrace]
  refine ⟨27828604451814030081752503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37104805935752040109003337 27828604451814030081752503)
  ·
    refine ⟨41742906677721045122628755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27828604451814030081752503 41742906677721045122628755)
    ·
      refine ⟨62614360016581567683943133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41742906677721045122628755 62614360016581567683943133)
      ·
        refine ⟨23480385006218087881478675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62614360016581567683943133 23480385006218087881478675)
        ·
          refine ⟨35220577509327131822218013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23480385006218087881478675 35220577509327131822218013)
          ·
            refine ⟨13207716565997674433331755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35220577509327131822218013 13207716565997674433331755)
            ·
              refine ⟨19811574848996511649997633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13207716565997674433331755 19811574848996511649997633)
              ·
                refine ⟨14858681136747383737498225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19811574848996511649997633 14858681136747383737498225)
                ·
                  refine ⟨11144010852560537803123669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14858681136747383737498225 11144010852560537803123669)
                  ·
                    refine ⟨261187754356887604760711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11144010852560537803123669 261187754356887604760711)
                    ·
                      rfl

theorem cell23_1525984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 2, 7].length) (baseStart_1525984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525984 prefixEnd_1525984 := by exact prefixLift 1525984
  have htrace : WordTrace (prefixWord ++ tailWord_1525984) baseStart_1525984 baseEnd_1525984 := by
    simpa [prefixWord, tailWord_1525984, baseEnd_1525984] using wordTrace_append hprefix tailTrace_1525984
  have hstable : (prefixWord ++ tailWord_1525984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525984).length < 2 ^ (prefixWord ++ tailWord_1525984).sum := by decide
  have hdescent : baseEnd_1525984 < baseStart_1525984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525986 : List Nat := [3, 3, 4, 1, 1, 2, 1, 1, 2, 3, 2]
def baseStart_1525986 : Nat := 118140960795 + 1525986 * 2 ^ 59
def prefixEnd_1525986 : Nat := 4983230072969 + 3 ^ 40 * 1525986 * 2
def baseEnd_1525986 : Nat := 783564290031971806457125

theorem tailTrace_1525986 : CollatzResearch.WordTrace tailWord_1525986 prefixEnd_1525986 783564290031971806457125 := by
  unfold tailWord_1525986
  simp only [CollatzResearch.WordTrace]
  refine ⟨13914320462405203626269453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37104854566413876336718541 13914320462405203626269453)
  ·
    refine ⟨5217870173401951359851045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13914320462405203626269453 5217870173401951359851045)
    ·
      refine ⟨978350657512865879972071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5217870173401951359851045 978350657512865879972071)
      ·
        refine ⟨1467525986269298819958107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 978350657512865879972071 1467525986269298819958107)
        ·
          refine ⟨2201288979403948229937161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1467525986269298819958107 2201288979403948229937161)
          ·
            refine ⟨1650966734552961172452871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2201288979403948229937161 1650966734552961172452871)
            ·
              refine ⟨2476450101829441758679307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1650966734552961172452871 2476450101829441758679307)
              ·
                refine ⟨3714675152744162638018961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2476450101829441758679307 3714675152744162638018961)
                ·
                  refine ⟨2786006364558121978514221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3714675152744162638018961 2786006364558121978514221)
                  ·
                    refine ⟨1044752386709295741942833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2786006364558121978514221 1044752386709295741942833)
                    ·
                      refine ⟨783564290031971806457125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1044752386709295741942833 783564290031971806457125)
                      ·
                        rfl

theorem cell23_1525986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_1525986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525986 prefixEnd_1525986 := by exact prefixLift 1525986
  have htrace : WordTrace (prefixWord ++ tailWord_1525986) baseStart_1525986 baseEnd_1525986 := by
    simpa [prefixWord, tailWord_1525986, baseEnd_1525986] using wordTrace_append hprefix tailTrace_1525986
  have hstable : (prefixWord ++ tailWord_1525986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525986).length < 2 ^ (prefixWord ++ tailWord_1525986).sum := by decide
  have hdescent : baseEnd_1525986 < baseStart_1525986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525998 : List Nat := [4, 1, 2, 1, 1, 1, 1, 4, 4, 1, 3]
def baseStart_1525998 : Nat := 118140960795 + 1525998 * 2 ^ 59
def prefixEnd_1525998 : Nat := 4983230072969 + 3 ^ 40 * 1525998 * 2
def baseEnd_1525998 : Nat := 783570451799825759507069

theorem tailTrace_1525998 : CollatzResearch.WordTrace tailWord_1525998 prefixEnd_1525998 783570451799825759507069 := by
  unfold tailWord_1525998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6957214940697167569314331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37105146350384893703009765 6957214940697167569314331)
  ·
    refine ⟨10435822411045751353971497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6957214940697167569314331 10435822411045751353971497)
    ·
      refine ⟨7826866808284313515478623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10435822411045751353971497 7826866808284313515478623)
      ·
        refine ⟨11740300212426470273217935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7826866808284313515478623 11740300212426470273217935)
        ·
          refine ⟨17610450318639705409826903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11740300212426470273217935 17610450318639705409826903)
          ·
            refine ⟨26415675477959558114740355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17610450318639705409826903 26415675477959558114740355)
            ·
              refine ⟨39623513216939337172110533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26415675477959558114740355 39623513216939337172110533)
              ·
                refine ⟨7429408728176125719770725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39623513216939337172110533 7429408728176125719770725)
                ·
                  refine ⟨1393014136533023572457011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7429408728176125719770725 1393014136533023572457011)
                  ·
                    refine ⟨2089521204799535358685517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1393014136533023572457011 2089521204799535358685517)
                    ·
                      refine ⟨783570451799825759507069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2089521204799535358685517 783570451799825759507069)
                      ·
                        rfl

theorem cell23_1525998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_1525998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1525998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1525998 prefixEnd_1525998 := by exact prefixLift 1525998
  have htrace : WordTrace (prefixWord ++ tailWord_1525998) baseStart_1525998 baseEnd_1525998 := by
    simpa [prefixWord, tailWord_1525998, baseEnd_1525998] using wordTrace_append hprefix tailTrace_1525998
  have hstable : (prefixWord ++ tailWord_1525998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525998).length < 2 ^ (prefixWord ++ tailWord_1525998).sum := by decide
  have hdescent : baseEnd_1525998 < baseStart_1525998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526002 : List Nat := [3, 2, 1, 3, 2, 3, 2, 1, 1, 2, 3]
def baseStart_1526002 : Nat := 118140960795 + 1526002 * 2 ^ 59
def prefixEnd_1526002 : Nat := 4983230072969 + 3 ^ 40 * 1526002 * 2
def baseEnd_1526002 : Nat := 783572505722443743857051

theorem tailTrace_1526002 : CollatzResearch.WordTrace tailWord_1526002 prefixEnd_1526002 783572505722443743857051 := by
  unfold tailWord_1526002
  simp only [CollatzResearch.WordTrace]
  refine ⟨13914466354390712309415065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37105243611708566158440173 13914466354390712309415065)
  ·
    refine ⟨10435849765793034232061299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13914466354390712309415065 10435849765793034232061299)
    ·
      refine ⟨15653774648689551348091949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10435849765793034232061299 15653774648689551348091949)
      ·
        refine ⟨5870165493258581755534481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15653774648689551348091949 5870165493258581755534481)
        ·
          refine ⟨4402624119943936316650861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5870165493258581755534481 4402624119943936316650861)
          ·
            refine ⟨1650984044978976118744073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4402624119943936316650861 1650984044978976118744073)
            ·
              refine ⟨1238238033734232089058055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1650984044978976118744073 1238238033734232089058055)
              ·
                refine ⟨1857357050601348133587083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1238238033734232089058055 1857357050601348133587083)
                ·
                  refine ⟨2786035575902022200380625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1857357050601348133587083 2786035575902022200380625)
                  ·
                    refine ⟨2089526681926516650285469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2786035575902022200380625 2089526681926516650285469)
                    ·
                      refine ⟨783572505722443743857051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2089526681926516650285469 783572505722443743857051)
                      ·
                        rfl

theorem cell23_1526002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_1526002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526002 prefixEnd_1526002 := by exact prefixLift 1526002
  have htrace : WordTrace (prefixWord ++ tailWord_1526002) baseStart_1526002 baseEnd_1526002 := by
    simpa [prefixWord, tailWord_1526002, baseEnd_1526002] using wordTrace_append hprefix tailTrace_1526002
  have hstable : (prefixWord ++ tailWord_1526002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526002).length < 2 ^ (prefixWord ++ tailWord_1526002).sum := by decide
  have hdescent : baseEnd_1526002 < baseStart_1526002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526042 : List Nat := [3, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2]
def baseStart_1526042 : Nat := 118140960795 + 1526042 * 2 ^ 59
def prefixEnd_1526042 : Nat := 4983230072969 + 3 ^ 40 * 1526042 * 2
def baseEnd_1526042 : Nat := 783593044948623587356867

theorem tailTrace_1526042 : CollatzResearch.WordTrace tailWord_1526042 prefixEnd_1526042 783593044948623587356867 := by
  unfold tailWord_1526042
  simp only [CollatzResearch.WordTrace]
  refine ⟨13914831084354484017279095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37106216224945290712744253 13914831084354484017279095)
  ·
    refine ⟨20872246626531726025918643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13914831084354484017279095 20872246626531726025918643)
    ·
      refine ⟨31308369939797589038877965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20872246626531726025918643 31308369939797589038877965)
      ·
        refine ⟨11740638727424095889579237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31308369939797589038877965 11740638727424095889579237)
        ·
          refine ⟨2201369761392017979296107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11740638727424095889579237 2201369761392017979296107)
          ·
            refine ⟨3302054642088026968944161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2201369761392017979296107 3302054642088026968944161)
            ·
              refine ⟨2476540981566020226708121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3302054642088026968944161 2476540981566020226708121)
              ·
                refine ⟨1857405736174515170031091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2476540981566020226708121 1857405736174515170031091)
                ·
                  refine ⟨2786108604261772755046637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1857405736174515170031091 2786108604261772755046637)
                  ·
                    refine ⟨1044790726598164783142489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2786108604261772755046637 1044790726598164783142489)
                    ·
                      refine ⟨783593044948623587356867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1044790726598164783142489 783593044948623587356867)
                      ·
                        rfl

theorem cell23_1526042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_1526042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526042 prefixEnd_1526042 := by exact prefixLift 1526042
  have htrace : WordTrace (prefixWord ++ tailWord_1526042) baseStart_1526042 baseEnd_1526042 := by
    simpa [prefixWord, tailWord_1526042, baseEnd_1526042] using wordTrace_append hprefix tailTrace_1526042
  have hstable : (prefixWord ++ tailWord_1526042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526042).length < 2 ^ (prefixWord ++ tailWord_1526042).sum := by decide
  have hdescent : baseEnd_1526042 < baseStart_1526042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526071 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 4, 3, 3]
def baseStart_1526071 : Nat := 118140960795 + 1526071 * 2 ^ 59
def prefixEnd_1526071 : Nat := 4983230072969 + 3 ^ 40 * 1526071 * 2
def baseEnd_1526071 : Nat := 783607935887603973894233

theorem tailTrace_1526071 : CollatzResearch.WordTrace tailWord_1526071 prefixEnd_1526071 783607935887603973894233 := by
  unfold tailWord_1526071
  simp only [CollatzResearch.WordTrace]
  refine ⟨55660382054312874021922067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37106921369541916014614711 55660382054312874021922067)
  ·
    refine ⟨83490573081469311032883101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55660382054312874021922067 83490573081469311032883101)
    ·
      refine ⟨31308964905550991637331163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83490573081469311032883101 31308964905550991637331163)
      ·
        refine ⟨46963447358326487455996745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31308964905550991637331163 46963447358326487455996745)
        ·
          refine ⟨35222585518744865591997559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46963447358326487455996745 35222585518744865591997559)
          ·
            refine ⟨52833878278117298387996339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35222585518744865591997559 52833878278117298387996339)
            ·
              refine ⟨79250817417175947581994509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52833878278117298387996339 79250817417175947581994509)
              ·
                refine ⟨29719056531440980343247941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79250817417175947581994509 29719056531440980343247941)
                ·
                  refine ⟨5572323099645183814358989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29719056531440980343247941 5572323099645183814358989)
                  ·
                    refine ⟨2089621162366943930384621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5572323099645183814358989 2089621162366943930384621)
                    ·
                      refine ⟨783607935887603973894233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2089621162366943930384621 783607935887603973894233)
                      ·
                        rfl

theorem cell23_1526071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3, 3].length) (baseStart_1526071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526071 prefixEnd_1526071 := by exact prefixLift 1526071
  have htrace : WordTrace (prefixWord ++ tailWord_1526071) baseStart_1526071 baseEnd_1526071 := by
    simpa [prefixWord, tailWord_1526071, baseEnd_1526071] using wordTrace_append hprefix tailTrace_1526071
  have hstable : (prefixWord ++ tailWord_1526071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526071).length < 2 ^ (prefixWord ++ tailWord_1526071).sum := by decide
  have hdescent : baseEnd_1526071 < baseStart_1526071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526078 : List Nat := [4, 2, 1, 2, 1, 2, 3, 1, 7]
def baseStart_1526078 : Nat := 118140960795 + 1526078 * 2 ^ 59
def prefixEnd_1526078 : Nat := 4983230072969 + 3 ^ 40 * 1526078 * 2
def baseEnd_1526078 : Nat := 87067947805798382945189

theorem tailTrace_1526078 : CollatzResearch.WordTrace tailWord_1526078 prefixEnd_1526078 87067947805798382945189 := by
  unfold tailWord_1526078
  simp only [CollatzResearch.WordTrace]
  refine ⟨6957579670660939277178361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37107091576858342811617925 6957579670660939277178361)
  ·
    refine ⟨5218184752995704457883771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6957579670660939277178361 5218184752995704457883771)
    ·
      refine ⟨7827277129493556686825657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5218184752995704457883771 7827277129493556686825657)
      ·
        refine ⟨5870457847120167515119243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7827277129493556686825657 5870457847120167515119243)
        ·
          refine ⟨8805686770680251272678865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5870457847120167515119243 8805686770680251272678865)
          ·
            refine ⟨6604265078010188454509149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8805686770680251272678865 6604265078010188454509149)
            ·
              refine ⟨2476599404253820670440931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6604265078010188454509149 2476599404253820670440931)
              ·
                refine ⟨3714899106380731005661397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2476599404253820670440931 3714899106380731005661397)
                ·
                  refine ⟨87067947805798382945189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3714899106380731005661397 87067947805798382945189)
                  ·
                    rfl

theorem cell23_1526078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_1526078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526078 prefixEnd_1526078 := by exact prefixLift 1526078
  have htrace : WordTrace (prefixWord ++ tailWord_1526078) baseStart_1526078 baseEnd_1526078 := by
    simpa [prefixWord, tailWord_1526078, baseEnd_1526078] using wordTrace_append hprefix tailTrace_1526078
  have hstable : (prefixWord ++ tailWord_1526078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526078).length < 2 ^ (prefixWord ++ tailWord_1526078).sum := by decide
  have hdescent : baseEnd_1526078 < baseStart_1526078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526110 : List Nat := [4, 4, 2, 1, 1, 1, 3, 1, 1, 3, 2]
def baseStart_1526110 : Nat := 118140960795 + 1526110 * 2 ^ 59
def prefixEnd_1526110 : Nat := 4983230072969 + 3 ^ 40 * 1526110 * 2
def baseEnd_1526110 : Nat := 783627961633129321306555

theorem tailTrace_1526110 : CollatzResearch.WordTrace tailWord_1526110 prefixEnd_1526110 783627961633129321306555 := by
  unfold tailWord_1526110
  simp only [CollatzResearch.WordTrace]
  refine ⟨6957725562646447960323973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37107869667447722455061189 6957725562646447960323973)
  ·
    refine ⟨1304573542996208992560745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6957725562646447960323973 1304573542996208992560745)
    ·
      refine ⟨978430157247156744420559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1304573542996208992560745 978430157247156744420559)
      ·
        refine ⟨1467645235870735116630839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 978430157247156744420559 1467645235870735116630839)
        ·
          refine ⟨2201467853806102674946259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1467645235870735116630839 2201467853806102674946259)
          ·
            refine ⟨3302201780709154012419389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2201467853806102674946259 3302201780709154012419389)
            ·
              refine ⟨1238325667765932754657271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3302201780709154012419389 1238325667765932754657271)
              ·
                refine ⟨1857488501648899131985907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1238325667765932754657271 1857488501648899131985907)
                ·
                  refine ⟨2786232752473348697978861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1857488501648899131985907 2786232752473348697978861)
                  ·
                    refine ⟨1044837282177505761742073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2786232752473348697978861 1044837282177505761742073)
                    ·
                      refine ⟨783627961633129321306555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1044837282177505761742073 783627961633129321306555)
                      ·
                        rfl

theorem cell23_1526110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_1526110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526110 prefixEnd_1526110 := by exact prefixLift 1526110
  have htrace : WordTrace (prefixWord ++ tailWord_1526110) baseStart_1526110 baseEnd_1526110 := by
    simpa [prefixWord, tailWord_1526110, baseEnd_1526110] using wordTrace_append hprefix tailTrace_1526110
  have hstable : (prefixWord ++ tailWord_1526110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526110).length < 2 ^ (prefixWord ++ tailWord_1526110).sum := by decide
  have hdescent : baseEnd_1526110 < baseStart_1526110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526111 : List Nat := [1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 4]
def baseStart_1526111 : Nat := 118140960795 + 1526111 * 2 ^ 59
def prefixEnd_1526111 : Nat := 4983230072969 + 3 ^ 40 * 1526111 * 2
def baseEnd_1526111 : Nat := 783628475113783817394049

theorem tailTrace_1526111 : CollatzResearch.WordTrace tailWord_1526111 prefixEnd_1526111 783628475113783817394049 := by
  unfold tailWord_1526111
  simp only [CollatzResearch.WordTrace]
  refine ⟨55661840974167960853378187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37107893982778640568918791 55661840974167960853378187)
  ·
    refine ⟨83492761461251941280067281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55661840974167960853378187 83492761461251941280067281)
    ·
      refine ⟨62619571095938955960050461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83492761461251941280067281 62619571095938955960050461)
      ·
        refine ⟨23482339160977108485018923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62619571095938955960050461 23482339160977108485018923)
        ·
          refine ⟨35223508741465662727528385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23482339160977108485018923 35223508741465662727528385)
          ·
            refine ⟨26417631556099247045646289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35223508741465662727528385 26417631556099247045646289)
            ·
              refine ⟨19813223667074435284234717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26417631556099247045646289 19813223667074435284234717)
              ·
                refine ⟨7429958875152913231588019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19813223667074435284234717 7429958875152913231588019)
                ·
                  refine ⟨11144938312729369847382029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7429958875152913231588019 11144938312729369847382029)
                  ·
                    refine ⟨4179351867273513692768261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11144938312729369847382029 4179351867273513692768261)
                    ·
                      refine ⟨783628475113783817394049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4179351867273513692768261 783628475113783817394049)
                      ·
                        rfl

theorem cell23_1526111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_1526111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526111 prefixEnd_1526111 := by exact prefixLift 1526111
  have htrace : WordTrace (prefixWord ++ tailWord_1526111) baseStart_1526111 baseEnd_1526111 := by
    simpa [prefixWord, tailWord_1526111, baseEnd_1526111] using wordTrace_append hprefix tailTrace_1526111
  have hstable : (prefixWord ++ tailWord_1526111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526111).length < 2 ^ (prefixWord ++ tailWord_1526111).sum := by decide
  have hdescent : baseEnd_1526111 < baseStart_1526111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526128 : List Nat := [2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 4]
def baseStart_1526128 : Nat := 118140960795 + 1526128 * 2 ^ 59
def prefixEnd_1526128 : Nat := 4983230072969 + 3 ^ 40 * 1526128 * 2
def baseEnd_1526128 : Nat := 783637204284910250881471

theorem tailTrace_1526128 : CollatzResearch.WordTrace tailWord_1526128 prefixEnd_1526128 783637204284910250881471 := by
  unfold tailWord_1526128
  simp only [CollatzResearch.WordTrace]
  refine ⟨27831230507553186378373519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37108307343404248504498025 27831230507553186378373519)
  ·
    refine ⟨41746845761329779567560279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27831230507553186378373519 41746845761329779567560279)
    ·
      refine ⟨62620268641994669351340419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41746845761329779567560279 62620268641994669351340419)
      ·
        refine ⟨93930402962992004027010629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62620268641994669351340419 93930402962992004027010629)
        ·
          refine ⟨17611950555561000755064493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93930402962992004027010629 17611950555561000755064493)
          ·
            refine ⟨6604481458335375283149185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17611950555561000755064493 6604481458335375283149185)
            ·
              refine ⟨4953361093751531462361889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6604481458335375283149185 4953361093751531462361889)
              ·
                refine ⟨3715020820313648596771417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4953361093751531462361889 3715020820313648596771417)
                ·
                  refine ⟨2786265615235236447578563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3715020820313648596771417 2786265615235236447578563)
                  ·
                    refine ⟨4179398422852854671367845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2786265615235236447578563 4179398422852854671367845)
                    ·
                      refine ⟨783637204284910250881471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4179398422852854671367845 783637204284910250881471)
                      ·
                        rfl

theorem cell23_1526128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 4].length) (baseStart_1526128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526128 prefixEnd_1526128 := by exact prefixLift 1526128
  have htrace : WordTrace (prefixWord ++ tailWord_1526128) baseStart_1526128 baseEnd_1526128 := by
    simpa [prefixWord, tailWord_1526128, baseEnd_1526128] using wordTrace_append hprefix tailTrace_1526128
  have hstable : (prefixWord ++ tailWord_1526128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526128).length < 2 ^ (prefixWord ++ tailWord_1526128).sum := by decide
  have hdescent : baseEnd_1526128 < baseStart_1526128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526145 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 1, 6, 2]
def baseStart_1526145 : Nat := 118140960795 + 1526145 * 2 ^ 59
def prefixEnd_1526145 : Nat := 4983230072969 + 3 ^ 40 * 1526145 * 2
def baseEnd_1526145 : Nat := 783645933456036684368893

theorem tailTrace_1526145 : CollatzResearch.WordTrace tailWord_1526145 prefixEnd_1526145 783645933456036684368893 := by
  unfold tailWord_1526145
  simp only [CollatzResearch.WordTrace]
  refine ⟨55663081056044784660115889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37108720704029856440077259 55663081056044784660115889)
  ·
    refine ⟨41747310792033588495086917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55663081056044784660115889 41747310792033588495086917)
    ·
      refine ⟨7827620773506297842828797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41747310792033588495086917 7827620773506297842828797)
      ·
        refine ⟨2935357790064861691060799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7827620773506297842828797 2935357790064861691060799)
        ·
          refine ⟨4403036685097292536591199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2935357790064861691060799 4403036685097292536591199)
          ·
            refine ⟨6604555027645938804886799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4403036685097292536591199 6604555027645938804886799)
            ·
              refine ⟨9906832541468908207330199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6604555027645938804886799 9906832541468908207330199)
              ·
                refine ⟨14860248812203362310995299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9906832541468908207330199 14860248812203362310995299)
                ·
                  refine ⟨22290373218305043466492949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14860248812203362310995299 22290373218305043466492949)
                  ·
                    refine ⟨1044861244608048912491857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22290373218305043466492949 1044861244608048912491857)
                    ·
                      refine ⟨783645933456036684368893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1044861244608048912491857 783645933456036684368893)
                      ·
                        rfl

theorem cell23_1526145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_1526145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526145 prefixEnd_1526145 := by exact prefixLift 1526145
  have htrace : WordTrace (prefixWord ++ tailWord_1526145) baseStart_1526145 baseEnd_1526145 := by
    simpa [prefixWord, tailWord_1526145, baseEnd_1526145] using wordTrace_append hprefix tailTrace_1526145
  have hstable : (prefixWord ++ tailWord_1526145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526145).length < 2 ^ (prefixWord ++ tailWord_1526145).sum := by decide
  have hdescent : baseEnd_1526145 < baseStart_1526145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526148 : List Nat := [2, 3, 2, 1, 1, 2, 2, 2, 1, 4, 3]
def baseStart_1526148 : Nat := 118140960795 + 1526148 * 2 ^ 59
def prefixEnd_1526148 : Nat := 4983230072969 + 3 ^ 40 * 1526148 * 2
def baseEnd_1526148 : Nat := 783647473898000172631379

theorem tailTrace_1526148 : CollatzResearch.WordTrace tailWord_1526148 prefixEnd_1526148 783647473898000172631379 := by
  unfold tailWord_1526148
  simp only [CollatzResearch.WordTrace]
  refine ⟨27831595237516958086237549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37108793650022610781650065 27831595237516958086237549)
  ·
    refine ⟨10436848214068859282339081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27831595237516958086237549 10436848214068859282339081)
    ·
      refine ⟨7827636160551644461754311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10436848214068859282339081 7827636160551644461754311)
      ·
        refine ⟨11741454240827466692631467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7827636160551644461754311 11741454240827466692631467)
        ·
          refine ⟨17612181361241200038947201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11741454240827466692631467 17612181361241200038947201)
          ·
            refine ⟨13209136020930900029210401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17612181361241200038947201 13209136020930900029210401)
            ·
              refine ⟨9906852015698175021907801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13209136020930900029210401 9906852015698175021907801)
              ·
                refine ⟨7430139011773631266430851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9906852015698175021907801 7430139011773631266430851)
                ·
                  refine ⟨11145208517660446899646277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7430139011773631266430851 11145208517660446899646277)
                  ·
                    refine ⟨2089726597061333793683677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11145208517660446899646277 2089726597061333793683677)
                    ·
                      refine ⟨783647473898000172631379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2089726597061333793683677 783647473898000172631379)
                      ·
                        rfl

theorem cell23_1526148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_1526148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526148 prefixEnd_1526148 := by exact prefixLift 1526148
  have htrace : WordTrace (prefixWord ++ tailWord_1526148) baseStart_1526148 baseEnd_1526148 := by
    simpa [prefixWord, tailWord_1526148, baseEnd_1526148] using wordTrace_append hprefix tailTrace_1526148
  have hstable : (prefixWord ++ tailWord_1526148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526148).length < 2 ^ (prefixWord ++ tailWord_1526148).sum := by decide
  have hdescent : baseEnd_1526148 < baseStart_1526148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526205 : List Nat := [1, 4, 1, 2, 2, 2, 1, 2, 1, 5, 2]
def baseStart_1526205 : Nat := 118140960795 + 1526205 * 2 ^ 59
def prefixEnd_1526205 : Nat := 4983230072969 + 3 ^ 40 * 1526205 * 2
def baseEnd_1526205 : Nat := 783676742295306449618617

theorem tailTrace_1526205 : CollatzResearch.WordTrace tailWord_1526205 prefixEnd_1526205 783676742295306449618617 := by
  unfold tailWord_1526205
  simp only [CollatzResearch.WordTrace]
  refine ⟨55665269435827414907300069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37110179623884943271533379 55665269435827414907300069)
  ·
    refine ⟨10437238019217640295118763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55665269435827414907300069 10437238019217640295118763)
    ·
      refine ⟨15655857028826460442678145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10437238019217640295118763 15655857028826460442678145)
      ·
        refine ⟨11741892771619845332008609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15655857028826460442678145 11741892771619845332008609)
        ·
          refine ⟨8806419578714883999006457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11741892771619845332008609 8806419578714883999006457)
          ·
            refine ⟨6604814684036162999254843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8806419578714883999006457 6604814684036162999254843)
            ·
              refine ⟨9907222026054244498882265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6604814684036162999254843 9907222026054244498882265)
              ·
                refine ⟨7430416519540683374161699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9907222026054244498882265 7430416519540683374161699)
                ·
                  refine ⟨11145624779311025061242549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7430416519540683374161699 11145624779311025061242549)
                  ·
                    refine ⟨1044902323060408599491489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11145624779311025061242549 1044902323060408599491489)
                    ·
                      refine ⟨783676742295306449618617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1044902323060408599491489 783676742295306449618617)
                      ·
                        rfl

theorem cell23_1526205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_1526205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526205 prefixEnd_1526205 := by exact prefixLift 1526205
  have htrace : WordTrace (prefixWord ++ tailWord_1526205) baseStart_1526205 baseEnd_1526205 := by
    simpa [prefixWord, tailWord_1526205, baseEnd_1526205] using wordTrace_append hprefix tailTrace_1526205
  have hstable : (prefixWord ++ tailWord_1526205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526205).length < 2 ^ (prefixWord ++ tailWord_1526205).sum := by decide
  have hdescent : baseEnd_1526205 < baseStart_1526205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526215 : List Nat := [1, 1, 4, 1, 1, 5, 2, 2, 1, 5]
def baseStart_1526215 : Nat := 118140960795 + 1526215 * 2 ^ 59
def prefixEnd_1526215 : Nat := 4983230072969 + 3 ^ 40 * 1526215 * 2
def baseEnd_1526215 : Nat := 261227292367283803497857

theorem tailTrace_1526215 : CollatzResearch.WordTrace tailWord_1526215 prefixEnd_1526215 261227292367283803497857 := by
  unfold tailWord_1526215
  simp only [CollatzResearch.WordTrace]
  refine ⟨55665634165791186615164099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37110422777194124410109399 55665634165791186615164099)
  ·
    refine ⟨83498451248686779922746149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55665634165791186615164099 83498451248686779922746149)
    ·
      refine ⟨15655959609128771235514903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83498451248686779922746149 15655959609128771235514903)
      ·
        refine ⟨23483939413693156853272355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15655959609128771235514903 23483939413693156853272355)
        ·
          refine ⟨35225909120539735279908533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23483939413693156853272355 35225909120539735279908533)
          ·
            refine ⟨3302428980050600182491425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35225909120539735279908533 3302428980050600182491425)
            ·
              refine ⟨2476821735037950136868569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3302428980050600182491425 2476821735037950136868569)
              ·
                refine ⟨1857616301278462602651427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2476821735037950136868569 1857616301278462602651427)
                ·
                  refine ⟨2786424451917693903977141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1857616301278462602651427 2786424451917693903977141)
                  ·
                    refine ⟨261227292367283803497857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2786424451917693903977141 261227292367283803497857)
                    ·
                      rfl

theorem cell23_1526215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_1526215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526215 prefixEnd_1526215 := by exact prefixLift 1526215
  have htrace : WordTrace (prefixWord ++ tailWord_1526215) baseStart_1526215 baseEnd_1526215 := by
    simpa [prefixWord, tailWord_1526215, baseEnd_1526215] using wordTrace_append hprefix tailTrace_1526215
  have hstable : (prefixWord ++ tailWord_1526215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526215).length < 2 ^ (prefixWord ++ tailWord_1526215).sum := by decide
  have hdescent : baseEnd_1526215 < baseStart_1526215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526229 : List Nat := [1, 3, 2, 3, 1, 2, 3, 3, 1, 1, 3]
def baseStart_1526229 : Nat := 118140960795 + 1526229 * 2 ^ 59
def prefixEnd_1526229 : Nat := 4983230072969 + 3 ^ 40 * 1526229 * 2
def baseEnd_1526229 : Nat := 783689065831014355718507

theorem tailTrace_1526229 : CollatzResearch.WordTrace tailWord_1526229 prefixEnd_1526229 783689065831014355718507 := by
  unfold tailWord_1526229
  simp only [CollatzResearch.WordTrace]
  refine ⟨55666144787740467006173741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37110763191826978004115827 55666144787740467006173741)
  ·
    refine ⟨20874804295402675127315153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55666144787740467006173741 20874804295402675127315153)
    ·
      refine ⟨15656103221552006345486365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20874804295402675127315153 15656103221552006345486365)
      ·
        refine ⟨5871038708082002379557387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15656103221552006345486365 5871038708082002379557387)
        ·
          refine ⟨8806558062123003569336081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5871038708082002379557387 8806558062123003569336081)
          ·
            refine ⟨6604918546592252677002061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8806558062123003569336081 6604918546592252677002061)
            ·
              refine ⟨2476844454972094753875773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6604918546592252677002061 2476844454972094753875773)
              ·
                refine ⟨928816670614535532703415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2476844454972094753875773 928816670614535532703415)
                ·
                  refine ⟨1393225005921803299055123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 928816670614535532703415 1393225005921803299055123)
                  ·
                    refine ⟨2089837508882704948582685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1393225005921803299055123 2089837508882704948582685)
                    ·
                      refine ⟨783689065831014355718507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2089837508882704948582685 783689065831014355718507)
                      ·
                        rfl

theorem cell23_1526229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_1526229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526229 prefixEnd_1526229 := by exact prefixLift 1526229
  have htrace : WordTrace (prefixWord ++ tailWord_1526229) baseStart_1526229 baseEnd_1526229 := by
    simpa [prefixWord, tailWord_1526229, baseEnd_1526229] using wordTrace_append hprefix tailTrace_1526229
  have hstable : (prefixWord ++ tailWord_1526229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526229).length < 2 ^ (prefixWord ++ tailWord_1526229).sum := by decide
  have hdescent : baseEnd_1526229 < baseStart_1526229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526248 : List Nat := [2, 1, 4, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_1526248 : Nat := 118140960795 + 1526248 * 2 ^ 59
def prefixEnd_1526248 : Nat := 4983230072969 + 3 ^ 40 * 1526248 * 2
def baseEnd_1526248 : Nat := 783698821963449781380919

theorem tailTrace_1526248 : CollatzResearch.WordTrace tailWord_1526248 prefixEnd_1526248 783698821963449781380919 := by
  unfold tailWord_1526248
  simp only [CollatzResearch.WordTrace]
  refine ⟨27833418887335816625557699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37111225183114422167410265 27833418887335816625557699)
  ·
    refine ⟨41750128331003724938336549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27833418887335816625557699 41750128331003724938336549)
    ·
      refine ⟨7828149062063198425938103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41750128331003724938336549 7828149062063198425938103)
      ·
        refine ⟨11742223593094797638907155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7828149062063198425938103 11742223593094797638907155)
        ·
          refine ⟨17613335389642196458360733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11742223593094797638907155 17613335389642196458360733)
          ·
            refine ⟨6605000771115823671885275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17613335389642196458360733 6605000771115823671885275)
            ·
              refine ⟨9907501156673735507827913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6605000771115823671885275 9907501156673735507827913)
              ·
                refine ⟨7430625867505301630870935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9907501156673735507827913 7430625867505301630870935)
                ·
                  refine ⟨11145938801257952446306403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7430625867505301630870935 11145938801257952446306403)
                  ·
                    refine ⟨16718908201886928669459605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11145938801257952446306403 16718908201886928669459605)
                    ·
                      refine ⟨783698821963449781380919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16718908201886928669459605 783698821963449781380919)
                      ·
                        rfl

theorem cell23_1526248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_1526248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526248 prefixEnd_1526248 := by exact prefixLift 1526248
  have htrace : WordTrace (prefixWord ++ tailWord_1526248) baseStart_1526248 baseEnd_1526248 := by
    simpa [prefixWord, tailWord_1526248, baseEnd_1526248] using wordTrace_append hprefix tailTrace_1526248
  have hstable : (prefixWord ++ tailWord_1526248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526248).length < 2 ^ (prefixWord ++ tailWord_1526248).sum := by decide
  have hdescent : baseEnd_1526248 < baseStart_1526248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526262 : List Nat := [5, 1, 1, 1, 2, 1, 3, 3, 2, 4]
def baseStart_1526262 : Nat := 118140960795 + 1526262 * 2 ^ 59
def prefixEnd_1526262 : Nat := 4983230072969 + 3 ^ 40 * 1526262 * 2
def baseEnd_1526262 : Nat := 261235336897537575535285

theorem tailTrace_1526262 : CollatzResearch.WordTrace tailWord_1526262 prefixEnd_1526262 261235336897537575535285 := by
  unfold tailWord_1526262
  simp only [CollatzResearch.WordTrace]
  refine ⟨3479209274788807102632815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37111565597747275761416693 3479209274788807102632815)
  ·
    refine ⟨5218813912183210653949223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3479209274788807102632815 5218813912183210653949223)
    ·
      refine ⟨7828220868274815980923835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5218813912183210653949223 7828220868274815980923835)
      ·
        refine ⟨11742331302412223971385753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7828220868274815980923835 11742331302412223971385753)
        ·
          refine ⟨8806748476809167978539315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11742331302412223971385753 8806748476809167978539315)
          ·
            refine ⟨13210122715213751967808973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8806748476809167978539315 13210122715213751967808973)
            ·
              refine ⟨4953796018205156987928365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13210122715213751967808973 4953796018205156987928365)
              ·
                refine ⟨1857673506826933870473137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4953796018205156987928365 1857673506826933870473137)
                ·
                  refine ⟨1393255130120200402854853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1857673506826933870473137 1393255130120200402854853)
                  ·
                    refine ⟨261235336897537575535285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1393255130120200402854853 261235336897537575535285)
                    ·
                      rfl

theorem cell23_1526262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_1526262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526262 prefixEnd_1526262 := by exact prefixLift 1526262
  have htrace : WordTrace (prefixWord ++ tailWord_1526262) baseStart_1526262 baseEnd_1526262 := by
    simpa [prefixWord, tailWord_1526262, baseEnd_1526262] using wordTrace_append hprefix tailTrace_1526262
  have hstable : (prefixWord ++ tailWord_1526262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526262).length < 2 ^ (prefixWord ++ tailWord_1526262).sum := by decide
  have hdescent : baseEnd_1526262 < baseStart_1526262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
