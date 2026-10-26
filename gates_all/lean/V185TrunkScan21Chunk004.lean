import V185TrunkScan21Chunk003

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_48367 : List Nat := [1, 1, 2, 1, 7, 2, 1, 1, 5]
def baseStart_48367 : Nat := 118140960795 + 48367 * 2 ^ 59
def prefixEnd_48367 : Nat := 4983230072969 + 3 ^ 40 * 48367 * 2
def baseEnd_48367 : Nat := 11038008362718887817809

theorem tailTrace_48367 : CollatzResearch.WordTrace tailWord_48367 prefixEnd_48367 11038008362718887817809 := by
  unfold tailWord_48367
  simp only [CollatzResearch.WordTrace]
  refine ⟨1764089415782094271063355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1176059610521396180708903 1764089415782094271063355)
  ·
    refine ⟨2646134123673141406595033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1764089415782094271063355 2646134123673141406595033)
    ·
      refine ⟨1984600592754856054946275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2646134123673141406595033 1984600592754856054946275)
      ·
        refine ⟨2976900889132284082419413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1984600592754856054946275 2976900889132284082419413)
        ·
          refine ⟨69771114589037908181705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 2976900889132284082419413 69771114589037908181705)
          ·
            refine ⟨52328335941778431136279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69771114589037908181705 52328335941778431136279)
            ·
              refine ⟨78492503912667646704419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52328335941778431136279 78492503912667646704419)
              ·
                refine ⟨117738755869001470056629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78492503912667646704419 117738755869001470056629)
                ·
                  refine ⟨11038008362718887817809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117738755869001470056629 11038008362718887817809)
                  ·
                    rfl

theorem cell21_48367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 5].length) (baseStart_48367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_48367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_48367 prefixEnd_48367 := by exact prefixLift 48367
  have htrace : WordTrace (prefixWord ++ tailWord_48367) baseStart_48367 baseEnd_48367 := by
    simpa [prefixWord, tailWord_48367, baseEnd_48367] using wordTrace_append hprefix tailTrace_48367
  have hstable : (prefixWord ++ tailWord_48367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48367).length < 2 ^ (prefixWord ++ tailWord_48367).sum := by decide
  have hdescent : baseEnd_48367 < baseStart_48367 := by decide
  rcases family_descends (prefixWord ++ tailWord_48367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48418 : List Nat := [3, 3, 1, 1, 5, 1, 2, 2, 3]
def baseStart_48418 : Nat := 118140960795 + 48418 * 2 ^ 59
def prefixEnd_48418 : Nat := 4983230072969 + 3 ^ 40 * 48418 * 2
def baseEnd_48418 : Nat := 11049647257554132467705

theorem tailTrace_48418 : CollatzResearch.WordTrace tailWord_48418 prefixEnd_48418 11049647257554132467705 := by
  unfold tailWord_48418
  simp only [CollatzResearch.WordTrace]
  refine ⟨441487384649332495292477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1177299692398219987446605 441487384649332495292477)
  ·
    refine ⟨165557769243499685734679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 441487384649332495292477 165557769243499685734679)
    ·
      refine ⟨248336653865249528602019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165557769243499685734679 248336653865249528602019)
      ·
        refine ⟨372504980797874292903029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248336653865249528602019 372504980797874292903029)
        ·
          refine ⟨34922341949800714959659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 372504980797874292903029 34922341949800714959659)
          ·
            refine ⟨52383512924701072439489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34922341949800714959659 52383512924701072439489)
            ·
              refine ⟨39287634693525804329617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52383512924701072439489 39287634693525804329617)
              ·
                refine ⟨29465726020144353247213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39287634693525804329617 29465726020144353247213)
                ·
                  refine ⟨11049647257554132467705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29465726020144353247213 11049647257554132467705)
                  ·
                    rfl

theorem cell21_48418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_48418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_48418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_48418 prefixEnd_48418 := by exact prefixLift 48418
  have htrace : WordTrace (prefixWord ++ tailWord_48418) baseStart_48418 baseEnd_48418 := by
    simpa [prefixWord, tailWord_48418, baseEnd_48418] using wordTrace_append hprefix tailTrace_48418
  have hstable : (prefixWord ++ tailWord_48418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48418).length < 2 ^ (prefixWord ++ tailWord_48418).sum := by decide
  have hdescent : baseEnd_48418 < baseStart_48418 := by decide
  rcases family_descends (prefixWord ++ tailWord_48418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48429 : List Nat := [1, 5, 3, 1, 1, 3, 1, 6]
def baseStart_48429 : Nat := 118140960795 + 48429 * 2 ^ 59
def prefixEnd_48429 : Nat := 4983230072969 + 3 ^ 40 * 48429 * 2
def baseEnd_48429 : Nat := 3684052535806852594783

theorem tailTrace_48429 : CollatzResearch.WordTrace tailWord_48429 prefixEnd_48429 3684052535806852594783 := by
  unfold tailWord_48429
  simp only [CollatzResearch.WordTrace]
  refine ⟨1766350741557478859820341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1177567161038319239880227 1766350741557478859820341)
  ·
    refine ⟨165595382021013643108157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1766350741557478859820341 165595382021013643108157)
    ·
      refine ⟨62098268257880116165559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165595382021013643108157 62098268257880116165559)
      ·
        refine ⟨93147402386820174248339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62098268257880116165559 93147402386820174248339)
        ·
          refine ⟨139721103580230261372509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93147402386820174248339 139721103580230261372509)
          ·
            refine ⟨52395413842586348014691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139721103580230261372509 52395413842586348014691)
            ·
              refine ⟨78593120763879522022037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52395413842586348014691 78593120763879522022037)
              ·
                refine ⟨3684052535806852594783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78593120763879522022037 3684052535806852594783)
                ·
                  rfl

theorem cell21_48429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 6].length) (baseStart_48429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_48429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_48429 prefixEnd_48429 := by exact prefixLift 48429
  have htrace : WordTrace (prefixWord ++ tailWord_48429) baseStart_48429 baseEnd_48429 := by
    simpa [prefixWord, tailWord_48429, baseEnd_48429] using wordTrace_append hprefix tailTrace_48429
  have hstable : (prefixWord ++ tailWord_48429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48429).length < 2 ^ (prefixWord ++ tailWord_48429).sum := by decide
  have hdescent : baseEnd_48429 < baseStart_48429 := by decide
  rcases family_descends (prefixWord ++ tailWord_48429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48477 : List Nat := [1, 4, 5, 1, 1, 1, 2, 1, 5]
def baseStart_48477 : Nat := 118140960795 + 48477 * 2 ^ 59
def prefixEnd_48477 : Nat := 4983230072969 + 3 ^ 40 * 48477 * 2
def baseEnd_48477 : Nat := 11063111861383140984251

theorem tailTrace_48477 : CollatzResearch.WordTrace tailWord_48477 prefixEnd_48477 11063111861383140984251 := by
  unfold tailWord_48477
  simp only [CollatzResearch.WordTrace]
  refine ⟨1768101445383583057567685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1178734296922388705045123 1768101445383583057567685)
  ·
    refine ⟨331519021009421823293941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1768101445383583057567685 331519021009421823293941)
    ·
      refine ⟨31079908219633295933807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 331519021009421823293941 31079908219633295933807)
      ·
        refine ⟨46619862329449943900711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31079908219633295933807 46619862329449943900711)
        ·
          refine ⟨69929793494174915851067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46619862329449943900711 69929793494174915851067)
          ·
            refine ⟨104894690241262373776601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69929793494174915851067 104894690241262373776601)
            ·
              refine ⟨78671017680946780332451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104894690241262373776601 78671017680946780332451)
              ·
                refine ⟨118006526521420170498677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78671017680946780332451 118006526521420170498677)
                ·
                  refine ⟨11063111861383140984251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118006526521420170498677 11063111861383140984251)
                  ·
                    rfl

theorem cell21_48477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_48477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_48477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_48477 prefixEnd_48477 := by exact prefixLift 48477
  have htrace : WordTrace (prefixWord ++ tailWord_48477) baseStart_48477 baseEnd_48477 := by
    simpa [prefixWord, tailWord_48477, baseEnd_48477] using wordTrace_append hprefix tailTrace_48477
  have hstable : (prefixWord ++ tailWord_48477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48477).length < 2 ^ (prefixWord ++ tailWord_48477).sum := by decide
  have hdescent : baseEnd_48477 < baseStart_48477 := by decide
  rcases family_descends (prefixWord ++ tailWord_48477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48499 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 10]
def baseStart_48499 : Nat := 118140960795 + 48499 * 2 ^ 59
def prefixEnd_48499 : Nat := 4983230072969 + 3 ^ 40 * 48499 * 2
def baseEnd_48499 : Nat := 11068132561115991617539

theorem tailTrace_48499 : CollatzResearch.WordTrace tailWord_48499 prefixEnd_48499 11068132561115991617539 := by
  unfold tailWord_48499
  simp only [CollatzResearch.WordTrace]
  refine ⟨1768903851303880814868551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1179269234202587209912367 1768903851303880814868551)
  ·
    refine ⟨2653355776955821222302827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1768903851303880814868551 2653355776955821222302827)
    ·
      refine ⟨3980033665433731833454241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2653355776955821222302827 3980033665433731833454241)
      ·
        refine ⟨2985025249075298875090681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3980033665433731833454241 2985025249075298875090681)
        ·
          refine ⟨2238768936806474156318011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2985025249075298875090681 2238768936806474156318011)
          ·
            refine ⟨3358153405209711234477017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2238768936806474156318011 3358153405209711234477017)
            ·
              refine ⟨2518615053907283425857763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3358153405209711234477017 2518615053907283425857763)
              ·
                refine ⟨3777922580860925138786645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2518615053907283425857763 3777922580860925138786645)
                ·
                  refine ⟨11068132561115991617539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 3777922580860925138786645 11068132561115991617539)
                  ·
                    rfl

theorem cell21_48499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 10].length) (baseStart_48499 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_48499 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_48499 prefixEnd_48499 := by exact prefixLift 48499
  have htrace : WordTrace (prefixWord ++ tailWord_48499) baseStart_48499 baseEnd_48499 := by
    simpa [prefixWord, tailWord_48499, baseEnd_48499] using wordTrace_append hprefix tailTrace_48499
  have hstable : (prefixWord ++ tailWord_48499).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48499).length < 2 ^ (prefixWord ++ tailWord_48499).sum := by decide
  have hdescent : baseEnd_48499 < baseStart_48499 := by decide
  rcases family_descends (prefixWord ++ tailWord_48499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48516 : List Nat := [2, 3, 2, 1, 1, 3, 1, 2, 6]
def baseStart_48516 : Nat := 118140960795 + 48516 * 2 ^ 59
def prefixEnd_48516 : Nat := 4983230072969 + 3 ^ 40 * 48516 * 2
def baseEnd_48516 : Nat := 11072012192727739834171

theorem tailTrace_48516 : CollatzResearch.WordTrace tailWord_48516 prefixEnd_48516 11072012192727739834171 := by
  unfold tailWord_48516
  simp only [CollatzResearch.WordTrace]
  refine ⟨884761946121146359118701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1179682594828195145491601 884761946121146359118701)
  ·
    refine ⟨331785729795429884669513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 884761946121146359118701 331785729795429884669513)
    ·
      refine ⟨248839297346572413502135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331785729795429884669513 248839297346572413502135)
      ·
        refine ⟨373258946019858620253203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248839297346572413502135 373258946019858620253203)
        ·
          refine ⟨559888419029787930379805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373258946019858620253203 559888419029787930379805)
          ·
            refine ⟨209958157136170473892427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 559888419029787930379805 209958157136170473892427)
            ·
              refine ⟨314937235704255710838641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209958157136170473892427 314937235704255710838641)
              ·
                refine ⟨236202926778191783128981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314937235704255710838641 236202926778191783128981)
                ·
                  refine ⟨11072012192727739834171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 236202926778191783128981 11072012192727739834171)
                  ·
                    rfl

theorem cell21_48516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_48516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_48516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_48516 prefixEnd_48516 := by exact prefixLift 48516
  have htrace : WordTrace (prefixWord ++ tailWord_48516) baseStart_48516 baseEnd_48516 := by
    simpa [prefixWord, tailWord_48516, baseEnd_48516] using wordTrace_append hprefix tailTrace_48516
  have hstable : (prefixWord ++ tailWord_48516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48516).length < 2 ^ (prefixWord ++ tailWord_48516).sum := by decide
  have hdescent : baseEnd_48516 < baseStart_48516 := by decide
  rcases family_descends (prefixWord ++ tailWord_48516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48519 : List Nat := [1, 1, 4, 2, 2, 2, 3, 3, 3]
def baseStart_48519 : Nat := 118140960795 + 48519 * 2 ^ 59
def prefixEnd_48519 : Nat := 4983230072969 + 3 ^ 40 * 48519 * 2
def baseEnd_48519 : Nat := 11072696833600401284165

theorem tailTrace_48519 : CollatzResearch.WordTrace tailWord_48519 prefixEnd_48519 11072696833600401284165 := by
  unfold tailWord_48519
  simp only [CollatzResearch.WordTrace]
  refine ⟨1769633311231424230596611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1179755540820949487064407 1769633311231424230596611)
  ·
    refine ⟨2654449966847136345894917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1769633311231424230596611 2654449966847136345894917)
    ·
      refine ⟨497709368783838064855297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2654449966847136345894917 497709368783838064855297)
      ·
        refine ⟨373282026587878548641473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 497709368783838064855297 373282026587878548641473)
        ·
          refine ⟨279961519940908911481105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373282026587878548641473 279961519940908911481105)
          ·
            refine ⟨209971139955681683610829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279961519940908911481105 209971139955681683610829)
            ·
              refine ⟨78739177483380631354061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209971139955681683610829 78739177483380631354061)
              ·
                refine ⟨29527191556267736757773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78739177483380631354061 29527191556267736757773)
                ·
                  refine ⟨11072696833600401284165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29527191556267736757773 11072696833600401284165)
                  ·
                    rfl

theorem cell21_48519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3, 3].length) (baseStart_48519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_48519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_48519 prefixEnd_48519 := by exact prefixLift 48519
  have htrace : WordTrace (prefixWord ++ tailWord_48519) baseStart_48519 baseEnd_48519 := by
    simpa [prefixWord, tailWord_48519, baseEnd_48519] using wordTrace_append hprefix tailTrace_48519
  have hstable : (prefixWord ++ tailWord_48519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48519).length < 2 ^ (prefixWord ++ tailWord_48519).sum := by decide
  have hdescent : baseEnd_48519 < baseStart_48519 := by decide
  rcases family_descends (prefixWord ++ tailWord_48519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48536 : List Nat := [2, 1, 2, 5, 3, 1, 1, 1, 5]
def baseStart_48536 : Nat := 118140960795 + 48536 * 2 ^ 59
def prefixEnd_48536 : Nat := 4983230072969 + 3 ^ 40 * 48536 * 2
def baseEnd_48536 : Nat := 11076576465212149500797

theorem tailTrace_48536 : CollatzResearch.WordTrace tailWord_48536 prefixEnd_48536 11076576465212149500797 := by
  unfold tailWord_48536
  simp only [CollatzResearch.WordTrace]
  refine ⟨885126676084918066982731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1180168901446557422643641 885126676084918066982731)
  ·
    refine ⟨1327690014127377100474097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 885126676084918066982731 1327690014127377100474097)
    ·
      refine ⟨995767510595532825355573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1327690014127377100474097 995767510595532825355573)
      ·
        refine ⟨93353204118331202377085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 995767510595532825355573 93353204118331202377085)
        ·
          refine ⟨35007451544374200891407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93353204118331202377085 35007451544374200891407)
          ·
            refine ⟨52511177316561301337111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35007451544374200891407 52511177316561301337111)
            ·
              refine ⟨78766765974841952005667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52511177316561301337111 78766765974841952005667)
              ·
                refine ⟨118150148962262928008501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78766765974841952005667 118150148962262928008501)
                ·
                  refine ⟨11076576465212149500797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118150148962262928008501 11076576465212149500797)
                  ·
                    rfl

theorem cell21_48536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 5].length) (baseStart_48536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_48536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_48536 prefixEnd_48536 := by exact prefixLift 48536
  have htrace : WordTrace (prefixWord ++ tailWord_48536) baseStart_48536 baseEnd_48536 := by
    simpa [prefixWord, tailWord_48536, baseEnd_48536] using wordTrace_append hprefix tailTrace_48536
  have hstable : (prefixWord ++ tailWord_48536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48536).length < 2 ^ (prefixWord ++ tailWord_48536).sum := by decide
  have hdescent : baseEnd_48536 < baseStart_48536 := by decide
  rcases family_descends (prefixWord ++ tailWord_48536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48561 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 7]
def baseStart_48561 : Nat := 118140960795 + 48561 * 2 ^ 59
def prefixEnd_48561 : Nat := 4983230072969 + 3 ^ 40 * 48561 * 2
def baseEnd_48561 : Nat := 11082281805817661584079

theorem tailTrace_48561 : CollatzResearch.WordTrace tailWord_48561 prefixEnd_48561 11082281805817661584079 := by
  unfold tailWord_48561
  simp only [CollatzResearch.WordTrace]
  refine ⟨1771165177079265403625537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1180776784719510269083691 1771165177079265403625537)
  ·
    refine ⟨1328373882809449052719153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1771165177079265403625537 1328373882809449052719153)
    ·
      refine ⟨996280412107086789539365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1328373882809449052719153 996280412107086789539365)
      ·
        refine ⟨186802577270078773038631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 996280412107086789539365 186802577270078773038631)
        ·
          refine ⟨280203865905118159557947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186802577270078773038631 280203865905118159557947)
          ·
            refine ⟨420305798857677239336921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280203865905118159557947 420305798857677239336921)
            ·
              refine ⟨315229349143257929502691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420305798857677239336921 315229349143257929502691)
              ·
                refine ⟨472844023714886894254037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315229349143257929502691 472844023714886894254037)
                ·
                  refine ⟨11082281805817661584079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 472844023714886894254037 11082281805817661584079)
                  ·
                    rfl

theorem cell21_48561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 7].length) (baseStart_48561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_48561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_48561 prefixEnd_48561 := by exact prefixLift 48561
  have htrace : WordTrace (prefixWord ++ tailWord_48561) baseStart_48561 baseEnd_48561 := by
    simpa [prefixWord, tailWord_48561, baseEnd_48561] using wordTrace_append hprefix tailTrace_48561
  have hstable : (prefixWord ++ tailWord_48561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48561).length < 2 ^ (prefixWord ++ tailWord_48561).sum := by decide
  have hdescent : baseEnd_48561 < baseStart_48561 := by decide
  rcases family_descends (prefixWord ++ tailWord_48561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48575 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 8]
def baseStart_48575 : Nat := 118140960795 + 48575 * 2 ^ 59
def prefixEnd_48575 : Nat := 4983230072969 + 3 ^ 40 * 48575 * 2
def baseEnd_48575 : Nat := 11085476796556748350717

theorem tailTrace_48575 : CollatzResearch.WordTrace tailWord_48575 prefixEnd_48575 11085476796556748350717 := by
  unfold tailWord_48575
  simp only [CollatzResearch.WordTrace]
  refine ⟨1771675799028545794635179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1181117199352363863090119 1771675799028545794635179)
  ·
    refine ⟨2657513698542818691952769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1771675799028545794635179 2657513698542818691952769)
    ·
      refine ⟨1993135273907114018964577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2657513698542818691952769 1993135273907114018964577)
      ·
        refine ⟨1494851455430335514223433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1993135273907114018964577 1494851455430335514223433)
        ·
          refine ⟨1121138591572751635667575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1494851455430335514223433 1121138591572751635667575)
          ·
            refine ⟨1681707887359127453501363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1121138591572751635667575 1681707887359127453501363)
            ·
              refine ⟨2522561831038691180252045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1681707887359127453501363 2522561831038691180252045)
              ·
                refine ⟨945960686639509192594517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2522561831038691180252045 945960686639509192594517)
                ·
                  refine ⟨11085476796556748350717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 945960686639509192594517 11085476796556748350717)
                  ·
                    rfl

theorem cell21_48575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 8].length) (baseStart_48575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_48575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_48575 prefixEnd_48575 := by exact prefixLift 48575
  have htrace : WordTrace (prefixWord ++ tailWord_48575) baseStart_48575 baseEnd_48575 := by
    simpa [prefixWord, tailWord_48575, baseEnd_48575] using wordTrace_append hprefix tailTrace_48575
  have hstable : (prefixWord ++ tailWord_48575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48575).length < 2 ^ (prefixWord ++ tailWord_48575).sum := by decide
  have hdescent : baseEnd_48575 < baseStart_48575 := by decide
  rcases family_descends (prefixWord ++ tailWord_48575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48775 : List Nat := [1, 1, 4, 2, 1, 5, 1, 6]
def baseStart_48775 : Nat := 118140960795 + 48775 * 2 ^ 59
def prefixEnd_48775 : Nat := 4983230072969 + 3 ^ 40 * 48775 * 2
def baseEnd_48775 : Nat := 3710373173800281672325

theorem tailTrace_48775 : CollatzResearch.WordTrace tailWord_48775 prefixEnd_48775 3710373173800281672325 := by
  unfold tailWord_48775
  simp only [CollatzResearch.WordTrace]
  refine ⟨1778970398303979951915779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1185980265535986634610519 1778970398303979951915779)
  ·
    refine ⟨2668455597455969927873669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1778970398303979951915779 2668455597455969927873669)
    ·
      refine ⟨500335424522994361476313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2668455597455969927873669 500335424522994361476313)
      ·
        refine ⟨375251568392245771107235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 500335424522994361476313 375251568392245771107235)
        ·
          refine ⟨562877352588368656660853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375251568392245771107235 562877352588368656660853)
          ·
            refine ⟨52769751805159561561955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 562877352588368656660853 52769751805159561561955)
            ·
              refine ⟨79154627707739342342933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52769751805159561561955 79154627707739342342933)
              ·
                refine ⟨3710373173800281672325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79154627707739342342933 3710373173800281672325)
                ·
                  rfl

theorem cell21_48775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 6].length) (baseStart_48775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_48775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_48775 prefixEnd_48775 := by exact prefixLift 48775
  have htrace : WordTrace (prefixWord ++ tailWord_48775) baseStart_48775 baseEnd_48775 := by
    simpa [prefixWord, tailWord_48775, baseEnd_48775] using wordTrace_append hprefix tailTrace_48775
  have hstable : (prefixWord ++ tailWord_48775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48775).length < 2 ^ (prefixWord ++ tailWord_48775).sum := by decide
  have hdescent : baseEnd_48775 < baseStart_48775 := by decide
  rcases family_descends (prefixWord ++ tailWord_48775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48803 : List Nat := [1, 1, 1, 4, 1, 1, 4, 2, 6]
def baseStart_48803 : Nat := 118140960795 + 48803 * 2 ^ 59
def prefixEnd_48803 : Nat := 4983230072969 + 3 ^ 40 * 48803 * 2
def baseEnd_48803 : Nat := 11137509502879018550251

theorem tailTrace_48803 : CollatzResearch.WordTrace tailWord_48803 prefixEnd_48803 11137509502879018550251 := by
  unfold tailWord_48803
  simp only [CollatzResearch.WordTrace]
  refine ⟨1779991642202540733935063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1186661094801693822623375 1779991642202540733935063)
  ·
    refine ⟨2669987463303811100902595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1779991642202540733935063 2669987463303811100902595)
    ·
      refine ⟨4004981194955716651353893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2669987463303811100902595 4004981194955716651353893)
      ·
        refine ⟨750933974054196872128855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4004981194955716651353893 750933974054196872128855)
        ·
          refine ⟨1126400961081295308193283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750933974054196872128855 1126400961081295308193283)
          ·
            refine ⟨1689601441621942962289925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1126400961081295308193283 1689601441621942962289925)
            ·
              refine ⟨316800270304114305429361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1689601441621942962289925 316800270304114305429361)
              ·
                refine ⟨237600202728085729072021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 316800270304114305429361 237600202728085729072021)
                ·
                  refine ⟨11137509502879018550251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 237600202728085729072021 11137509502879018550251)
                  ·
                    rfl

theorem cell21_48803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 6].length) (baseStart_48803 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_48803 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_48803 prefixEnd_48803 := by exact prefixLift 48803
  have htrace : WordTrace (prefixWord ++ tailWord_48803) baseStart_48803 baseEnd_48803 := by
    simpa [prefixWord, tailWord_48803, baseEnd_48803] using wordTrace_append hprefix tailTrace_48803
  have hstable : (prefixWord ++ tailWord_48803).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48803).length < 2 ^ (prefixWord ++ tailWord_48803).sum := by decide
  have hdescent : baseEnd_48803 < baseStart_48803 := by decide
  rcases family_descends (prefixWord ++ tailWord_48803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48848 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 7]
def baseStart_48848 : Nat := 118140960795 + 48848 * 2 ^ 59
def prefixEnd_48848 : Nat := 4983230072969 + 3 ^ 40 * 48848 * 2
def baseEnd_48848 : Nat := 11147779115968940300159

theorem tailTrace_48848 : CollatzResearch.WordTrace tailWord_48848 prefixEnd_48848 11147779115968940300159 := by
  unfold tailWord_48848
  simp only [CollatzResearch.WordTrace]
  refine ⟨890816463519756709661599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1187755284693008946215465 890816463519756709661599)
  ·
    refine ⟨1336224695279635064492399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 890816463519756709661599 1336224695279635064492399)
    ·
      refine ⟨2004337042919452596738599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1336224695279635064492399 2004337042919452596738599)
      ·
        refine ⟨3006505564379178895107899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2004337042919452596738599 3006505564379178895107899)
        ·
          refine ⟨4509758346568768342661849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3006505564379178895107899 4509758346568768342661849)
          ·
            refine ⟨3382318759926576256996387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4509758346568768342661849 3382318759926576256996387)
            ·
              refine ⟨5073478139889864385494581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3382318759926576256996387 5073478139889864385494581)
              ·
                refine ⟨475638575614674786140117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5073478139889864385494581 475638575614674786140117)
                ·
                  refine ⟨11147779115968940300159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 475638575614674786140117 11147779115968940300159)
                  ·
                    rfl

theorem cell21_48848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 7].length) (baseStart_48848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_48848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_48848 prefixEnd_48848 := by exact prefixLift 48848
  have htrace : WordTrace (prefixWord ++ tailWord_48848) baseStart_48848 baseEnd_48848 := by
    simpa [prefixWord, tailWord_48848, baseEnd_48848] using wordTrace_append hprefix tailTrace_48848
  have hstable : (prefixWord ++ tailWord_48848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48848).length < 2 ^ (prefixWord ++ tailWord_48848).sum := by decide
  have hdescent : baseEnd_48848 < baseStart_48848 := by decide
  rcases family_descends (prefixWord ++ tailWord_48848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48879 : List Nat := [1, 1, 2, 1, 5, 1, 1, 3, 6]
def baseStart_48879 : Nat := 118140960795 + 48879 * 2 ^ 59
def prefixEnd_48879 : Nat := 4983230072969 + 3 ^ 40 * 48879 * 2
def baseEnd_48879 : Nat := 11154853738319775283429

theorem tailTrace_48879 : CollatzResearch.WordTrace tailWord_48879 prefixEnd_48879 11154853738319775283429 := by
  unfold tailWord_48879
  simp only [CollatzResearch.WordTrace]
  refine ⟨1782763589927205713701691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1188509059951470475801127 1782763589927205713701691)
  ·
    refine ⟨2674145384890808570552537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1782763589927205713701691 2674145384890808570552537)
    ·
      refine ⟨2005609038668106427914403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2674145384890808570552537 2005609038668106427914403)
      ·
        refine ⟨3008413558002159641871605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2005609038668106427914403 3008413558002159641871605)
        ·
          refine ⟨282038771062702466425463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3008413558002159641871605 282038771062702466425463)
          ·
            refine ⟨423058156594053699638195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282038771062702466425463 423058156594053699638195)
            ·
              refine ⟨634587234891080549457293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423058156594053699638195 634587234891080549457293)
              ·
                refine ⟨237970213084155206046485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 634587234891080549457293 237970213084155206046485)
                ·
                  refine ⟨11154853738319775283429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 237970213084155206046485 11154853738319775283429)
                  ·
                    rfl

theorem cell21_48879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 6].length) (baseStart_48879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_48879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_48879 prefixEnd_48879 := by exact prefixLift 48879
  have htrace : WordTrace (prefixWord ++ tailWord_48879) baseStart_48879 baseEnd_48879 := by
    simpa [prefixWord, tailWord_48879, baseEnd_48879] using wordTrace_append hprefix tailTrace_48879
  have hstable : (prefixWord ++ tailWord_48879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48879).length < 2 ^ (prefixWord ++ tailWord_48879).sum := by decide
  have hdescent : baseEnd_48879 < baseStart_48879 := by decide
  rcases family_descends (prefixWord ++ tailWord_48879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48910 : List Nat := [4, 1, 1, 2, 1, 1, 4, 7]
def baseStart_48910 : Nat := 118140960795 + 48910 * 2 ^ 59
def prefixEnd_48910 : Nat := 4983230072969 + 3 ^ 40 * 48910 * 2
def baseEnd_48910 : Nat := 3720642786890203422233

theorem tailTrace_48910 : CollatzResearch.WordTrace tailWord_48910 prefixEnd_48910 3720642786890203422233 := by
  unfold tailWord_48910
  simp only [CollatzResearch.WordTrace]
  refine ⟨222986781601862251010023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1189262835209932005386789 222986781601862251010023)
  ·
    refine ⟨334480172402793376515035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222986781601862251010023 334480172402793376515035)
    ·
      refine ⟨501720258604190064772553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334480172402793376515035 501720258604190064772553)
      ·
        refine ⟨376290193953142548579415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 501720258604190064772553 376290193953142548579415)
        ·
          refine ⟨564435290929713822869123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376290193953142548579415 564435290929713822869123)
          ·
            refine ⟨846652936394570734303685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564435290929713822869123 846652936394570734303685)
            ·
              refine ⟨158747425573982012681941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 846652936394570734303685 158747425573982012681941)
              ·
                refine ⟨3720642786890203422233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 158747425573982012681941 3720642786890203422233)
                ·
                  rfl

theorem cell21_48910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_48910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_48910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_48910 prefixEnd_48910 := by exact prefixLift 48910
  have htrace : WordTrace (prefixWord ++ tailWord_48910) baseStart_48910 baseEnd_48910 := by
    simpa [prefixWord, tailWord_48910, baseEnd_48910] using wordTrace_append hprefix tailTrace_48910
  have hstable : (prefixWord ++ tailWord_48910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48910).length < 2 ^ (prefixWord ++ tailWord_48910).sum := by decide
  have hdescent : baseEnd_48910 < baseStart_48910 := by decide
  rcases family_descends (prefixWord ++ tailWord_48910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48958 : List Nat := [4, 2, 1, 2, 2, 2, 1, 2, 5]
def baseStart_48958 : Nat := 118140960795 + 48958 * 2 ^ 59
def prefixEnd_48958 : Nat := 4983230072969 + 3 ^ 40 * 48958 * 2
def baseEnd_48958 : Nat := 11172882614633193466601

theorem tailTrace_48958 : CollatzResearch.WordTrace tailWord_48958 prefixEnd_48958 11172882614633193466601 := by
  unfold tailWord_48958
  simp only [CollatzResearch.WordTrace]
  refine ⟨223205619580125275728441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1190429971094001470551685 223205619580125275728441)
  ·
    refine ⟨167404214685093956796331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223205619580125275728441 167404214685093956796331)
    ·
      refine ⟨251106322027640935194497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167404214685093956796331 251106322027640935194497)
      ·
        refine ⟨188329741520730701395873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251106322027640935194497 188329741520730701395873)
        ·
          refine ⟨141247306140548026046905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188329741520730701395873 141247306140548026046905)
          ·
            refine ⟨105935479605411019535179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141247306140548026046905 105935479605411019535179)
            ·
              refine ⟨158903219408116529302769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105935479605411019535179 158903219408116529302769)
              ·
                refine ⟨119177414556087396977077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158903219408116529302769 119177414556087396977077)
                ·
                  refine ⟨11172882614633193466601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119177414556087396977077 11172882614633193466601)
                  ·
                    rfl

theorem cell21_48958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_48958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_48958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_48958 prefixEnd_48958 := by exact prefixLift 48958
  have htrace : WordTrace (prefixWord ++ tailWord_48958) baseStart_48958 baseEnd_48958 := by
    simpa [prefixWord, tailWord_48958, baseEnd_48958] using wordTrace_append hprefix tailTrace_48958
  have hstable : (prefixWord ++ tailWord_48958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48958).length < 2 ^ (prefixWord ++ tailWord_48958).sum := by decide
  have hdescent : baseEnd_48958 < baseStart_48958 := by decide
  rcases family_descends (prefixWord ++ tailWord_48958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49006 : List Nat := [4, 1, 2, 3, 1, 2, 3, 1, 4]
def baseStart_49006 : Nat := 118140960795 + 49006 * 2 ^ 59
def prefixEnd_49006 : Nat := 4983230072969 + 3 ^ 40 * 49006 * 2
def baseEnd_49006 : Nat := 11183836868595776666503

theorem tailTrace_49006 : CollatzResearch.WordTrace tailWord_49006 prefixEnd_49006 11183836868595776666503 := by
  unfold tailWord_49006
  simp only [CollatzResearch.WordTrace]
  refine ⟨223424457558388300446859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1191597106978070935716581 223424457558388300446859)
  ·
    refine ⟨335136686337582450670289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223424457558388300446859 335136686337582450670289)
    ·
      refine ⟨251352514753186838002717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335136686337582450670289 251352514753186838002717)
      ·
        refine ⟨94257193032445064251019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251352514753186838002717 94257193032445064251019)
        ·
          refine ⟨141385789548667596376529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94257193032445064251019 141385789548667596376529)
          ·
            refine ⟨106039342161500697282397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141385789548667596376529 106039342161500697282397)
            ·
              refine ⟨39764753310562761480899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106039342161500697282397 39764753310562761480899)
              ·
                refine ⟨59647129965844142221349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39764753310562761480899 59647129965844142221349)
                ·
                  refine ⟨11183836868595776666503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59647129965844142221349 11183836868595776666503)
                  ·
                    rfl

theorem cell21_49006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_49006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_49006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_49006 prefixEnd_49006 := by exact prefixLift 49006
  have htrace : WordTrace (prefixWord ++ tailWord_49006) baseStart_49006 baseEnd_49006 := by
    simpa [prefixWord, tailWord_49006, baseEnd_49006] using wordTrace_append hprefix tailTrace_49006
  have hstable : (prefixWord ++ tailWord_49006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49006).length < 2 ^ (prefixWord ++ tailWord_49006).sum := by decide
  have hdescent : baseEnd_49006 < baseStart_49006 := by decide
  rcases family_descends (prefixWord ++ tailWord_49006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49234 : List Nat := [3, 2, 2, 1, 4, 2, 2, 1, 4]
def baseStart_49234 : Nat := 118140960795 + 49234 * 2 ^ 59
def prefixEnd_49234 : Nat := 4983230072969 + 3 ^ 40 * 49234 * 2
def baseEnd_49234 : Nat := 11235869574918046866037

theorem tailTrace_49234 : CollatzResearch.WordTrace tailWord_49234 prefixEnd_49234 11235869574918046866037 := by
  unfold tailWord_49234
  simp only [CollatzResearch.WordTrace]
  refine ⟨448927875910275335718689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1197141002427400895249837 448927875910275335718689)
  ·
    refine ⟨336695906932706501789017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 448927875910275335718689 336695906932706501789017)
    ·
      refine ⟨252521930199529876341763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336695906932706501789017 252521930199529876341763)
      ·
        refine ⟨378782895299294814512645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252521930199529876341763 378782895299294814512645)
        ·
          refine ⟨71021792868617777721121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 378782895299294814512645 71021792868617777721121)
          ·
            refine ⟨53266344651463333290841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71021792868617777721121 53266344651463333290841)
            ·
              refine ⟨39949758488597499968131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53266344651463333290841 39949758488597499968131)
              ·
                refine ⟨59924637732896249952197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39949758488597499968131 59924637732896249952197)
                ·
                  refine ⟨11235869574918046866037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59924637732896249952197 11235869574918046866037)
                  ·
                    rfl

theorem cell21_49234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_49234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_49234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_49234 prefixEnd_49234 := by exact prefixLift 49234
  have htrace : WordTrace (prefixWord ++ tailWord_49234) baseStart_49234 baseEnd_49234 := by
    simpa [prefixWord, tailWord_49234, baseEnd_49234] using wordTrace_append hprefix tailTrace_49234
  have hstable : (prefixWord ++ tailWord_49234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49234).length < 2 ^ (prefixWord ++ tailWord_49234).sum := by decide
  have hdescent : baseEnd_49234 < baseStart_49234 := by decide
  rcases family_descends (prefixWord ++ tailWord_49234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49262 : List Nat := [4, 1, 2, 2, 1, 1, 2, 5, 3]
def baseStart_49262 : Nat := 118140960795 + 49262 * 2 ^ 59
def prefixEnd_49262 : Nat := 4983230072969 + 3 ^ 40 * 49262 * 2
def baseEnd_49262 : Nat := 11242259556396220399313

theorem tailTrace_49262 : CollatzResearch.WordTrace tailWord_49262 prefixEnd_49262 11242259556396220399313 := by
  unfold tailWord_49262
  simp only [CollatzResearch.WordTrace]
  refine ⟨224591593442457765611755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1197821831693108083262693 224591593442457765611755)
  ·
    refine ⟨336887390163686648417633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224591593442457765611755 336887390163686648417633)
    ·
      refine ⟨252665542622764986313225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336887390163686648417633 252665542622764986313225)
      ·
        refine ⟨189499156967073739734919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252665542622764986313225 189499156967073739734919)
        ·
          refine ⟨284248735450610609602379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189499156967073739734919 284248735450610609602379)
          ·
            refine ⟨426373103175915914403569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284248735450610609602379 426373103175915914403569)
            ·
              refine ⟨319779827381936935802677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 426373103175915914403569 319779827381936935802677)
              ·
                refine ⟨29979358817056587731501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 319779827381936935802677 29979358817056587731501)
                ·
                  refine ⟨11242259556396220399313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29979358817056587731501 11242259556396220399313)
                  ·
                    rfl

theorem cell21_49262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_49262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_49262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_49262 prefixEnd_49262 := by exact prefixLift 49262
  have htrace : WordTrace (prefixWord ++ tailWord_49262) baseStart_49262 baseEnd_49262 := by
    simpa [prefixWord, tailWord_49262, baseEnd_49262] using wordTrace_append hprefix tailTrace_49262
  have hstable : (prefixWord ++ tailWord_49262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49262).length < 2 ^ (prefixWord ++ tailWord_49262).sum := by decide
  have hdescent : baseEnd_49262 < baseStart_49262 := by decide
  rcases family_descends (prefixWord ++ tailWord_49262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49273 : List Nat := [1, 2, 1, 3, 4, 10]
def baseStart_49273 : Nat := 118140960795 + 49273 * 2 ^ 59
def prefixEnd_49273 : Nat := 4983230072969 + 3 ^ 40 * 49273 * 2
def baseEnd_49273 : Nat := 416472959491209100591

theorem tailTrace_49273 : CollatzResearch.WordTrace tailWord_49273 prefixEnd_49273 416472959491209100591 := by
  unfold tailWord_49273
  simp only [CollatzResearch.WordTrace]
  refine ⟨1797133950499811003544473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1198089300333207335696315 1797133950499811003544473)
  ·
    refine ⟨1347850462874858252658355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1797133950499811003544473 1347850462874858252658355)
    ·
      refine ⟨2021775694312287378987533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1347850462874858252658355 2021775694312287378987533)
      ·
        refine ⟨758165885367107767120325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2021775694312287378987533 758165885367107767120325)
        ·
          refine ⟨142156103506332706335061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 758165885367107767120325 142156103506332706335061)
          ·
            refine ⟨416472959491209100591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 142156103506332706335061 416472959491209100591)
            ·
              rfl

theorem cell21_49273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 10].length) (baseStart_49273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_49273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_49273 prefixEnd_49273 := by exact prefixLift 49273
  have htrace : WordTrace (prefixWord ++ tailWord_49273) baseStart_49273 baseEnd_49273 := by
    simpa [prefixWord, tailWord_49273, baseEnd_49273] using wordTrace_append hprefix tailTrace_49273
  have hstable : (prefixWord ++ tailWord_49273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49273).length < 2 ^ (prefixWord ++ tailWord_49273).sum := by decide
  have hdescent : baseEnd_49273 < baseStart_49273 := by decide
  rcases family_descends (prefixWord ++ tailWord_49273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49276 : List Nat := [2, 2, 2, 1, 1, 5, 2, 2, 4]
def baseStart_49276 : Nat := 118140960795 + 49276 * 2 ^ 59
def prefixEnd_49276 : Nat := 4983230072969 + 3 ^ 40 * 49276 * 2
def baseEnd_49276 : Nat := 11245454547135307165951

theorem tailTrace_49276 : CollatzResearch.WordTrace tailWord_49276 prefixEnd_49276 11245454547135307165951 := by
  unfold tailWord_49276
  simp only [CollatzResearch.WordTrace]
  refine ⟨898621684744471257951841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1198162246325961677269121 898621684744471257951841)
  ·
    refine ⟨673966263558353443463881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 898621684744471257951841 673966263558353443463881)
    ·
      refine ⟨505474697668765082597911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 673966263558353443463881 505474697668765082597911)
      ·
        refine ⟨758212046503147623896867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505474697668765082597911 758212046503147623896867)
        ·
          refine ⟨1137318069754721435845301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758212046503147623896867 1137318069754721435845301)
          ·
            refine ⟨106623569039505134610497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1137318069754721435845301 106623569039505134610497)
            ·
              refine ⟨79967676779628850957873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106623569039505134610497 79967676779628850957873)
              ·
                refine ⟨59975757584721638218405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79967676779628850957873 59975757584721638218405)
                ·
                  refine ⟨11245454547135307165951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59975757584721638218405 11245454547135307165951)
                  ·
                    rfl

theorem cell21_49276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_49276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_49276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_49276 prefixEnd_49276 := by exact prefixLift 49276
  have htrace : WordTrace (prefixWord ++ tailWord_49276) baseStart_49276 baseEnd_49276 := by
    simpa [prefixWord, tailWord_49276, baseEnd_49276] using wordTrace_append hprefix tailTrace_49276
  have hstable : (prefixWord ++ tailWord_49276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49276).length < 2 ^ (prefixWord ++ tailWord_49276).sum := by decide
  have hdescent : baseEnd_49276 < baseStart_49276 := by decide
  rcases family_descends (prefixWord ++ tailWord_49276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49290 : List Nat := [3, 1, 2, 3, 1, 2, 3, 6]
def baseStart_49290 : Nat := 118140960795 + 49290 * 2 ^ 59
def prefixEnd_49290 : Nat := 4983230072969 + 3 ^ 40 * 49290 * 2
def baseEnd_49290 : Nat := 3749549845958131310863

theorem tailTrace_49290 : CollatzResearch.WordTrace tailWord_49290 prefixEnd_49290 3749549845958131310863 := by
  unfold tailWord_49290
  simp only [CollatzResearch.WordTrace]
  refine ⟨449438497859555726728331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1198502660958815271275549 449438497859555726728331)
  ·
    refine ⟨674157746789333590092497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 449438497859555726728331 674157746789333590092497)
    ·
      refine ⟨505618310092000192569373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 674157746789333590092497 505618310092000192569373)
      ·
        refine ⟨189606866284500072213515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 505618310092000192569373 189606866284500072213515)
        ·
          refine ⟨284410299426750108320273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189606866284500072213515 284410299426750108320273)
          ·
            refine ⟨213307724570062581240205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284410299426750108320273 213307724570062581240205)
            ·
              refine ⟨79990396713773467965077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213307724570062581240205 79990396713773467965077)
              ·
                refine ⟨3749549845958131310863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79990396713773467965077 3749549845958131310863)
                ·
                  rfl

theorem cell21_49290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 6].length) (baseStart_49290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_49290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_49290 prefixEnd_49290 := by exact prefixLift 49290
  have htrace : WordTrace (prefixWord ++ tailWord_49290) baseStart_49290 baseEnd_49290 := by
    simpa [prefixWord, tailWord_49290, baseEnd_49290] using wordTrace_append hprefix tailTrace_49290
  have hstable : (prefixWord ++ tailWord_49290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49290).length < 2 ^ (prefixWord ++ tailWord_49290).sum := by decide
  have hdescent : baseEnd_49290 < baseStart_49290 := by decide
  rcases family_descends (prefixWord ++ tailWord_49290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49335 : List Nat := [1, 1, 3, 1, 4, 3, 1, 1, 6]
def baseStart_49335 : Nat := 118140960795 + 49335 * 2 ^ 59
def prefixEnd_49335 : Nat := 4983230072969 + 3 ^ 40 * 49335 * 2
def baseEnd_49335 : Nat := 11258919150964315682497

theorem tailTrace_49335 : CollatzResearch.WordTrace tailWord_49335 prefixEnd_49335 11258919150964315682497 := by
  unfold tailWord_49335
  simp only [CollatzResearch.WordTrace]
  refine ⟨1799395276275195592301459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1199596850850130394867639 1799395276275195592301459)
  ·
    refine ⟨2699092914412793388452189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1799395276275195592301459 2699092914412793388452189)
    ·
      refine ⟨1012159842904797520669571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2699092914412793388452189 1012159842904797520669571)
      ·
        refine ⟨1518239764357196281004357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1012159842904797520669571 1518239764357196281004357)
        ·
          refine ⟨284669955816974302688317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1518239764357196281004357 284669955816974302688317)
          ·
            refine ⟨106751233431365363508119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284669955816974302688317 106751233431365363508119)
            ·
              refine ⟨160126850147048045262179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106751233431365363508119 160126850147048045262179)
              ·
                refine ⟨240190275220572067893269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160126850147048045262179 240190275220572067893269)
                ·
                  refine ⟨11258919150964315682497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 240190275220572067893269 11258919150964315682497)
                  ·
                    rfl

theorem cell21_49335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 6].length) (baseStart_49335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_49335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_49335 prefixEnd_49335 := by exact prefixLift 49335
  have htrace : WordTrace (prefixWord ++ tailWord_49335) baseStart_49335 baseEnd_49335 := by
    simpa [prefixWord, tailWord_49335, baseEnd_49335] using wordTrace_append hprefix tailTrace_49335
  have hstable : (prefixWord ++ tailWord_49335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49335).length < 2 ^ (prefixWord ++ tailWord_49335).sum := by decide
  have hdescent : baseEnd_49335 < baseStart_49335 := by decide
  rcases family_descends (prefixWord ++ tailWord_49335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49411 : List Nat := [1, 1, 1, 3, 2, 3, 3, 3, 4]
def baseStart_49411 : Nat := 118140960795 + 49411 * 2 ^ 59
def prefixEnd_49411 : Nat := 4983230072969 + 3 ^ 40 * 49411 * 2
def baseEnd_49411 : Nat := 11276263386405072415675

theorem tailTrace_49411 : CollatzResearch.WordTrace tailWord_49411 prefixEnd_49411 11276263386405072415675 := by
  unfold tailWord_49411
  simp only [CollatzResearch.WordTrace]
  refine ⟨1802167223999860572068087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1201444815999907048045391 1802167223999860572068087)
  ·
    refine ⟨2703250835999790858102131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1802167223999860572068087 2703250835999790858102131)
    ·
      refine ⟨4054876253999686287153197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2703250835999790858102131 4054876253999686287153197)
      ·
        refine ⟨1520578595249882357682449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4054876253999686287153197 1520578595249882357682449)
        ·
          refine ⟨1140433946437411768261837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1520578595249882357682449 1140433946437411768261837)
          ·
            refine ⟨427662729914029413098189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1140433946437411768261837 427662729914029413098189)
            ·
              refine ⟨160373523717761029911821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 427662729914029413098189 160373523717761029911821)
              ·
                refine ⟨60140071394160386216933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160373523717761029911821 60140071394160386216933)
                ·
                  refine ⟨11276263386405072415675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60140071394160386216933 11276263386405072415675)
                  ·
                    rfl

theorem cell21_49411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 4].length) (baseStart_49411 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_49411 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_49411 prefixEnd_49411 := by exact prefixLift 49411
  have htrace : WordTrace (prefixWord ++ tailWord_49411) baseStart_49411 baseEnd_49411 := by
    simpa [prefixWord, tailWord_49411, baseEnd_49411] using wordTrace_append hprefix tailTrace_49411
  have hstable : (prefixWord ++ tailWord_49411).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49411).length < 2 ^ (prefixWord ++ tailWord_49411).sum := by decide
  have hdescent : baseEnd_49411 < baseStart_49411 := by decide
  rcases family_descends (prefixWord ++ tailWord_49411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49425 : List Nat := [1, 2, 2, 1, 1, 5, 2, 7]
def baseStart_49425 : Nat := 118140960795 + 49425 * 2 ^ 59
def prefixEnd_49425 : Nat := 4983230072969 + 3 ^ 40 * 49425 * 2
def baseEnd_49425 : Nat := 3759819459048053060771

theorem tailTrace_49425 : CollatzResearch.WordTrace tailWord_49425 prefixEnd_49425 3759819459048053060771 := by
  unfold tailWord_49425
  simp only [CollatzResearch.WordTrace]
  refine ⟨1802677845949140963077729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1201785230632760642051819 1802677845949140963077729)
  ·
    refine ⟨1352008384461855722308297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1802677845949140963077729 1352008384461855722308297)
    ·
      refine ⟨1014006288346391791731223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1352008384461855722308297 1014006288346391791731223)
      ·
        refine ⟨1521009432519587687596835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1014006288346391791731223 1521009432519587687596835)
        ·
          refine ⟨2281514148779381531395253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1521009432519587687596835 2281514148779381531395253)
          ·
            refine ⟨213891951448067018568305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2281514148779381531395253 213891951448067018568305)
            ·
              refine ⟨160418963586050263926229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213891951448067018568305 160418963586050263926229)
              ·
                refine ⟨3759819459048053060771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 160418963586050263926229 3759819459048053060771)
                ·
                  rfl

theorem cell21_49425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 7].length) (baseStart_49425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_49425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_49425 prefixEnd_49425 := by exact prefixLift 49425
  have htrace : WordTrace (prefixWord ++ tailWord_49425) baseStart_49425 baseEnd_49425 := by
    simpa [prefixWord, tailWord_49425, baseEnd_49425] using wordTrace_append hprefix tailTrace_49425
  have hstable : (prefixWord ++ tailWord_49425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49425).length < 2 ^ (prefixWord ++ tailWord_49425).sum := by decide
  have hdescent : baseEnd_49425 < baseStart_49425 := by decide
  rcases family_descends (prefixWord ++ tailWord_49425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49448 : List Nat := [2, 1, 5, 1, 3, 2, 2, 2, 3]
def baseStart_49448 : Nat := 118140960795 + 49448 * 2 ^ 59
def prefixEnd_49448 : Nat := 4983230072969 + 3 ^ 40 * 49448 * 2
def baseEnd_49448 : Nat := 11284707290501230298933

theorem tailTrace_49448 : CollatzResearch.WordTrace tailWord_49448 prefixEnd_49448 11284707290501230298933 := by
  unfold tailWord_49448
  simp only [CollatzResearch.WordTrace]
  refine ⟨901758362432907945582499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1202344483243877260776665 901758362432907945582499)
  ·
    refine ⟨1352637543649361918373749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 901758362432907945582499 1352637543649361918373749)
    ·
      refine ⟨126809769717127679847539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1352637543649361918373749 126809769717127679847539)
      ·
        refine ⟨190214654575691519771309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126809769717127679847539 190214654575691519771309)
        ·
          refine ⟨71330495465884319914241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190214654575691519771309 71330495465884319914241)
          ·
            refine ⟨53497871599413239935681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71330495465884319914241 53497871599413239935681)
            ·
              refine ⟨40123403699559929951761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53497871599413239935681 40123403699559929951761)
              ·
                refine ⟨30092552774669947463821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40123403699559929951761 30092552774669947463821)
                ·
                  refine ⟨11284707290501230298933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30092552774669947463821 11284707290501230298933)
                  ·
                    rfl

theorem cell21_49448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2, 3].length) (baseStart_49448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_49448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_49448 prefixEnd_49448 := by exact prefixLift 49448
  have htrace : WordTrace (prefixWord ++ tailWord_49448) baseStart_49448 baseEnd_49448 := by
    simpa [prefixWord, tailWord_49448, baseEnd_49448] using wordTrace_append hprefix tailTrace_49448
  have hstable : (prefixWord ++ tailWord_49448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49448).length < 2 ^ (prefixWord ++ tailWord_49448).sum := by decide
  have hdescent : baseEnd_49448 < baseStart_49448 := by decide
  rcases family_descends (prefixWord ++ tailWord_49448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49476 : List Nat := [2, 3, 4, 1, 2, 1, 3, 5]
def baseStart_49476 : Nat := 118140960795 + 49476 * 2 ^ 59
def prefixEnd_49476 : Nat := 4983230072969 + 3 ^ 40 * 49476 * 2
def baseEnd_49476 : Nat := 3763699090659801277403

theorem tailTrace_49476 : CollatzResearch.WordTrace tailWord_49476 prefixEnd_49476 3763699090659801277403 := by
  unfold tailWord_49476
  simp only [CollatzResearch.WordTrace]
  refine ⟨902268984382188336592141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1203025312509584448789521 902268984382188336592141)
  ·
    refine ⟨338350869143320626222053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 902268984382188336592141 338350869143320626222053)
    ·
      refine ⟨63440787964372617416635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 338350869143320626222053 63440787964372617416635)
      ·
        refine ⟨95161181946558926124953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63440787964372617416635 95161181946558926124953)
        ·
          refine ⟨71370886459919194593715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95161181946558926124953 71370886459919194593715)
          ·
            refine ⟨107056329689878791890573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71370886459919194593715 107056329689878791890573)
            ·
              refine ⟨40146123633704546958965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107056329689878791890573 40146123633704546958965)
              ·
                refine ⟨3763699090659801277403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40146123633704546958965 3763699090659801277403)
                ·
                  rfl

theorem cell21_49476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 5].length) (baseStart_49476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_49476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_49476 prefixEnd_49476 := by exact prefixLift 49476
  have htrace : WordTrace (prefixWord ++ tailWord_49476) baseStart_49476 baseEnd_49476 := by
    simpa [prefixWord, tailWord_49476, baseEnd_49476] using wordTrace_append hprefix tailTrace_49476
  have hstable : (prefixWord ++ tailWord_49476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49476).length < 2 ^ (prefixWord ++ tailWord_49476).sum := by decide
  have hdescent : baseEnd_49476 < baseStart_49476 := by decide
  rcases family_descends (prefixWord ++ tailWord_49476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49515 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 9]
def baseStart_49515 : Nat := 118140960795 + 49515 * 2 ^ 59
def prefixEnd_49515 : Nat := 4983230072969 + 3 ^ 40 * 49515 * 2
def baseEnd_49515 : Nat := 11299997603324002682129

theorem tailTrace_49515 : CollatzResearch.WordTrace tailWord_49515 prefixEnd_49515 11299997603324002682129 := by
  unfold tailWord_49515
  simp only [CollatzResearch.WordTrace]
  refine ⟨1805960415623086333853999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1203973610415390889235999 1805960415623086333853999)
  ·
    refine ⟨2708940623434629500780999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1805960415623086333853999 2708940623434629500780999)
    ·
      refine ⟨4063410935151944251171499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2708940623434629500780999 4063410935151944251171499)
      ·
        refine ⟨6095116402727916376757249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4063410935151944251171499 6095116402727916376757249)
        ·
          refine ⟨4571337302045937282567937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6095116402727916376757249 4571337302045937282567937)
          ·
            refine ⟨3428502976534452961925953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4571337302045937282567937 3428502976534452961925953)
            ·
              refine ⟨2571377232400839721444465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3428502976534452961925953 2571377232400839721444465)
              ·
                refine ⟨1928532924300629791083349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2571377232400839721444465 1928532924300629791083349)
                ·
                  refine ⟨11299997603324002682129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1928532924300629791083349 11299997603324002682129)
                  ·
                    rfl

theorem cell21_49515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 9].length) (baseStart_49515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_49515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_49515 prefixEnd_49515 := by exact prefixLift 49515
  have htrace : WordTrace (prefixWord ++ tailWord_49515) baseStart_49515 baseEnd_49515 := by
    simpa [prefixWord, tailWord_49515, baseEnd_49515] using wordTrace_append hprefix tailTrace_49515
  have hstable : (prefixWord ++ tailWord_49515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49515).length < 2 ^ (prefixWord ++ tailWord_49515).sum := by decide
  have hdescent : baseEnd_49515 < baseStart_49515 := by decide
  rcases family_descends (prefixWord ++ tailWord_49515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49558 : List Nat := [5, 3, 1, 2, 1, 1, 3, 2, 3]
def baseStart_49558 : Nat := 118140960795 + 49558 * 2 ^ 59
def prefixEnd_49558 : Nat := 4983230072969 + 3 ^ 40 * 49558 * 2
def baseEnd_49558 : Nat := 11309810789165483465375

theorem tailTrace_49558 : CollatzResearch.WordTrace tailWord_49558 prefixEnd_49558 11309810789165483465375 := by
  unfold tailWord_49558
  simp only [CollatzResearch.WordTrace]
  refine ⟨112970547154206542354333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1205019169644869785112885 112970547154206542354333)
  ·
    refine ⟨42363955182827453382875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112970547154206542354333 42363955182827453382875)
    ·
      refine ⟨63545932774241180074313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42363955182827453382875 63545932774241180074313)
      ·
        refine ⟨47659449580680885055735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63545932774241180074313 47659449580680885055735)
        ·
          refine ⟨71489174371021327583603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47659449580680885055735 71489174371021327583603)
          ·
            refine ⟨107233761556531991375405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71489174371021327583603 107233761556531991375405)
            ·
              refine ⟨40212660583699496765777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107233761556531991375405 40212660583699496765777)
              ·
                refine ⟨30159495437774622574333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40212660583699496765777 30159495437774622574333)
                ·
                  refine ⟨11309810789165483465375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30159495437774622574333 11309810789165483465375)
                  ·
                    rfl

theorem cell21_49558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_49558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_49558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_49558 prefixEnd_49558 := by exact prefixLift 49558
  have htrace : WordTrace (prefixWord ++ tailWord_49558) baseStart_49558 baseEnd_49558 := by
    simpa [prefixWord, tailWord_49558, baseEnd_49558] using wordTrace_append hprefix tailTrace_49558
  have hstable : (prefixWord ++ tailWord_49558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49558).length < 2 ^ (prefixWord ++ tailWord_49558).sum := by decide
  have hdescent : baseEnd_49558 < baseStart_49558 := by decide
  rcases family_descends (prefixWord ++ tailWord_49558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49566 : List Nat := [4, 3, 1, 2, 1, 1, 3, 1, 5]
def baseStart_49566 : Nat := 118140960795 + 49566 * 2 ^ 59
def prefixEnd_49566 : Nat := 4983230072969 + 3 ^ 40 * 49566 * 2
def baseEnd_49566 : Nat := 11311636498159247332025

theorem tailTrace_49566 : CollatzResearch.WordTrace tailWord_49566 prefixEnd_49566 11311636498159247332025 := by
  unfold tailWord_49566
  simp only [CollatzResearch.WordTrace]
  refine ⟨225977567304790255495069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1205213692292214695973701 225977567304790255495069)
  ·
    refine ⟨84741587739296345810651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225977567304790255495069 84741587739296345810651)
    ·
      refine ⟨127112381608944518715977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84741587739296345810651 127112381608944518715977)
      ·
        refine ⟨95334286206708389036983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127112381608944518715977 95334286206708389036983)
        ·
          refine ⟨143001429310062583555475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95334286206708389036983 143001429310062583555475)
          ·
            refine ⟨214502143965093875333213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143001429310062583555475 214502143965093875333213)
            ·
              refine ⟨80438303986910203249955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214502143965093875333213 80438303986910203249955)
              ·
                refine ⟨120657455980365304874933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80438303986910203249955 120657455980365304874933)
                ·
                  refine ⟨11311636498159247332025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120657455980365304874933 11311636498159247332025)
                  ·
                    rfl

theorem cell21_49566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_49566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_49566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_49566 prefixEnd_49566 := by exact prefixLift 49566
  have htrace : WordTrace (prefixWord ++ tailWord_49566) baseStart_49566 baseEnd_49566 := by
    simpa [prefixWord, tailWord_49566, baseEnd_49566] using wordTrace_append hprefix tailTrace_49566
  have hstable : (prefixWord ++ tailWord_49566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49566).length < 2 ^ (prefixWord ++ tailWord_49566).sum := by decide
  have hdescent : baseEnd_49566 < baseStart_49566 := by decide
  rcases family_descends (prefixWord ++ tailWord_49566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49625 : List Nat := [1, 2, 1, 2, 4, 1, 3, 4, 3]
def baseStart_49625 : Nat := 118140960795 + 49625 * 2 ^ 59
def prefixEnd_49625 : Nat := 4983230072969 + 3 ^ 40 * 49625 * 2
def baseEnd_49625 : Nat := 11325101101988255848571

theorem tailTrace_49625 : CollatzResearch.WordTrace tailWord_49625 prefixEnd_49625 11325101101988255848571 := by
  unfold tailWord_49625
  simp only [CollatzResearch.WordTrace]
  refine ⟨1809972445224575120358329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1206648296816383413572219 1809972445224575120358329)
  ·
    refine ⟨1357479333918431340268747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1809972445224575120358329 1357479333918431340268747)
    ·
      refine ⟨2036219000877647010403121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1357479333918431340268747 2036219000877647010403121)
      ·
        refine ⟨1527164250658235257802341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2036219000877647010403121 1527164250658235257802341)
        ·
          refine ⟨286343296998419110837939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1527164250658235257802341 286343296998419110837939)
          ·
            refine ⟨429514945497628666256909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286343296998419110837939 429514945497628666256909)
            ·
              refine ⟨161068104561610749846341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 429514945497628666256909 161068104561610749846341)
              ·
                refine ⟨30200269605302015596189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161068104561610749846341 30200269605302015596189)
                ·
                  refine ⟨11325101101988255848571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30200269605302015596189 11325101101988255848571)
                  ·
                    rfl

theorem cell21_49625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4, 3].length) (baseStart_49625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_49625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_49625 prefixEnd_49625 := by exact prefixLift 49625
  have htrace : WordTrace (prefixWord ++ tailWord_49625) baseStart_49625 baseEnd_49625 := by
    simpa [prefixWord, tailWord_49625, baseEnd_49625] using wordTrace_append hprefix tailTrace_49625
  have hstable : (prefixWord ++ tailWord_49625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49625).length < 2 ^ (prefixWord ++ tailWord_49625).sum := by decide
  have hdescent : baseEnd_49625 < baseStart_49625 := by decide
  rcases family_descends (prefixWord ++ tailWord_49625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49639 : List Nat := [1, 1, 5, 2, 1, 1, 1, 5, 4]
def baseStart_49639 : Nat := 118140960795 + 49639 * 2 ^ 59
def prefixEnd_49639 : Nat := 4983230072969 + 3 ^ 40 * 49639 * 2
def baseEnd_49639 : Nat := 11328296092727342615209

theorem tailTrace_49639 : CollatzResearch.WordTrace tailWord_49639 prefixEnd_49639 11328296092727342615209 := by
  unfold tailWord_49639
  simp only [CollatzResearch.WordTrace]
  refine ⟨1810483067173855511367971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1206988711449237007578647 1810483067173855511367971)
  ·
    refine ⟨2715724600760783267051957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1810483067173855511367971 2715724600760783267051957)
    ·
      refine ⟨254599181321323431286121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2715724600760783267051957 254599181321323431286121)
      ·
        refine ⟨190949385990992573464591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254599181321323431286121 190949385990992573464591)
        ·
          refine ⟨286424078986488860196887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190949385990992573464591 286424078986488860196887)
          ·
            refine ⟨429636118479733290295331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286424078986488860196887 429636118479733290295331)
            ·
              refine ⟨644454177719599935442997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429636118479733290295331 644454177719599935442997)
              ·
                refine ⟨60417579161212493947781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 644454177719599935442997 60417579161212493947781)
                ·
                  refine ⟨11328296092727342615209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60417579161212493947781 11328296092727342615209)
                  ·
                    rfl

theorem cell21_49639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 4].length) (baseStart_49639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_49639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_49639 prefixEnd_49639 := by exact prefixLift 49639
  have htrace : WordTrace (prefixWord ++ tailWord_49639) baseStart_49639 baseEnd_49639 := by
    simpa [prefixWord, tailWord_49639, baseEnd_49639] using wordTrace_append hprefix tailTrace_49639
  have hstable : (prefixWord ++ tailWord_49639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49639).length < 2 ^ (prefixWord ++ tailWord_49639).sum := by decide
  have hdescent : baseEnd_49639 < baseStart_49639 := by decide
  rcases family_descends (prefixWord ++ tailWord_49639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49667 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 7]
def baseStart_49667 : Nat := 118140960795 + 49667 * 2 ^ 59
def prefixEnd_49667 : Nat := 4983230072969 + 3 ^ 40 * 49667 * 2
def baseEnd_49667 : Nat := 11334686074205516148485

theorem tailTrace_49667 : CollatzResearch.WordTrace tailWord_49667 prefixEnd_49667 11334686074205516148485 := by
  unfold tailWord_49667
  simp only [CollatzResearch.WordTrace]
  refine ⟨1811504311072416293387255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1207669540714944195591503 1811504311072416293387255)
  ·
    refine ⟨2717256466608624440080883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1811504311072416293387255 2717256466608624440080883)
    ·
      refine ⟨4075884699912936660121325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2717256466608624440080883 4075884699912936660121325)
      ·
        refine ⟨1528456762467351247545497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4075884699912936660121325 1528456762467351247545497)
        ·
          refine ⟨1146342571850513435659123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1528456762467351247545497 1146342571850513435659123)
          ·
            refine ⟨1719513857775770153488685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1146342571850513435659123 1719513857775770153488685)
            ·
              refine ⟨644817696665913807558257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1719513857775770153488685 644817696665913807558257)
              ·
                refine ⟨483613272499435355668693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 644817696665913807558257 483613272499435355668693)
                ·
                  refine ⟨11334686074205516148485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 483613272499435355668693 11334686074205516148485)
                  ·
                    rfl

theorem cell21_49667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 7].length) (baseStart_49667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_49667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_49667 prefixEnd_49667 := by exact prefixLift 49667
  have htrace : WordTrace (prefixWord ++ tailWord_49667) baseStart_49667 baseEnd_49667 := by
    simpa [prefixWord, tailWord_49667, baseEnd_49667] using wordTrace_append hprefix tailTrace_49667
  have hstable : (prefixWord ++ tailWord_49667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49667).length < 2 ^ (prefixWord ++ tailWord_49667).sum := by decide
  have hdescent : baseEnd_49667 < baseStart_49667 := by decide
  rcases family_descends (prefixWord ++ tailWord_49667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49729 : List Nat := [1, 2, 5, 1, 1, 2, 9]
def baseStart_49729 : Nat := 118140960795 + 49729 * 2 ^ 59
def prefixEnd_49729 : Nat := 4983230072969 + 3 ^ 40 * 49729 * 2
def baseEnd_49729 : Nat := 1260981702100798457225

theorem tailTrace_49729 : CollatzResearch.WordTrace tailWord_49729 prefixEnd_49729 1260981702100798457225 := by
  unfold tailWord_49729
  simp only [CollatzResearch.WordTrace]
  refine ⟨1813765636847800882144241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1209177091231867254762827 1813765636847800882144241)
  ·
    refine ⟨1360324227635850661608181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1813765636847800882144241 1360324227635850661608181)
    ·
      refine ⟨127530396340860999525767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1360324227635850661608181 127530396340860999525767)
      ·
        refine ⟨191295594511291499288651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127530396340860999525767 191295594511291499288651)
        ·
          refine ⟨286943391766937248932977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191295594511291499288651 286943391766937248932977)
          ·
            refine ⟨215207543825202936699733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286943391766937248932977 215207543825202936699733)
            ·
              refine ⟨1260981702100798457225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 215207543825202936699733 1260981702100798457225)
              ·
                rfl

theorem cell21_49729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 9].length) (baseStart_49729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_49729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_49729 prefixEnd_49729 := by exact prefixLift 49729
  have htrace : WordTrace (prefixWord ++ tailWord_49729) baseStart_49729 baseEnd_49729 := by
    simpa [prefixWord, tailWord_49729, baseEnd_49729] using wordTrace_append hprefix tailTrace_49729
  have hstable : (prefixWord ++ tailWord_49729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49729).length < 2 ^ (prefixWord ++ tailWord_49729).sum := by decide
  have hdescent : baseEnd_49729 < baseStart_49729 := by decide
  rcases family_descends (prefixWord ++ tailWord_49729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49850 : List Nat := [3, 1, 1, 1, 2, 3, 3, 1, 6]
def baseStart_49850 : Nat := 118140960795 + 49850 * 2 ^ 59
def prefixEnd_49850 : Nat := 4983230072969 + 3 ^ 40 * 49850 * 2
def baseEnd_49850 : Nat := 11376449167437864598111

theorem tailTrace_49850 : CollatzResearch.WordTrace tailWord_49850 prefixEnd_49850 11376449167437864598111 := by
  unfold tailWord_49850
  simp only [CollatzResearch.WordTrace]
  refine ⟨454544717352359636824751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1212119246272959031532669 454544717352359636824751)
  ·
    refine ⟨681817076028539455237127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 454544717352359636824751 681817076028539455237127)
    ·
      refine ⟨1022725614042809182855691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 681817076028539455237127 1022725614042809182855691)
      ·
        refine ⟨1534088421064213774283537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1022725614042809182855691 1534088421064213774283537)
        ·
          refine ⟨1150566315798160330712653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1534088421064213774283537 1150566315798160330712653)
          ·
            refine ⟨431462368424310124017245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1150566315798160330712653 431462368424310124017245)
            ·
              refine ⟨161798388159116296506467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 431462368424310124017245 161798388159116296506467)
              ·
                refine ⟨242697582238674444759701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161798388159116296506467 242697582238674444759701)
                ·
                  refine ⟨11376449167437864598111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 242697582238674444759701 11376449167437864598111)
                  ·
                    rfl

theorem cell21_49850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_49850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_49850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_49850 prefixEnd_49850 := by exact prefixLift 49850
  have htrace : WordTrace (prefixWord ++ tailWord_49850) baseStart_49850 baseEnd_49850 := by
    simpa [prefixWord, tailWord_49850, baseEnd_49850] using wordTrace_append hprefix tailTrace_49850
  have hstable : (prefixWord ++ tailWord_49850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49850).length < 2 ^ (prefixWord ++ tailWord_49850).sum := by decide
  have hdescent : baseEnd_49850 < baseStart_49850 := by decide
  rcases family_descends (prefixWord ++ tailWord_49850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49853 : List Nat := [1, 4, 1, 2, 1, 3, 2, 4, 3]
def baseStart_49853 : Nat := 118140960795 + 49853 * 2 ^ 59
def prefixEnd_49853 : Nat := 4983230072969 + 3 ^ 40 * 49853 * 2
def baseEnd_49853 : Nat := 11377133808310526048105

theorem tailTrace_49853 : CollatzResearch.WordTrace tailWord_49853 prefixEnd_49853 11377133808310526048105 := by
  unfold tailWord_49853
  simp only [CollatzResearch.WordTrace]
  refine ⟨1818288288398570059658213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1212192192265713373105475 1818288288398570059658213)
  ·
    refine ⟨340929054074731886185915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1818288288398570059658213 340929054074731886185915)
    ·
      refine ⟨511393581112097829278873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340929054074731886185915 511393581112097829278873)
      ·
        refine ⟨383545185834073371959155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 511393581112097829278873 383545185834073371959155)
        ·
          refine ⟨575317778751110057938733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383545185834073371959155 575317778751110057938733)
          ·
            refine ⟨215744167031666271727025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 575317778751110057938733 215744167031666271727025)
            ·
              refine ⟨161808125273749703795269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215744167031666271727025 161808125273749703795269)
              ·
                refine ⟨30339023488828069461613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161808125273749703795269 30339023488828069461613)
                ·
                  refine ⟨11377133808310526048105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30339023488828069461613 11377133808310526048105)
                  ·
                    rfl

theorem cell21_49853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_49853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_49853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_49853 prefixEnd_49853 := by exact prefixLift 49853
  have htrace : WordTrace (prefixWord ++ tailWord_49853) baseStart_49853 baseEnd_49853 := by
    simpa [prefixWord, tailWord_49853, baseEnd_49853] using wordTrace_append hprefix tailTrace_49853
  have hstable : (prefixWord ++ tailWord_49853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49853).length < 2 ^ (prefixWord ++ tailWord_49853).sum := by decide
  have hdescent : baseEnd_49853 < baseStart_49853 := by decide
  rcases family_descends (prefixWord ++ tailWord_49853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50002 : List Nat := [3, 2, 2, 1, 1, 2, 2, 2, 6]
def baseStart_50002 : Nat := 118140960795 + 50002 * 2 ^ 59
def prefixEnd_50002 : Nat := 4983230072969 + 3 ^ 40 * 50002 * 2
def baseEnd_50002 : Nat := 11411137638319378064467

theorem tailTrace_50002 : CollatzResearch.WordTrace tailWord_50002 prefixEnd_50002 11411137638319378064467 := by
  unfold tailWord_50002
  simp only [CollatzResearch.WordTrace]
  refine ⟨455930691214692126708065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1215815176572512337888173 455930691214692126708065)
  ·
    refine ⟨341948018411019095031049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 455930691214692126708065 341948018411019095031049)
    ·
      refine ⟨256461013808264321273287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341948018411019095031049 256461013808264321273287)
      ·
        refine ⟨384691520712396481909931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256461013808264321273287 384691520712396481909931)
        ·
          refine ⟨577037281068594722864897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384691520712396481909931 577037281068594722864897)
          ·
            refine ⟨432777960801446042148673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 577037281068594722864897 432777960801446042148673)
            ·
              refine ⟨324583470601084531611505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432777960801446042148673 324583470601084531611505)
              ·
                refine ⟨243437602950813398708629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 324583470601084531611505 243437602950813398708629)
                ·
                  refine ⟨11411137638319378064467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 243437602950813398708629 11411137638319378064467)
                  ·
                    rfl

theorem cell21_50002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_50002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_50002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_50002 prefixEnd_50002 := by exact prefixLift 50002
  have htrace : WordTrace (prefixWord ++ tailWord_50002) baseStart_50002 baseEnd_50002 := by
    simpa [prefixWord, tailWord_50002, baseEnd_50002] using wordTrace_append hprefix tailTrace_50002
  have hstable : (prefixWord ++ tailWord_50002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50002).length < 2 ^ (prefixWord ++ tailWord_50002).sum := by decide
  have hdescent : baseEnd_50002 < baseStart_50002 := by decide
  rcases family_descends (prefixWord ++ tailWord_50002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50005 : List Nat := [1, 3, 2, 2, 2, 1, 4, 3, 3]
def baseStart_50005 : Nat := 118140960795 + 50005 * 2 ^ 59
def prefixEnd_50005 : Nat := 4983230072969 + 3 ^ 40 * 50005 * 2
def baseEnd_50005 : Nat := 11411822279192039514461

theorem tailTrace_50005 : CollatzResearch.WordTrace tailWord_50005 prefixEnd_50005 11411822279192039514461 := by
  unfold tailWord_50005
  simp only [CollatzResearch.WordTrace]
  refine ⟨1823832183847900019191469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1215888122565266679460979 1823832183847900019191469)
  ·
    refine ⟨683937068942962507196801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1823832183847900019191469 683937068942962507196801)
    ·
      refine ⟨512952801707221880397601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 683937068942962507196801 512952801707221880397601)
      ·
        refine ⟨384714601280416410298201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 512952801707221880397601 384714601280416410298201)
        ·
          refine ⟨288535950960312307723651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384714601280416410298201 288535950960312307723651)
          ·
            refine ⟨432803926440468461585477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288535950960312307723651 432803926440468461585477)
            ·
              refine ⟨81150736207587836547277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 432803926440468461585477 81150736207587836547277)
              ·
                refine ⟨30431526077845438705229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81150736207587836547277 30431526077845438705229)
                ·
                  refine ⟨11411822279192039514461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30431526077845438705229 11411822279192039514461)
                  ·
                    rfl

theorem cell21_50005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3, 3].length) (baseStart_50005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_50005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_50005 prefixEnd_50005 := by exact prefixLift 50005
  have htrace : WordTrace (prefixWord ++ tailWord_50005) baseStart_50005 baseEnd_50005 := by
    simpa [prefixWord, tailWord_50005, baseEnd_50005] using wordTrace_append hprefix tailTrace_50005
  have hstable : (prefixWord ++ tailWord_50005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50005).length < 2 ^ (prefixWord ++ tailWord_50005).sum := by decide
  have hdescent : baseEnd_50005 < baseStart_50005 := by decide
  rcases family_descends (prefixWord ++ tailWord_50005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50016 : List Nat := [2, 1, 1, 3, 3, 1, 10]
def baseStart_50016 : Nat := 118140960795 + 50016 * 2 ^ 59
def prefixEnd_50016 : Nat := 4983230072969 + 3 ^ 40 * 50016 * 2
def baseEnd_50016 : Nat := 1268259181006496092345

theorem tailTrace_50016 : CollatzResearch.WordTrace tailWord_50016 prefixEnd_50016 1268259181006496092345 := by
  unfold tailWord_50016
  simp only [CollatzResearch.WordTrace]
  refine ⟨912116693404024448920951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1216155591205365931894601 912116693404024448920951)
  ·
    refine ⟨1368175040106036673381427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 912116693404024448920951 1368175040106036673381427)
    ·
      refine ⟨2052262560159055010072141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1368175040106036673381427 2052262560159055010072141)
      ·
        refine ⟨769598460059645628777053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2052262560159055010072141 769598460059645628777053)
        ·
          refine ⟨288599422522367110791395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 769598460059645628777053 288599422522367110791395)
          ·
            refine ⟨432899133783550666187093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288599422522367110791395 432899133783550666187093)
            ·
              refine ⟨1268259181006496092345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 432899133783550666187093 1268259181006496092345)
              ·
                rfl

theorem cell21_50016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 10].length) (baseStart_50016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_50016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_50016 prefixEnd_50016 := by exact prefixLift 50016
  have htrace : WordTrace (prefixWord ++ tailWord_50016) baseStart_50016 baseEnd_50016 := by
    simpa [prefixWord, tailWord_50016, baseEnd_50016] using wordTrace_append hprefix tailTrace_50016
  have hstable : (prefixWord ++ tailWord_50016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50016).length < 2 ^ (prefixWord ++ tailWord_50016).sum := by decide
  have hdescent : baseEnd_50016 < baseStart_50016 := by decide
  rcases family_descends (prefixWord ++ tailWord_50016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50019 : List Nat := [1, 1, 1, 5, 3, 1, 3, 2, 4]
def baseStart_50019 : Nat := 118140960795 + 50019 * 2 ^ 59
def prefixEnd_50019 : Nat := 4983230072969 + 3 ^ 40 * 50019 * 2
def baseEnd_50019 : Nat := 11415017269931126281099

theorem tailTrace_50019 : CollatzResearch.WordTrace tailWord_50019 prefixEnd_50019 11415017269931126281099 := by
  unfold tailWord_50019
  simp only [CollatzResearch.WordTrace]
  refine ⟨1824342805797180410201111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1216228537198120273467407 1824342805797180410201111)
  ·
    refine ⟨2736514208695770615301667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1824342805797180410201111 2736514208695770615301667)
    ·
      refine ⟨4104771313043655922952501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2736514208695770615301667 4104771313043655922952501)
      ·
        refine ⟨384822310597842742776797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4104771313043655922952501 384822310597842742776797)
        ·
          refine ⟨144308366474191028541299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 384822310597842742776797 144308366474191028541299)
          ·
            refine ⟨216462549711286542811949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144308366474191028541299 216462549711286542811949)
            ·
              refine ⟨81173456141732453554481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216462549711286542811949 81173456141732453554481)
              ·
                refine ⟨60880092106299340165861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81173456141732453554481 60880092106299340165861)
                ·
                  refine ⟨11415017269931126281099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60880092106299340165861 11415017269931126281099)
                  ·
                    rfl

theorem cell21_50019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 4].length) (baseStart_50019 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_50019 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_50019 prefixEnd_50019 := by exact prefixLift 50019
  have htrace : WordTrace (prefixWord ++ tailWord_50019) baseStart_50019 baseEnd_50019 := by
    simpa [prefixWord, tailWord_50019, baseEnd_50019] using wordTrace_append hprefix tailTrace_50019
  have hstable : (prefixWord ++ tailWord_50019).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50019).length < 2 ^ (prefixWord ++ tailWord_50019).sum := by decide
  have hdescent : baseEnd_50019 < baseStart_50019 := by decide
  rcases family_descends (prefixWord ++ tailWord_50019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50047 : List Nat := [1, 1, 2, 2, 1, 1, 6, 2, 5]
def baseStart_50047 : Nat := 118140960795 + 50047 * 2 ^ 59
def prefixEnd_50047 : Nat := 4983230072969 + 3 ^ 40 * 50047 * 2
def baseEnd_50047 : Nat := 11421407251409299814375

theorem tailTrace_50047 : CollatzResearch.WordTrace tailWord_50047 prefixEnd_50047 11421407251409299814375 := by
  unfold tailWord_50047
  simp only [CollatzResearch.WordTrace]
  refine ⟨1825364049695741192220395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1216909366463827461480263 1825364049695741192220395)
  ·
    refine ⟨2738046074543611788330593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1825364049695741192220395 2738046074543611788330593)
    ·
      refine ⟨2053534555907708841247945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2738046074543611788330593 2053534555907708841247945)
      ·
        refine ⟨1540150916930781630935959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2053534555907708841247945 1540150916930781630935959)
        ·
          refine ⟨2310226375396172446403939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1540150916930781630935959 2310226375396172446403939)
          ·
            refine ⟨3465339563094258669605909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2310226375396172446403939 3465339563094258669605909)
            ·
              refine ⟨162437792020043375137777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3465339563094258669605909 162437792020043375137777)
              ·
                refine ⟨121828344015032531353333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162437792020043375137777 121828344015032531353333)
                ·
                  refine ⟨11421407251409299814375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121828344015032531353333 11421407251409299814375)
                  ·
                    rfl

theorem cell21_50047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 5].length) (baseStart_50047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_50047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_50047 prefixEnd_50047 := by exact prefixLift 50047
  have htrace : WordTrace (prefixWord ++ tailWord_50047) baseStart_50047 baseEnd_50047 := by
    simpa [prefixWord, tailWord_50047, baseEnd_50047] using wordTrace_append hprefix tailTrace_50047
  have hstable : (prefixWord ++ tailWord_50047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50047).length < 2 ^ (prefixWord ++ tailWord_50047).sum := by decide
  have hdescent : baseEnd_50047 < baseStart_50047 := by decide
  rcases family_descends (prefixWord ++ tailWord_50047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50081 : List Nat := [1, 2, 3, 4, 1, 3, 1, 1, 5]
def baseStart_50081 : Nat := 118140960795 + 50081 * 2 ^ 59
def prefixEnd_50081 : Nat := 4983230072969 + 3 ^ 40 * 50081 * 2
def baseEnd_50081 : Nat := 11429166514632796247639

theorem tailTrace_50081 : CollatzResearch.WordTrace tailWord_50081 prefixEnd_50081 11429166514632796247639 := by
  unfold tailWord_50081
  simp only [CollatzResearch.WordTrace]
  refine ⟨1826604131572564998958097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1217736087715043332638731 1826604131572564998958097)
  ·
    refine ⟨1369953098679423749218573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1826604131572564998958097 1369953098679423749218573)
    ·
      refine ⟨513732412004783905956965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1369953098679423749218573 513732412004783905956965)
      ·
        refine ⟨96324827250896982366931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 513732412004783905956965 96324827250896982366931)
        ·
          refine ⟨144487240876345473550397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96324827250896982366931 144487240876345473550397)
          ·
            refine ⟨54182715328629552581399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144487240876345473550397 54182715328629552581399)
            ·
              refine ⟨81274072992944328872099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54182715328629552581399 81274072992944328872099)
              ·
                refine ⟨121911109489416493308149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81274072992944328872099 121911109489416493308149)
                ·
                  refine ⟨11429166514632796247639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121911109489416493308149 11429166514632796247639)
                  ·
                    rfl

theorem cell21_50081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 5].length) (baseStart_50081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_50081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_50081 prefixEnd_50081 := by exact prefixLift 50081
  have htrace : WordTrace (prefixWord ++ tailWord_50081) baseStart_50081 baseEnd_50081 := by
    simpa [prefixWord, tailWord_50081, baseEnd_50081] using wordTrace_append hprefix tailTrace_50081
  have hstable : (prefixWord ++ tailWord_50081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50081).length < 2 ^ (prefixWord ++ tailWord_50081).sum := by decide
  have hdescent : baseEnd_50081 < baseStart_50081 := by decide
  rcases family_descends (prefixWord ++ tailWord_50081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50233 : List Nat := [1, 2, 1, 5, 2, 1, 3, 3, 3]
def baseStart_50233 : Nat := 118140960795 + 50233 * 2 ^ 59
def prefixEnd_50233 : Nat := 4983230072969 + 3 ^ 40 * 50233 * 2
def baseEnd_50233 : Nat := 11463854985514309713995

theorem tailTrace_50233 : CollatzResearch.WordTrace tailWord_50233 prefixEnd_50233 11463854985514309713995 := by
  unfold tailWord_50233
  simp only [CollatzResearch.WordTrace]
  refine ⟨1832148027021894958491353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1221432018014596638994235 1832148027021894958491353)
  ·
    refine ⟨1374111020266421218868515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1832148027021894958491353 1374111020266421218868515)
    ·
      refine ⟨2061166530399631828302773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1374111020266421218868515 2061166530399631828302773)
      ·
        refine ⟨193234362224965483903385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2061166530399631828302773 193234362224965483903385)
        ·
          refine ⟨144925771668724112927539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193234362224965483903385 144925771668724112927539)
          ·
            refine ⟨217388657503086169391309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144925771668724112927539 217388657503086169391309)
            ·
              refine ⟨81520746563657313521741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217388657503086169391309 81520746563657313521741)
              ·
                refine ⟨30570279961371492570653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81520746563657313521741 30570279961371492570653)
                ·
                  refine ⟨11463854985514309713995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30570279961371492570653 11463854985514309713995)
                  ·
                    rfl

theorem cell21_50233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3, 3].length) (baseStart_50233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_50233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_50233 prefixEnd_50233 := by exact prefixLift 50233
  have htrace : WordTrace (prefixWord ++ tailWord_50233) baseStart_50233 baseEnd_50233 := by
    simpa [prefixWord, tailWord_50233, baseEnd_50233] using wordTrace_append hprefix tailTrace_50233
  have hstable : (prefixWord ++ tailWord_50233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50233).length < 2 ^ (prefixWord ++ tailWord_50233).sum := by decide
  have hdescent : baseEnd_50233 < baseStart_50233 := by decide
  rcases family_descends (prefixWord ++ tailWord_50233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50289 : List Nat := [1, 2, 2, 2, 1, 1, 2, 4, 6]
def baseStart_50289 : Nat := 118140960795 + 50289 * 2 ^ 59
def prefixEnd_50289 : Nat := 4983230072969 + 3 ^ 40 * 50289 * 2
def baseEnd_50289 : Nat := 11476634948470656780547

theorem tailTrace_50289 : CollatzResearch.WordTrace tailWord_50289 prefixEnd_50289 11476634948470656780547 := by
  unfold tailWord_50289
  simp only [CollatzResearch.WordTrace]
  refine ⟨1834190514819016522529921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1222793676546011015019947 1834190514819016522529921)
  ·
    refine ⟨1375642886114262391897441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1834190514819016522529921 1375642886114262391897441)
    ·
      refine ⟨1031732164585696793923081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1375642886114262391897441 1031732164585696793923081)
      ·
        refine ⟨773799123439272595442311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1031732164585696793923081 773799123439272595442311)
        ·
          refine ⟨1160698685158908893163467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 773799123439272595442311 1160698685158908893163467)
          ·
            refine ⟨1741048027738363339745201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1160698685158908893163467 1741048027738363339745201)
            ·
              refine ⟨1305786020803772504808901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1741048027738363339745201 1305786020803772504808901)
              ·
                refine ⟨244834878900707344651669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1305786020803772504808901 244834878900707344651669)
                ·
                  refine ⟨11476634948470656780547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 244834878900707344651669 11476634948470656780547)
                  ·
                    rfl

theorem cell21_50289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 6].length) (baseStart_50289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_50289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_50289 prefixEnd_50289 := by exact prefixLift 50289
  have htrace : WordTrace (prefixWord ++ tailWord_50289) baseStart_50289 baseEnd_50289 := by
    simpa [prefixWord, tailWord_50289, baseEnd_50289] using wordTrace_append hprefix tailTrace_50289
  have hstable : (prefixWord ++ tailWord_50289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50289).length < 2 ^ (prefixWord ++ tailWord_50289).sum := by decide
  have hdescent : baseEnd_50289 < baseStart_50289 := by decide
  rcases family_descends (prefixWord ++ tailWord_50289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50309 : List Nat := [1, 3, 1, 1, 6, 1, 1, 4, 3]
def baseStart_50309 : Nat := 118140960795 + 50309 * 2 ^ 59
def prefixEnd_50309 : Nat := 4983230072969 + 3 ^ 40 * 50309 * 2
def baseEnd_50309 : Nat := 11481199220955066447173

theorem tailTrace_50309 : CollatzResearch.WordTrace tailWord_50309 prefixEnd_50309 11481199220955066447173 := by
  unfold tailWord_50309
  simp only [CollatzResearch.WordTrace]
  refine ⟨1834919974746559938257981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1223279983164373292171987 1834919974746559938257981)
  ·
    refine ⟨688094990529959976846743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1834919974746559938257981 688094990529959976846743)
    ·
      refine ⟨1032142485794939965270115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 688094990529959976846743 1032142485794939965270115)
      ·
        refine ⟨1548213728692409947905173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1032142485794939965270115 1548213728692409947905173)
        ·
          refine ⟨72572518532456716308055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1548213728692409947905173 72572518532456716308055)
          ·
            refine ⟨108858777798685074462083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72572518532456716308055 108858777798685074462083)
            ·
              refine ⟨163288166698027611693125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108858777798685074462083 163288166698027611693125)
              ·
                refine ⟨30616531255880177192461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163288166698027611693125 30616531255880177192461)
                ·
                  refine ⟨11481199220955066447173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30616531255880177192461 11481199220955066447173)
                  ·
                    rfl

theorem cell21_50309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4, 3].length) (baseStart_50309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_50309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_50309 prefixEnd_50309 := by exact prefixLift 50309
  have htrace : WordTrace (prefixWord ++ tailWord_50309) baseStart_50309 baseEnd_50309 := by
    simpa [prefixWord, tailWord_50309, baseEnd_50309] using wordTrace_append hprefix tailTrace_50309
  have hstable : (prefixWord ++ tailWord_50309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50309).length < 2 ^ (prefixWord ++ tailWord_50309).sum := by decide
  have hdescent : baseEnd_50309 < baseStart_50309 := by decide
  rcases family_descends (prefixWord ++ tailWord_50309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50337 : List Nat := [1, 2, 3, 3, 1, 1, 5, 5]
def baseStart_50337 : Nat := 118140960795 + 50337 * 2 ^ 59
def prefixEnd_50337 : Nat := 4983230072969 + 3 ^ 40 * 50337 * 2
def baseEnd_50337 : Nat := 3829196400811079993483

theorem tailTrace_50337 : CollatzResearch.WordTrace tailWord_50337 prefixEnd_50337 3829196400811079993483 := by
  unfold tailWord_50337
  simp only [CollatzResearch.WordTrace]
  refine ⟨1835941218645120720277265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1223960812430080480184843 1835941218645120720277265)
  ·
    refine ⟨1376955913983840540207949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1835941218645120720277265 1376955913983840540207949)
    ·
      refine ⟨516358467743940202577981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1376955913983840540207949 516358467743940202577981)
      ·
        refine ⟨193634425403977575966743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 516358467743940202577981 193634425403977575966743)
        ·
          refine ⟨290451638105966363950115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193634425403977575966743 290451638105966363950115)
          ·
            refine ⟨435677457158949545925173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290451638105966363950115 435677457158949545925173)
            ·
              refine ⟨40844761608651519930485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 435677457158949545925173 40844761608651519930485)
              ·
                refine ⟨3829196400811079993483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40844761608651519930485 3829196400811079993483)
                ·
                  rfl

theorem cell21_50337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 5].length) (baseStart_50337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_50337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_50337 prefixEnd_50337 := by exact prefixLift 50337
  have htrace : WordTrace (prefixWord ++ tailWord_50337) baseStart_50337 baseEnd_50337 := by
    simpa [prefixWord, tailWord_50337, baseEnd_50337] using wordTrace_append hprefix tailTrace_50337
  have hstable : (prefixWord ++ tailWord_50337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50337).length < 2 ^ (prefixWord ++ tailWord_50337).sum := by decide
  have hdescent : baseEnd_50337 < baseStart_50337 := by decide
  rcases family_descends (prefixWord ++ tailWord_50337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50368 : List Nat := [2, 1, 1, 2, 6, 1, 2, 1, 5]
def baseStart_50368 : Nat := 118140960795 + 50368 * 2 ^ 59
def prefixEnd_50368 : Nat := 4983230072969 + 3 ^ 40 * 50368 * 2
def baseEnd_50368 : Nat := 11494663824784074963719

theorem tailTrace_50368 : CollatzResearch.WordTrace tailWord_50368 prefixEnd_50368 11494663824784074963719 := by
  unfold tailWord_50368
  simp only [CollatzResearch.WordTrace]
  refine ⟨918535940766406507327879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1224714587688542009770505 918535940766406507327879)
  ·
    refine ⟨1377803911149609760991819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 918535940766406507327879 1377803911149609760991819)
    ·
      refine ⟨2066705866724414641487729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1377803911149609760991819 2066705866724414641487729)
      ·
        refine ⟨1550029400043310981115797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2066705866724414641487729 1550029400043310981115797)
        ·
          refine ⟨72657628127030202239803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1550029400043310981115797 72657628127030202239803)
          ·
            refine ⟨108986442190545303359705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72657628127030202239803 108986442190545303359705)
            ·
              refine ⟨81739831642908977519779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108986442190545303359705 81739831642908977519779)
              ·
                refine ⟨122609747464363466279669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81739831642908977519779 122609747464363466279669)
                ·
                  refine ⟨11494663824784074963719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122609747464363466279669 11494663824784074963719)
                  ·
                    rfl

theorem cell21_50368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 5].length) (baseStart_50368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_50368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_50368 prefixEnd_50368 := by exact prefixLift 50368
  have htrace : WordTrace (prefixWord ++ tailWord_50368) baseStart_50368 baseEnd_50368 := by
    simpa [prefixWord, tailWord_50368, baseEnd_50368] using wordTrace_append hprefix tailTrace_50368
  have hstable : (prefixWord ++ tailWord_50368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50368).length < 2 ^ (prefixWord ++ tailWord_50368).sum := by decide
  have hdescent : baseEnd_50368 < baseStart_50368 := by decide
  rcases family_descends (prefixWord ++ tailWord_50368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50388 : List Nat := [2, 4, 1, 4, 2, 1, 2, 5]
def baseStart_50388 : Nat := 118140960795 + 50388 * 2 ^ 59
def prefixEnd_50388 : Nat := 4983230072969 + 3 ^ 40 * 50388 * 2
def baseEnd_50388 : Nat := 3833076032422828210115

theorem tailTrace_50388 : CollatzResearch.WordTrace tailWord_50388 prefixEnd_50388 3833076032422828210115 := by
  unfold tailWord_50388
  simp only [CollatzResearch.WordTrace]
  refine ⟨918900670730178215191909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1225200894306904286922545 918900670730178215191909)
  ·
    refine ⟨172293875761908415348483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 918900670730178215191909 172293875761908415348483)
    ·
      refine ⟨258440813642862623022725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172293875761908415348483 258440813642862623022725)
      ·
        refine ⟨48457652558036741816761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 258440813642862623022725 48457652558036741816761)
        ·
          refine ⟨36343239418527556362571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48457652558036741816761 36343239418527556362571)
          ·
            refine ⟨54514859127791334543857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36343239418527556362571 54514859127791334543857)
            ·
              refine ⟨40886144345843500907893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54514859127791334543857 40886144345843500907893)
              ·
                refine ⟨3833076032422828210115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40886144345843500907893 3833076032422828210115)
                ·
                  rfl

theorem cell21_50388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 5].length) (baseStart_50388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_50388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_50388 prefixEnd_50388 := by exact prefixLift 50388
  have htrace : WordTrace (prefixWord ++ tailWord_50388) baseStart_50388 baseEnd_50388 := by
    simpa [prefixWord, tailWord_50388, baseEnd_50388] using wordTrace_append hprefix tailTrace_50388
  have hstable : (prefixWord ++ tailWord_50388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50388).length < 2 ^ (prefixWord ++ tailWord_50388).sum := by decide
  have hdescent : baseEnd_50388 < baseStart_50388 := by decide
  rcases family_descends (prefixWord ++ tailWord_50388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50413 : List Nat := [1, 5, 1, 2, 2, 3, 7]
def baseStart_50413 : Nat := 118140960795 + 50413 * 2 ^ 59
def prefixEnd_50413 : Nat := 4983230072969 + 3 ^ 40 * 50413 * 2
def baseEnd_50413 : Nat := 1278325937541555190403

theorem tailTrace_50413 : CollatzResearch.WordTrace tailWord_50413 prefixEnd_50413 1278325937541555190403 := by
  unfold tailWord_50413
  simp only [CollatzResearch.WordTrace]
  refine ⟨1838713166369785700043893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1225808777579857133362595 1838713166369785700043893)
  ·
    refine ⟨172379359347167409379115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1838713166369785700043893 172379359347167409379115)
    ·
      refine ⟨258569039020751114068673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172379359347167409379115 258569039020751114068673)
      ·
        refine ⟨193926779265563335551505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258569039020751114068673 193926779265563335551505)
        ·
          refine ⟨145445084449172501663629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193926779265563335551505 145445084449172501663629)
          ·
            refine ⟨54541906668439688123861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145445084449172501663629 54541906668439688123861)
            ·
              refine ⟨1278325937541555190403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 54541906668439688123861 1278325937541555190403)
              ·
                rfl

theorem cell21_50413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 7].length) (baseStart_50413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_50413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_50413 prefixEnd_50413 := by exact prefixLift 50413
  have htrace : WordTrace (prefixWord ++ tailWord_50413) baseStart_50413 baseEnd_50413 := by
    simpa [prefixWord, tailWord_50413, baseEnd_50413] using wordTrace_append hprefix tailTrace_50413
  have hstable : (prefixWord ++ tailWord_50413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50413).length < 2 ^ (prefixWord ++ tailWord_50413).sum := by decide
  have hdescent : baseEnd_50413 < baseStart_50413 := by decide
  rcases family_descends (prefixWord ++ tailWord_50413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50472 : List Nat := [2, 1, 5, 1, 2, 10]
def baseStart_50472 : Nat := 118140960795 + 50472 * 2 ^ 59
def prefixEnd_50472 : Nat := 4983230072969 + 3 ^ 40 * 50472 * 2
def baseEnd_50472 : Nat := 426607334877889082599

theorem tailTrace_50472 : CollatzResearch.WordTrace tailWord_50472 prefixEnd_50472 426607334877889082599 := by
  unfold tailWord_50472
  simp only [CollatzResearch.WordTrace]
  refine ⟨920432536578019388220835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1227243382104025850961113 920432536578019388220835)
  ·
    refine ⟨1380648804867029082331253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 920432536578019388220835 1380648804867029082331253)
    ·
      refine ⟨129435825456283976468555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1380648804867029082331253 129435825456283976468555)
      ·
        refine ⟨194153738184425964702833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129435825456283976468555 194153738184425964702833)
        ·
          refine ⟨145615303638319473527125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194153738184425964702833 145615303638319473527125)
          ·
            refine ⟨426607334877889082599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 145615303638319473527125 426607334877889082599)
            ·
              rfl

theorem cell21_50472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 10].length) (baseStart_50472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_50472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_50472 prefixEnd_50472 := by exact prefixLift 50472
  have htrace : WordTrace (prefixWord ++ tailWord_50472) baseStart_50472 baseEnd_50472 := by
    simpa [prefixWord, tailWord_50472, baseEnd_50472] using wordTrace_append hprefix tailTrace_50472
  have hstable : (prefixWord ++ tailWord_50472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50472).length < 2 ^ (prefixWord ++ tailWord_50472).sum := by decide
  have hdescent : baseEnd_50472 < baseStart_50472 := by decide
  rcases family_descends (prefixWord ++ tailWord_50472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50503 : List Nat := [1, 1, 4, 1, 2, 4, 1, 2, 5]
def baseStart_50503 : Nat := 118140960795 + 50503 * 2 ^ 59
def prefixEnd_50503 : Nat := 4983230072969 + 3 ^ 40 * 50503 * 2
def baseEnd_50503 : Nat := 11525472664053840213443

theorem tailTrace_50503 : CollatzResearch.WordTrace tailWord_50503 prefixEnd_50503 11525472664053840213443 := by
  unfold tailWord_50503
  simp only [CollatzResearch.WordTrace]
  refine ⟨1841995736043731070820163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1227997157362487380546775 1841995736043731070820163)
  ·
    refine ⟨2762993604065596606230245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1841995736043731070820163 2762993604065596606230245)
    ·
      refine ⟨518061300762299363668171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2762993604065596606230245 518061300762299363668171)
      ·
        refine ⟨777091951143449045502257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518061300762299363668171 777091951143449045502257)
        ·
          refine ⟨582818963357586784126693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 777091951143449045502257 582818963357586784126693)
          ·
            refine ⟨109278555629547522023755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 582818963357586784126693 109278555629547522023755)
            ·
              refine ⟨163917833444321283035633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109278555629547522023755 163917833444321283035633)
              ·
                refine ⟨122938375083240962276725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163917833444321283035633 122938375083240962276725)
                ·
                  refine ⟨11525472664053840213443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122938375083240962276725 11525472664053840213443)
                  ·
                    rfl

theorem cell21_50503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 5].length) (baseStart_50503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_50503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_50503 prefixEnd_50503 := by exact prefixLift 50503
  have htrace : WordTrace (prefixWord ++ tailWord_50503) baseStart_50503 baseEnd_50503 := by
    simpa [prefixWord, tailWord_50503, baseEnd_50503] using wordTrace_append hprefix tailTrace_50503
  have hstable : (prefixWord ++ tailWord_50503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50503).length < 2 ^ (prefixWord ++ tailWord_50503).sum := by decide
  have hdescent : baseEnd_50503 < baseStart_50503 := by decide
  rcases family_descends (prefixWord ++ tailWord_50503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50520 : List Nat := [2, 1, 2, 2, 1, 1, 6, 3, 3]
def baseStart_50520 : Nat := 118140960795 + 50520 * 2 ^ 59
def prefixEnd_50520 : Nat := 4983230072969 + 3 ^ 40 * 50520 * 2
def baseEnd_50520 : Nat := 11529352295665588430075

theorem tailTrace_50520 : CollatzResearch.WordTrace tailWord_50520 prefixEnd_50520 11529352295665588430075 := by
  unfold tailWord_50520
  simp only [CollatzResearch.WordTrace]
  refine ⟨921307888491071487094507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1228410517988095316126009 921307888491071487094507)
  ·
    refine ⟨1381961832736607230641761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 921307888491071487094507 1381961832736607230641761)
    ·
      refine ⟨1036471374552455422981321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1381961832736607230641761 1036471374552455422981321)
      ·
        refine ⟨777353530914341567235991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1036471374552455422981321 777353530914341567235991)
        ·
          refine ⟨1166030296371512350853987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 777353530914341567235991 1166030296371512350853987)
          ·
            refine ⟨1749045444557268526280981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1166030296371512350853987 1749045444557268526280981)
            ·
              refine ⟨81986505213621962169421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1749045444557268526280981 81986505213621962169421)
              ·
                refine ⟨30744939455108235813533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81986505213621962169421 30744939455108235813533)
                ·
                  refine ⟨11529352295665588430075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30744939455108235813533 11529352295665588430075)
                  ·
                    rfl

theorem cell21_50520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3, 3].length) (baseStart_50520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_50520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_50520 prefixEnd_50520 := by exact prefixLift 50520
  have htrace : WordTrace (prefixWord ++ tailWord_50520) baseStart_50520 baseEnd_50520 := by
    simpa [prefixWord, tailWord_50520, baseEnd_50520] using wordTrace_append hprefix tailTrace_50520
  have hstable : (prefixWord ++ tailWord_50520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50520).length < 2 ^ (prefixWord ++ tailWord_50520).sum := by decide
  have hdescent : baseEnd_50520 < baseStart_50520 := by decide
  rcases family_descends (prefixWord ++ tailWord_50520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50689 : List Nat := [1, 2, 4, 1, 4, 1, 2, 3, 3]
def baseStart_50689 : Nat := 118140960795 + 50689 * 2 ^ 59
def prefixEnd_50689 : Nat := 4983230072969 + 3 ^ 40 * 50689 * 2
def baseEnd_50689 : Nat := 11567920398158850113063

theorem tailTrace_50689 : CollatzResearch.WordTrace tailWord_50689 prefixEnd_50689 11567920398158850113063 := by
  unfold tailWord_50689
  simp only [CollatzResearch.WordTrace]
  refine ⟨1848779713369884837091121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1232519808913256558060747 1848779713369884837091121)
  ·
    refine ⟨1386584785027413627818341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1848779713369884837091121 1386584785027413627818341)
    ·
      refine ⟨259984647192640055215939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1386584785027413627818341 259984647192640055215939)
      ·
        refine ⟨389976970788960082823909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259984647192640055215939 389976970788960082823909)
        ·
          refine ⟨73120682022930015529483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 389976970788960082823909 73120682022930015529483)
          ·
            refine ⟨109681023034395023294225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73120682022930015529483 109681023034395023294225)
            ·
              refine ⟨82260767275796267470669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109681023034395023294225 82260767275796267470669)
              ·
                refine ⟨30847787728423600301501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82260767275796267470669 30847787728423600301501)
                ·
                  refine ⟨11567920398158850113063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30847787728423600301501 11567920398158850113063)
                  ·
                    rfl

theorem cell21_50689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3, 3].length) (baseStart_50689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_50689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_50689 prefixEnd_50689 := by exact prefixLift 50689
  have htrace : WordTrace (prefixWord ++ tailWord_50689) baseStart_50689 baseEnd_50689 := by
    simpa [prefixWord, tailWord_50689, baseEnd_50689] using wordTrace_append hprefix tailTrace_50689
  have hstable : (prefixWord ++ tailWord_50689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50689).length < 2 ^ (prefixWord ++ tailWord_50689).sum := by decide
  have hdescent : baseEnd_50689 < baseStart_50689 := by decide
  rcases family_descends (prefixWord ++ tailWord_50689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50700 : List Nat := [2, 2, 1, 2, 5, 1, 8]
def baseStart_50700 : Nat := 118140960795 + 50700 * 2 ^ 59
def prefixEnd_50700 : Nat := 4983230072969 + 3 ^ 40 * 50700 * 2
def baseEnd_50700 : Nat := 1285603416447252825523

theorem tailTrace_50700 : CollatzResearch.WordTrace tailWord_50700 prefixEnd_50700 1285603416447252825523 := by
  unfold tailWord_50700
  simp only [CollatzResearch.WordTrace]
  refine ⟨924590458165016857870777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1232787277553355810494369 924590458165016857870777)
  ·
    refine ⟨693442843623762643403083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 924590458165016857870777 693442843623762643403083)
    ·
      refine ⟨1040164265435643965104625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 693442843623762643403083 1040164265435643965104625)
      ·
        refine ⟨780123199076732973828469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1040164265435643965104625 780123199076732973828469)
        ·
          refine ⟨73136549913443716296419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 780123199076732973828469 73136549913443716296419)
          ·
            refine ⟨109704824870165574444629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73136549913443716296419 109704824870165574444629)
            ·
              refine ⟨1285603416447252825523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 109704824870165574444629 1285603416447252825523)
              ·
                rfl

theorem cell21_50700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 8].length) (baseStart_50700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_50700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_50700 prefixEnd_50700 := by exact prefixLift 50700
  have htrace : WordTrace (prefixWord ++ tailWord_50700) baseStart_50700 baseEnd_50700 := by
    simpa [prefixWord, tailWord_50700, baseEnd_50700] using wordTrace_append hprefix tailTrace_50700
  have hstable : (prefixWord ++ tailWord_50700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50700).length < 2 ^ (prefixWord ++ tailWord_50700).sum := by decide
  have hdescent : baseEnd_50700 < baseStart_50700 := by decide
  rcases family_descends (prefixWord ++ tailWord_50700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50734 : List Nat := [4, 1, 3, 1, 2, 3, 2, 5]
def baseStart_50734 : Nat := 118140960795 + 50734 * 2 ^ 59
def prefixEnd_50734 : Nat := 4983230072969 + 3 ^ 40 * 50734 * 2
def baseEnd_50734 : Nat := 3859396670416257287657

theorem tailTrace_50734 : CollatzResearch.WordTrace tailWord_50734 prefixEnd_50734 3859396670416257287657 := by
  unfold tailWord_50734
  simp only [CollatzResearch.WordTrace]
  refine ⟨231302624775857190309907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1233613998804571681652837 231302624775857190309907)
  ·
    refine ⟨346953937163785785464861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231302624775857190309907 346953937163785785464861)
    ·
      refine ⟨130107726436419669549323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 346953937163785785464861 130107726436419669549323)
      ·
        refine ⟨195161589654629504323985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130107726436419669549323 195161589654629504323985)
        ·
          refine ⟨146371192240972128242989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195161589654629504323985 146371192240972128242989)
          ·
            refine ⟨54889197090364548091121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146371192240972128242989 54889197090364548091121)
            ·
              refine ⟨41166897817773411068341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54889197090364548091121 41166897817773411068341)
              ·
                refine ⟨3859396670416257287657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41166897817773411068341 3859396670416257287657)
                ·
                  rfl

theorem cell21_50734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_50734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_50734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_50734 prefixEnd_50734 := by exact prefixLift 50734
  have htrace : WordTrace (prefixWord ++ tailWord_50734) baseStart_50734 baseEnd_50734 := by
    simpa [prefixWord, tailWord_50734, baseEnd_50734] using wordTrace_append hprefix tailTrace_50734
  have hstable : (prefixWord ++ tailWord_50734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50734).length < 2 ^ (prefixWord ++ tailWord_50734).sum := by decide
  have hdescent : baseEnd_50734 < baseStart_50734 := by decide
  rcases family_descends (prefixWord ++ tailWord_50734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50745 : List Nat := [1, 2, 1, 5, 1, 2, 1, 2, 6]
def baseStart_50745 : Nat := 118140960795 + 50745 * 2 ^ 59
def prefixEnd_50745 : Nat := 4983230072969 + 3 ^ 40 * 50745 * 2
def baseEnd_50745 : Nat := 11580700361115197179615

theorem tailTrace_50745 : CollatzResearch.WordTrace tailWord_50745 prefixEnd_50745 11580700361115197179615 := by
  unfold tailWord_50745
  simp only [CollatzResearch.WordTrace]
  refine ⟨1850822201167006401129689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1233881467444670934086459 1850822201167006401129689)
  ·
    refine ⟨1388116650875254800847267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1850822201167006401129689 1388116650875254800847267)
    ·
      refine ⟨2082174976312882201270901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1388116650875254800847267 2082174976312882201270901)
      ·
        refine ⟨195203904029332706369147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2082174976312882201270901 195203904029332706369147)
        ·
          refine ⟨292805856043999059553721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195203904029332706369147 292805856043999059553721)
          ·
            refine ⟨219604392032999294665291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292805856043999059553721 219604392032999294665291)
            ·
              refine ⟨329406588049498941997937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219604392032999294665291 329406588049498941997937)
              ·
                refine ⟨247054941037124206498453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329406588049498941997937 247054941037124206498453)
                ·
                  refine ⟨11580700361115197179615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 247054941037124206498453 11580700361115197179615)
                  ·
                    rfl

theorem cell21_50745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 6].length) (baseStart_50745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_50745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_50745 prefixEnd_50745 := by exact prefixLift 50745
  have htrace : WordTrace (prefixWord ++ tailWord_50745) baseStart_50745 baseEnd_50745 := by
    simpa [prefixWord, tailWord_50745, baseEnd_50745] using wordTrace_append hprefix tailTrace_50745
  have hstable : (prefixWord ++ tailWord_50745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50745).length < 2 ^ (prefixWord ++ tailWord_50745).sum := by decide
  have hdescent : baseEnd_50745 < baseStart_50745 := by decide
  rcases family_descends (prefixWord ++ tailWord_50745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50765 : List Nat := [1, 6, 1, 1, 3, 2, 1, 1, 5]
def baseStart_50765 : Nat := 118140960795 + 50765 * 2 ^ 59
def prefixEnd_50765 : Nat := 4983230072969 + 3 ^ 40 * 50765 * 2
def baseEnd_50765 : Nat := 11585264633599606846241

theorem tailTrace_50765 : CollatzResearch.WordTrace tailWord_50765 prefixEnd_50765 11585264633599606846241 := by
  unfold tailWord_50765
  simp only [CollatzResearch.WordTrace]
  refine ⟨1851551661094549816857749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1234367774063033211238499 1851551661094549816857749)
  ·
    refine ⟨86791484113807022665207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1851551661094549816857749 86791484113807022665207)
    ·
      refine ⟨130187226170710533997811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86791484113807022665207 130187226170710533997811)
      ·
        refine ⟨195280839256065800996717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130187226170710533997811 195280839256065800996717)
        ·
          refine ⟨73230314721024675373769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195280839256065800996717 73230314721024675373769)
          ·
            refine ⟨54922736040768506530327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73230314721024675373769 54922736040768506530327)
            ·
              refine ⟨82384104061152759795491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54922736040768506530327 82384104061152759795491)
              ·
                refine ⟨123576156091729139693237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82384104061152759795491 123576156091729139693237)
                ·
                  refine ⟨11585264633599606846241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 123576156091729139693237 11585264633599606846241)
                  ·
                    rfl

theorem cell21_50765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_50765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_50765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_50765 prefixEnd_50765 := by exact prefixLift 50765
  have htrace : WordTrace (prefixWord ++ tailWord_50765) baseStart_50765 baseEnd_50765 := by
    simpa [prefixWord, tailWord_50765, baseEnd_50765] using wordTrace_append hprefix tailTrace_50765
  have hstable : (prefixWord ++ tailWord_50765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50765).length < 2 ^ (prefixWord ++ tailWord_50765).sum := by decide
  have hdescent : baseEnd_50765 < baseStart_50765 := by decide
  rcases family_descends (prefixWord ++ tailWord_50765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50807 : List Nat := [1, 1, 3, 1, 1, 3, 1, 7, 3]
def baseStart_50807 : Nat := 118140960795 + 50807 * 2 ^ 59
def prefixEnd_50807 : Nat := 4983230072969 + 3 ^ 40 * 50807 * 2
def baseEnd_50807 : Nat := 11594849605816867146155

theorem tailTrace_50807 : CollatzResearch.WordTrace tailWord_50807 prefixEnd_50807 11594849605816867146155 := by
  unfold tailWord_50807
  simp only [CollatzResearch.WordTrace]
  refine ⟨1853083526942390989886675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1235389017961593993257783 1853083526942390989886675)
  ·
    refine ⟨2779625290413586484830013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1853083526942390989886675 2779625290413586484830013)
    ·
      refine ⟨1042359483905094931811255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2779625290413586484830013 1042359483905094931811255)
      ·
        refine ⟨1563539225857642397716883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1042359483905094931811255 1563539225857642397716883)
        ·
          refine ⟨2345308838786463596575325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1563539225857642397716883 2345308838786463596575325)
          ·
            refine ⟨879490814544923848715747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2345308838786463596575325 879490814544923848715747)
            ·
              refine ⟨1319236221817385773073621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 879490814544923848715747 1319236221817385773073621)
              ·
                refine ⟨30919598948844979056413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1319236221817385773073621 30919598948844979056413)
                ·
                  refine ⟨11594849605816867146155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30919598948844979056413 11594849605816867146155)
                  ·
                    rfl

theorem cell21_50807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7, 3].length) (baseStart_50807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_50807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_50807 prefixEnd_50807 := by exact prefixLift 50807
  have htrace : WordTrace (prefixWord ++ tailWord_50807) baseStart_50807 baseEnd_50807 := by
    simpa [prefixWord, tailWord_50807, baseEnd_50807] using wordTrace_append hprefix tailTrace_50807
  have hstable : (prefixWord ++ tailWord_50807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50807).length < 2 ^ (prefixWord ++ tailWord_50807).sum := by decide
  have hdescent : baseEnd_50807 < baseStart_50807 := by decide
  rcases family_descends (prefixWord ++ tailWord_50807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50911 : List Nat := [1, 1, 2, 3, 2, 2, 3, 7]
def baseStart_50911 : Nat := 118140960795 + 50911 * 2 ^ 59
def prefixEnd_50911 : Nat := 4983230072969 + 3 ^ 40 * 50911 * 2
def baseEnd_50911 : Nat := 3872861274245265804203

theorem tailTrace_50911 : CollatzResearch.WordTrace tailWord_50911 prefixEnd_50911 3872861274245265804203 := by
  unfold tailWord_50911
  simp only [CollatzResearch.WordTrace]
  refine ⟨1856876718565616751672587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1237917812377077834448391 1856876718565616751672587)
  ·
    refine ⟨2785315077848425127508881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1856876718565616751672587 2785315077848425127508881)
    ·
      refine ⟨2088986308386318845631661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2785315077848425127508881 2088986308386318845631661)
      ·
        refine ⟨783369865644869567111873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2088986308386318845631661 783369865644869567111873)
        ·
          refine ⟨587527399233652175333905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 783369865644869567111873 587527399233652175333905)
          ·
            refine ⟨440645549425239131500429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 587527399233652175333905 440645549425239131500429)
            ·
              refine ⟨165242081034464674312661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 440645549425239131500429 165242081034464674312661)
              ·
                refine ⟨3872861274245265804203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 165242081034464674312661 3872861274245265804203)
                ·
                  rfl

theorem cell21_50911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 7].length) (baseStart_50911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_50911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_50911 prefixEnd_50911 := by exact prefixLift 50911
  have htrace : WordTrace (prefixWord ++ tailWord_50911) baseStart_50911 baseEnd_50911 := by
    simpa [prefixWord, tailWord_50911, baseEnd_50911] using wordTrace_append hprefix tailTrace_50911
  have hstable : (prefixWord ++ tailWord_50911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50911).length < 2 ^ (prefixWord ++ tailWord_50911).sum := by decide
  have hdescent : baseEnd_50911 < baseStart_50911 := by decide
  rcases family_descends (prefixWord ++ tailWord_50911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50993 : List Nat := [1, 2, 2, 3, 2, 4, 2, 2, 3]
def baseStart_50993 : Nat := 118140960795 + 50993 * 2 ^ 59
def prefixEnd_50993 : Nat := 4983230072969 + 3 ^ 40 * 50993 * 2
def baseEnd_50993 : Nat := 11637297339921877045775

theorem tailTrace_50993 : CollatzResearch.WordTrace tailWord_50993 prefixEnd_50993 11637297339921877045775 := by
  unfold tailWord_50993
  simp only [CollatzResearch.WordTrace]
  refine ⟨1859867504268544756157633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1239911669512363170771755 1859867504268544756157633)
  ·
    refine ⟨1394900628201408567118225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1859867504268544756157633 1394900628201408567118225)
    ·
      refine ⟨1046175471151056425338669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1394900628201408567118225 1046175471151056425338669)
      ·
        refine ⟨392315801681646159502001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1046175471151056425338669 392315801681646159502001)
        ·
          refine ⟨294236851261234619626501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392315801681646159502001 294236851261234619626501)
          ·
            refine ⟨55169409611481491179969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 294236851261234619626501 55169409611481491179969)
            ·
              refine ⟨41377057208611118384977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55169409611481491179969 41377057208611118384977)
              ·
                refine ⟨31032792906458338788733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41377057208611118384977 31032792906458338788733)
                ·
                  refine ⟨11637297339921877045775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31032792906458338788733 11637297339921877045775)
                  ·
                    rfl

theorem cell21_50993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2, 3].length) (baseStart_50993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_50993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_50993 prefixEnd_50993 := by exact prefixLift 50993
  have htrace : WordTrace (prefixWord ++ tailWord_50993) baseStart_50993 baseEnd_50993 := by
    simpa [prefixWord, tailWord_50993, baseEnd_50993] using wordTrace_append hprefix tailTrace_50993
  have hstable : (prefixWord ++ tailWord_50993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50993).length < 2 ^ (prefixWord ++ tailWord_50993).sum := by decide
  have hdescent : baseEnd_50993 < baseStart_50993 := by decide
  rcases family_descends (prefixWord ++ tailWord_50993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51018 : List Nat := [3, 1, 2, 1, 1, 1, 5, 2, 5]
def baseStart_51018 : Nat := 118140960795 + 51018 * 2 ^ 59
def prefixEnd_51018 : Nat := 4983230072969 + 3 ^ 40 * 51018 * 2
def baseEnd_51018 : Nat := 11643002680527389129057

theorem tailTrace_51018 : CollatzResearch.WordTrace tailWord_51018 prefixEnd_51018 11643002680527389129057 := by
  unfold tailWord_51018
  simp only [CollatzResearch.WordTrace]
  refine ⟨465194832294493506454427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1240519552785316017211805 465194832294493506454427)
  ·
    refine ⟨697792248441740259681641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 465194832294493506454427 697792248441740259681641)
    ·
      refine ⟨523344186331305194761231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 697792248441740259681641 523344186331305194761231)
      ·
        refine ⟨785016279496957792141847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523344186331305194761231 785016279496957792141847)
        ·
          refine ⟨1177524419245436688212771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 785016279496957792141847 1177524419245436688212771)
          ·
            refine ⟨1766286628868155032319157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1177524419245436688212771 1766286628868155032319157)
            ·
              refine ⟨165589371456389534279921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1766286628868155032319157 165589371456389534279921)
              ·
                refine ⟨124192028592292150709941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165589371456389534279921 124192028592292150709941)
                ·
                  refine ⟨11643002680527389129057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124192028592292150709941 11643002680527389129057)
                  ·
                    rfl

theorem cell21_51018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_51018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_51018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_51018 prefixEnd_51018 := by exact prefixLift 51018
  have htrace : WordTrace (prefixWord ++ tailWord_51018) baseStart_51018 baseEnd_51018 := by
    simpa [prefixWord, tailWord_51018, baseEnd_51018] using wordTrace_append hprefix tailTrace_51018
  have hstable : (prefixWord ++ tailWord_51018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51018).length < 2 ^ (prefixWord ++ tailWord_51018).sum := by decide
  have hdescent : baseEnd_51018 < baseStart_51018 := by decide
  rcases family_descends (prefixWord ++ tailWord_51018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51080 : List Nat := [2, 1, 3, 3, 3, 1, 1, 7]
def baseStart_51080 : Nat := 118140960795 + 51080 * 2 ^ 59
def prefixEnd_51080 : Nat := 4983230072969 + 3 ^ 40 * 51080 * 2
def baseEnd_51080 : Nat := 3885717308409686365199

theorem tailTrace_51080 : CollatzResearch.WordTrace tailWord_51080 prefixEnd_51080 3885717308409686365199 := by
  unfold tailWord_51080
  simp only [CollatzResearch.WordTrace]
  refine ⟨931520327476679307287347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1242027103302239076383129 931520327476679307287347)
  ·
    refine ⟨1397280491215018960931021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 931520327476679307287347 1397280491215018960931021)
    ·
      refine ⟨523980184205632110349133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1397280491215018960931021 523980184205632110349133)
      ·
        refine ⟨196492569077112041380925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 523980184205632110349133 196492569077112041380925)
        ·
          refine ⟨73684713403917015517847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196492569077112041380925 73684713403917015517847)
          ·
            refine ⟨110527070105875523276771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73684713403917015517847 110527070105875523276771)
            ·
              refine ⟨165790605158813284915157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110527070105875523276771 165790605158813284915157)
              ·
                refine ⟨3885717308409686365199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 165790605158813284915157 3885717308409686365199)
                ·
                  rfl

theorem cell21_51080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 7].length) (baseStart_51080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_51080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_51080 prefixEnd_51080 := by exact prefixLift 51080
  have htrace : WordTrace (prefixWord ++ tailWord_51080) baseStart_51080 baseEnd_51080 := by
    simpa [prefixWord, tailWord_51080, baseEnd_51080] using wordTrace_append hprefix tailTrace_51080
  have hstable : (prefixWord ++ tailWord_51080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51080).length < 2 ^ (prefixWord ++ tailWord_51080).sum := by decide
  have hdescent : baseEnd_51080 < baseStart_51080 := by decide
  rcases family_descends (prefixWord ++ tailWord_51080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51086 : List Nat := [4, 1, 1, 5, 1, 2, 1, 3, 3]
def baseStart_51086 : Nat := 118140960795 + 51086 * 2 ^ 59
def prefixEnd_51086 : Nat := 4983230072969 + 3 ^ 40 * 51086 * 2
def baseEnd_51086 : Nat := 11658521206974381995585

theorem tailTrace_51086 : CollatzResearch.WordTrace tailWord_51086 prefixEnd_51086 11658521206974381995585 := by
  unfold tailWord_51086
  simp only [CollatzResearch.WordTrace]
  refine ⟨232907436616452704911639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1242172995287747759528741 232907436616452704911639)
  ·
    refine ⟨349361154924679057367459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232907436616452704911639 349361154924679057367459)
    ·
      refine ⟨524041732387018586051189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349361154924679057367459 524041732387018586051189)
      ·
        refine ⟨49128912411282992442299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 524041732387018586051189 49128912411282992442299)
        ·
          refine ⟨73693368616924488663449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49128912411282992442299 73693368616924488663449)
          ·
            refine ⟨55270026462693366497587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73693368616924488663449 55270026462693366497587)
            ·
              refine ⟨82905039694040049746381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55270026462693366497587 82905039694040049746381)
              ·
                refine ⟨31089389885265018654893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82905039694040049746381 31089389885265018654893)
                ·
                  refine ⟨11658521206974381995585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31089389885265018654893 11658521206974381995585)
                  ·
                    rfl

theorem cell21_51086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_51086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_51086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_51086 prefixEnd_51086 := by exact prefixLift 51086
  have htrace : WordTrace (prefixWord ++ tailWord_51086) baseStart_51086 baseEnd_51086 := by
    simpa [prefixWord, tailWord_51086, baseEnd_51086] using wordTrace_append hprefix tailTrace_51086
  have hstable : (prefixWord ++ tailWord_51086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51086).length < 2 ^ (prefixWord ++ tailWord_51086).sum := by decide
  have hdescent : baseEnd_51086 < baseStart_51086 := by decide
  rcases family_descends (prefixWord ++ tailWord_51086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51111 : List Nat := [1, 1, 6, 1, 2, 1, 3, 1, 5]
def baseStart_51111 : Nat := 118140960795 + 51111 * 2 ^ 59
def prefixEnd_51111 : Nat := 4983230072969 + 3 ^ 40 * 51111 * 2
def baseEnd_51111 : Nat := 11664226547579894078867

theorem tailTrace_51111 : CollatzResearch.WordTrace tailWord_51111 prefixEnd_51111 11664226547579894078867 := by
  unfold tailWord_51111
  simp only [CollatzResearch.WordTrace]
  refine ⟨1864171317841050908953187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1242780878560700605968791 1864171317841050908953187)
  ·
    refine ⟨2796256976761576363429781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1864171317841050908953187 2796256976761576363429781)
    ·
      refine ⟨131074545785698892035771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2796256976761576363429781 131074545785698892035771)
      ·
        refine ⟨196611818678548338053657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131074545785698892035771 196611818678548338053657)
        ·
          refine ⟨147458864008911253540243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196611818678548338053657 147458864008911253540243)
          ·
            refine ⟨221188296013366880310365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147458864008911253540243 221188296013366880310365)
            ·
              refine ⟨82945611005012580116387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221188296013366880310365 82945611005012580116387)
              ·
                refine ⟨124418416507518870174581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82945611005012580116387 124418416507518870174581)
                ·
                  refine ⟨11664226547579894078867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124418416507518870174581 11664226547579894078867)
                  ·
                    rfl

theorem cell21_51111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 5].length) (baseStart_51111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_51111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_51111 prefixEnd_51111 := by exact prefixLift 51111
  have htrace : WordTrace (prefixWord ++ tailWord_51111) baseStart_51111 baseEnd_51111 := by
    simpa [prefixWord, tailWord_51111, baseEnd_51111] using wordTrace_append hprefix tailTrace_51111
  have hstable : (prefixWord ++ tailWord_51111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51111).length < 2 ^ (prefixWord ++ tailWord_51111).sum := by decide
  have hdescent : baseEnd_51111 < baseStart_51111 := by decide
  rcases family_descends (prefixWord ++ tailWord_51111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51153 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 9]
def baseStart_51153 : Nat := 118140960795 + 51153 * 2 ^ 59
def prefixEnd_51153 : Nat := 4983230072969 + 3 ^ 40 * 51153 * 2
def baseEnd_51153 : Nat := 11673811519797154378781

theorem tailTrace_51153 : CollatzResearch.WordTrace tailWord_51153 prefixEnd_51153 11673811519797154378781 := by
  unfold tailWord_51153
  simp only [CollatzResearch.WordTrace]
  refine ⟨1865703183688892081982113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1243802122459261387988075 1865703183688892081982113)
  ·
    refine ⟨1399277387766669061486585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1865703183688892081982113 1399277387766669061486585)
    ·
      refine ⟨1049458040825001796114939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1399277387766669061486585 1049458040825001796114939)
      ·
        refine ⟨1574187061237502694172409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1049458040825001796114939 1574187061237502694172409)
        ·
          refine ⟨1180640295928127020629307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1574187061237502694172409 1180640295928127020629307)
          ·
            refine ⟨1770960443892190530943961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1180640295928127020629307 1770960443892190530943961)
            ·
              refine ⟨1328220332919142898207971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1770960443892190530943961 1328220332919142898207971)
              ·
                refine ⟨1992330499378714347311957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1328220332919142898207971 1992330499378714347311957)
                ·
                  refine ⟨11673811519797154378781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1992330499378714347311957 11673811519797154378781)
                  ·
                    rfl

theorem cell21_51153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 9].length) (baseStart_51153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_51153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_51153 prefixEnd_51153 := by exact prefixLift 51153
  have htrace : WordTrace (prefixWord ++ tailWord_51153) baseStart_51153 baseEnd_51153 := by
    simpa [prefixWord, tailWord_51153, baseEnd_51153] using wordTrace_append hprefix tailTrace_51153
  have hstable : (prefixWord ++ tailWord_51153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51153).length < 2 ^ (prefixWord ++ tailWord_51153).sum := by decide
  have hdescent : baseEnd_51153 < baseStart_51153 := by decide
  rcases family_descends (prefixWord ++ tailWord_51153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51162 : List Nat := [3, 1, 1, 2, 6, 1, 2, 2, 3]
def baseStart_51162 : Nat := 118140960795 + 51162 * 2 ^ 59
def prefixEnd_51162 : Nat := 4983230072969 + 3 ^ 40 * 51162 * 2
def baseEnd_51162 : Nat := 11675865442415138728763

theorem tailTrace_51162 : CollatzResearch.WordTrace tailWord_51162 prefixEnd_51162 11675865442415138728763 := by
  unfold tailWord_51162
  simp only [CollatzResearch.WordTrace]
  refine ⟨466507860164071654764935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1244020960437524412706493 466507860164071654764935)
  ·
    refine ⟨699761790246107482147403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 466507860164071654764935 699761790246107482147403)
    ·
      refine ⟨1049642685369161223221105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 699761790246107482147403 1049642685369161223221105)
      ·
        refine ⟨787232014026870917415829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1049642685369161223221105 787232014026870917415829)
        ·
          refine ⟨36901500657509574253867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 787232014026870917415829 36901500657509574253867)
          ·
            refine ⟨55352250986264361380801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36901500657509574253867 55352250986264361380801)
            ·
              refine ⟨41514188239698271035601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55352250986264361380801 41514188239698271035601)
              ·
                refine ⟨31135641179773703276701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41514188239698271035601 31135641179773703276701)
                ·
                  refine ⟨11675865442415138728763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31135641179773703276701 11675865442415138728763)
                  ·
                    rfl

theorem cell21_51162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2, 3].length) (baseStart_51162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_51162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_51162 prefixEnd_51162 := by exact prefixLift 51162
  have htrace : WordTrace (prefixWord ++ tailWord_51162) baseStart_51162 baseEnd_51162 := by
    simpa [prefixWord, tailWord_51162, baseEnd_51162] using wordTrace_append hprefix tailTrace_51162
  have hstable : (prefixWord ++ tailWord_51162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51162).length < 2 ^ (prefixWord ++ tailWord_51162).sum := by decide
  have hdescent : baseEnd_51162 < baseStart_51162 := by decide
  rcases family_descends (prefixWord ++ tailWord_51162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51260 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 8]
def baseStart_51260 : Nat := 118140960795 + 51260 * 2 ^ 59
def prefixEnd_51260 : Nat := 4983230072969 + 3 ^ 40 * 51260 * 2
def baseEnd_51260 : Nat := 11698230377588746095229

theorem tailTrace_51260 : CollatzResearch.WordTrace tailWord_51260 prefixEnd_51260 11698230377588746095229 := by
  unfold tailWord_51260
  simp only [CollatzResearch.WordTrace]
  refine ⟨934802897150624678063617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1246403862867499570751489 934802897150624678063617)
  ·
    refine ⟨701102172862968508547713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 934802897150624678063617 701102172862968508547713)
    ·
      refine ⟨525826629647226381410785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 701102172862968508547713 525826629647226381410785)
      ·
        refine ⟨394369972235419786058089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 525826629647226381410785 394369972235419786058089)
        ·
          refine ⟨295777479176564839543567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394369972235419786058089 295777479176564839543567)
          ·
            refine ⟨443666218764847259315351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295777479176564839543567 443666218764847259315351)
            ·
              refine ⟨665499328147270888973027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443666218764847259315351 665499328147270888973027)
              ·
                refine ⟨998248992220906333459541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 665499328147270888973027 998248992220906333459541)
                ·
                  refine ⟨11698230377588746095229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 998248992220906333459541 11698230377588746095229)
                  ·
                    rfl

theorem cell21_51260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_51260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_51260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_51260 prefixEnd_51260 := by exact prefixLift 51260
  have htrace : WordTrace (prefixWord ++ tailWord_51260) baseStart_51260 baseEnd_51260 := by
    simpa [prefixWord, tailWord_51260, baseEnd_51260] using wordTrace_append hprefix tailTrace_51260
  have hstable : (prefixWord ++ tailWord_51260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51260).length < 2 ^ (prefixWord ++ tailWord_51260).sum := by decide
  have hdescent : baseEnd_51260 < baseStart_51260 := by decide
  rcases family_descends (prefixWord ++ tailWord_51260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51263 : List Nat := [1, 1, 2, 2, 3, 1, 5, 3, 3]
def baseStart_51263 : Nat := 118140960795 + 51263 * 2 ^ 59
def prefixEnd_51263 : Nat := 4983230072969 + 3 ^ 40 * 51263 * 2
def baseEnd_51263 : Nat := 11698915018461407545223

theorem tailTrace_51263 : CollatzResearch.WordTrace tailWord_51263 prefixEnd_51263 11698915018461407545223 := by
  unfold tailWord_51263
  simp only [CollatzResearch.WordTrace]
  refine ⟨1869715213290380868486443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1246476808860253912324295 1869715213290380868486443)
  ·
    refine ⟨2804572819935571302729665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1869715213290380868486443 2804572819935571302729665)
    ·
      refine ⟨2103429614951678477047249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2804572819935571302729665 2103429614951678477047249)
      ·
        refine ⟨1577572211213758857785437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2103429614951678477047249 1577572211213758857785437)
        ·
          refine ⟨591589579205159571669539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1577572211213758857785437 591589579205159571669539)
          ·
            refine ⟨887384368807739357504309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591589579205159571669539 887384368807739357504309)
            ·
              refine ⟨83192284575725564766029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 887384368807739357504309 83192284575725564766029)
              ·
                refine ⟨31197106715897086787261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83192284575725564766029 31197106715897086787261)
                ·
                  refine ⟨11698915018461407545223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31197106715897086787261 11698915018461407545223)
                  ·
                    rfl

theorem cell21_51263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3, 3].length) (baseStart_51263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_51263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_51263 prefixEnd_51263 := by exact prefixLift 51263
  have htrace : WordTrace (prefixWord ++ tailWord_51263) baseStart_51263 baseEnd_51263 := by
    simpa [prefixWord, tailWord_51263, baseEnd_51263] using wordTrace_append hprefix tailTrace_51263
  have hstable : (prefixWord ++ tailWord_51263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51263).length < 2 ^ (prefixWord ++ tailWord_51263).sum := by decide
  have hdescent : baseEnd_51263 < baseStart_51263 := by decide
  rcases family_descends (prefixWord ++ tailWord_51263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51277 : List Nat := [1, 6, 1, 1, 1, 1, 1, 3, 6]
def baseStart_51277 : Nat := 118140960795 + 51277 * 2 ^ 59
def prefixEnd_51277 : Nat := 4983230072969 + 3 ^ 40 * 51277 * 2
def baseEnd_51277 : Nat := 11702110009200494311861

theorem tailTrace_51277 : CollatzResearch.WordTrace tailWord_51277 prefixEnd_51277 11702110009200494311861 := by
  unfold tailWord_51277
  simp only [CollatzResearch.WordTrace]
  refine ⟨1870225835239661259496085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1246817223493107506330723 1870225835239661259496085)
  ·
    refine ⟨87666836026859121538879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1870225835239661259496085 87666836026859121538879)
    ·
      refine ⟨131500254040288682308319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87666836026859121538879 131500254040288682308319)
      ·
        refine ⟨197250381060433023462479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131500254040288682308319 197250381060433023462479)
        ·
          refine ⟨295875571590649535193719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197250381060433023462479 295875571590649535193719)
          ·
            refine ⟨443813357385974302790579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295875571590649535193719 443813357385974302790579)
            ·
              refine ⟨665720036078961454185869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443813357385974302790579 665720036078961454185869)
              ·
                refine ⟨249645013529610545319701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 665720036078961454185869 249645013529610545319701)
                ·
                  refine ⟨11702110009200494311861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 249645013529610545319701 11702110009200494311861)
                  ·
                    rfl

theorem cell21_51277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_51277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_51277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_51277 prefixEnd_51277 := by exact prefixLift 51277
  have htrace : WordTrace (prefixWord ++ tailWord_51277) baseStart_51277 baseEnd_51277 := by
    simpa [prefixWord, tailWord_51277, baseEnd_51277] using wordTrace_append hprefix tailTrace_51277
  have hstable : (prefixWord ++ tailWord_51277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51277).length < 2 ^ (prefixWord ++ tailWord_51277).sum := by decide
  have hdescent : baseEnd_51277 < baseStart_51277 := by decide
  rcases family_descends (prefixWord ++ tailWord_51277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51305 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 7]
def baseStart_51305 : Nat := 118140960795 + 51305 * 2 ^ 59
def prefixEnd_51305 : Nat := 4983230072969 + 3 ^ 40 * 51305 * 2
def baseEnd_51305 : Nat := 11708499990678667845137

theorem tailTrace_51305 : CollatzResearch.WordTrace tailWord_51305 prefixEnd_51305 11708499990678667845137 := by
  unfold tailWord_51305
  simp only [CollatzResearch.WordTrace]
  refine ⟨1871247079138222041515369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1247498052758814694343579 1871247079138222041515369)
  ·
    refine ⟨1403435309353666531136527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1871247079138222041515369 1403435309353666531136527)
    ·
      refine ⟨2105152964030499796704791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1403435309353666531136527 2105152964030499796704791)
      ·
        refine ⟨3157729446045749695057187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2105152964030499796704791 3157729446045749695057187)
        ·
          refine ⟨4736594169068624542585781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3157729446045749695057187 4736594169068624542585781)
          ·
            refine ⟨444055703350183550867417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4736594169068624542585781 444055703350183550867417)
            ·
              refine ⟨333041777512637663150563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 444055703350183550867417 333041777512637663150563)
              ·
                refine ⟨499562666268956494725845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333041777512637663150563 499562666268956494725845)
                ·
                  refine ⟨11708499990678667845137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 499562666268956494725845 11708499990678667845137)
                  ·
                    rfl

theorem cell21_51305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 7].length) (baseStart_51305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_51305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_51305 prefixEnd_51305 := by exact prefixLift 51305
  have htrace : WordTrace (prefixWord ++ tailWord_51305) baseStart_51305 baseEnd_51305 := by
    simpa [prefixWord, tailWord_51305, baseEnd_51305] using wordTrace_append hprefix tailTrace_51305
  have hstable : (prefixWord ++ tailWord_51305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51305).length < 2 ^ (prefixWord ++ tailWord_51305).sum := by decide
  have hdescent : baseEnd_51305 < baseStart_51305 := by decide
  rcases family_descends (prefixWord ++ tailWord_51305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51432 : List Nat := [2, 1, 4, 1, 2, 4, 1, 3, 3]
def baseStart_51432 : Nat := 118140960795 + 51432 * 2 ^ 59
def prefixEnd_51432 : Nat := 4983230072969 + 3 ^ 40 * 51432 * 2
def baseEnd_51432 : Nat := 11737483120954669228211

theorem tailTrace_51432 : CollatzResearch.WordTrace tailWord_51432 prefixEnd_51432 11737483120954669228211 := by
  unfold tailWord_51432
  simp only [CollatzResearch.WordTrace]
  refine ⟨937939574839061365694275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1250586099785415154259033 937939574839061365694275)
  ·
    refine ⟨1406909362258592048541413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 937939574839061365694275 1406909362258592048541413)
    ·
      refine ⟨263795505423486009101515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1406909362258592048541413 263795505423486009101515)
      ·
        refine ⟨395693258135229013652273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263795505423486009101515 395693258135229013652273)
        ·
          refine ⟨296769943601421760239205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 395693258135229013652273 296769943601421760239205)
          ·
            refine ⟨55644364425266580044851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 296769943601421760239205 55644364425266580044851)
            ·
              refine ⟨83466546637899870067277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55644364425266580044851 83466546637899870067277)
              ·
                refine ⟨31299954989212451275229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83466546637899870067277 31299954989212451275229)
                ·
                  refine ⟨11737483120954669228211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31299954989212451275229 11737483120954669228211)
                  ·
                    rfl

theorem cell21_51432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3, 3].length) (baseStart_51432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_51432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_51432 prefixEnd_51432 := by exact prefixLift 51432
  have htrace : WordTrace (prefixWord ++ tailWord_51432) baseStart_51432 baseEnd_51432 := by
    simpa [prefixWord, tailWord_51432, baseEnd_51432] using wordTrace_append hprefix tailTrace_51432
  have hstable : (prefixWord ++ tailWord_51432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51432).length < 2 ^ (prefixWord ++ tailWord_51432).sum := by decide
  have hdescent : baseEnd_51432 < baseStart_51432 := by decide
  rcases family_descends (prefixWord ++ tailWord_51432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51460 : List Nat := [2, 3, 2, 2, 3, 1, 2, 6]
def baseStart_51460 : Nat := 118140960795 + 51460 * 2 ^ 59
def prefixEnd_51460 : Nat := 4983230072969 + 3 ^ 40 * 51460 * 2
def baseEnd_51460 : Nat := 3914624367477614253829

theorem tailTrace_51460 : CollatzResearch.WordTrace tailWord_51460 prefixEnd_51460 3914624367477614253829 := by
  unfold tailWord_51460
  simp only [CollatzResearch.WordTrace]
  refine ⟨938450196788341756703917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1251266929051122342271889 938450196788341756703917)
  ·
    refine ⟨351918823795628158763969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 938450196788341756703917 351918823795628158763969)
    ·
      refine ⟨263939117846721119072977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351918823795628158763969 263939117846721119072977)
      ·
        refine ⟨197954338385040839304733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263939117846721119072977 197954338385040839304733)
        ·
          refine ⟨74232876894390314739275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197954338385040839304733 74232876894390314739275)
          ·
            refine ⟨111349315341585472108913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74232876894390314739275 111349315341585472108913)
            ·
              refine ⟨83511986506189104081685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111349315341585472108913 83511986506189104081685)
              ·
                refine ⟨3914624367477614253829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83511986506189104081685 3914624367477614253829)
                ·
                  rfl

theorem cell21_51460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 6].length) (baseStart_51460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_51460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_51460 prefixEnd_51460 := by exact prefixLift 51460
  have htrace : WordTrace (prefixWord ++ tailWord_51460) baseStart_51460 baseEnd_51460 := by
    simpa [prefixWord, tailWord_51460, baseEnd_51460] using wordTrace_append hprefix tailTrace_51460
  have hstable : (prefixWord ++ tailWord_51460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51460).length < 2 ^ (prefixWord ++ tailWord_51460).sum := by decide
  have hdescent : baseEnd_51460 < baseStart_51460 := by decide
  rcases family_descends (prefixWord ++ tailWord_51460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51508 : List Nat := [2, 5, 1, 1, 1, 3, 1, 4, 3]
def baseStart_51508 : Nat := 118140960795 + 51508 * 2 ^ 59
def prefixEnd_51508 : Nat := 4983230072969 + 3 ^ 40 * 51508 * 2
def baseEnd_51508 : Nat := 11754827356395425961389

theorem tailTrace_51508 : CollatzResearch.WordTrace tailWord_51508 prefixEnd_51508 11754827356395425961389 := by
  unfold tailWord_51508
  simp only [CollatzResearch.WordTrace]
  refine ⟨939325548701393855577589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1252434064935191807436785 939325548701393855577589)
  ·
    refine ⟨88061770190755673960399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 939325548701393855577589 88061770190755673960399)
    ·
      refine ⟨132092655286133510940599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88061770190755673960399 132092655286133510940599)
      ·
        refine ⟨198138982929200266410899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132092655286133510940599 198138982929200266410899)
        ·
          refine ⟨297208474393800399616349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198138982929200266410899 297208474393800399616349)
          ·
            refine ⟨111453177897675149856131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 297208474393800399616349 111453177897675149856131)
            ·
              refine ⟨167179766846512724784197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111453177897675149856131 167179766846512724784197)
              ·
                refine ⟨31346206283721135897037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167179766846512724784197 31346206283721135897037)
                ·
                  refine ⟨11754827356395425961389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31346206283721135897037 11754827356395425961389)
                  ·
                    rfl

theorem cell21_51508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_51508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_51508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_51508 prefixEnd_51508 := by exact prefixLift 51508
  have htrace : WordTrace (prefixWord ++ tailWord_51508) baseStart_51508 baseEnd_51508 := by
    simpa [prefixWord, tailWord_51508, baseEnd_51508] using wordTrace_append hprefix tailTrace_51508
  have hstable : (prefixWord ++ tailWord_51508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51508).length < 2 ^ (prefixWord ++ tailWord_51508).sum := by decide
  have hdescent : baseEnd_51508 < baseStart_51508 := by decide
  rcases family_descends (prefixWord ++ tailWord_51508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51595 : List Nat := [1, 1, 1, 1, 4, 4, 4, 5]
def baseStart_51595 : Nat := 118140960795 + 51595 * 2 ^ 59
def prefixEnd_51595 : Nat := 4983230072969 + 3 ^ 40 * 51595 * 2
def baseEnd_51595 : Nat := 3924893980567536003737

theorem tailTrace_51595 : CollatzResearch.WordTrace tailWord_51595 prefixEnd_51595 3924893980567536003737 := by
  unfold tailWord_51595
  simp only [CollatzResearch.WordTrace]
  refine ⟨1881824248087601569572239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1254549498725067713048159 1881824248087601569572239)
  ·
    refine ⟨2822736372131402354358359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1881824248087601569572239 2822736372131402354358359)
    ·
      refine ⟨4234104558197103531537539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2822736372131402354358359 4234104558197103531537539)
      ·
        refine ⟨6351156837295655297306309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4234104558197103531537539 6351156837295655297306309)
        ·
          refine ⟨1190841906992935368244933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6351156837295655297306309 1190841906992935368244933)
          ·
            refine ⟨223282857561175381545925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1190841906992935368244933 223282857561175381545925)
            ·
              refine ⟨41865535792720384039861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 223282857561175381545925 41865535792720384039861)
              ·
                refine ⟨3924893980567536003737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41865535792720384039861 3924893980567536003737)
                ·
                  rfl

theorem cell21_51595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 5].length) (baseStart_51595 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_51595 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_51595 prefixEnd_51595 := by exact prefixLift 51595
  have htrace : WordTrace (prefixWord ++ tailWord_51595) baseStart_51595 baseEnd_51595 := by
    simpa [prefixWord, tailWord_51595, baseEnd_51595] using wordTrace_append hprefix tailTrace_51595
  have hstable : (prefixWord ++ tailWord_51595).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51595).length < 2 ^ (prefixWord ++ tailWord_51595).sum := by decide
  have hdescent : baseEnd_51595 < baseStart_51595 := by decide
  rcases family_descends (prefixWord ++ tailWord_51595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51702 : List Nat := [5, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_51702 : Nat := 118140960795 + 51702 * 2 ^ 59
def prefixEnd_51702 : Nat := 4983230072969 + 3 ^ 40 * 51702 * 2
def baseEnd_51702 : Nat := 11799100799494199727659

theorem tailTrace_51702 : CollatzResearch.WordTrace tailWord_51702 prefixEnd_51702 11799100799494199727659 := by
  unfold tailWord_51702
  simp only [CollatzResearch.WordTrace]
  refine ⟨117857928668747427732335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1257151239133305895811573 117857928668747427732335)
  ·
    refine ⟨176786893003121141598503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117857928668747427732335 176786893003121141598503)
    ·
      refine ⟨265180339504681712397755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176786893003121141598503 265180339504681712397755)
      ·
        refine ⟨397770509257022568596633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265180339504681712397755 397770509257022568596633)
        ·
          refine ⟨298327881942766926447475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 397770509257022568596633 298327881942766926447475)
          ·
            refine ⟨447491822914150389671213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298327881942766926447475 447491822914150389671213)
            ·
              refine ⟨167809433592806396126705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 447491822914150389671213 167809433592806396126705)
              ·
                refine ⟨125857075194604797095029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167809433592806396126705 125857075194604797095029)
                ·
                  refine ⟨11799100799494199727659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125857075194604797095029 11799100799494199727659)
                  ·
                    rfl

theorem cell21_51702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_51702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_51702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_51702 prefixEnd_51702 := by exact prefixLift 51702
  have htrace : WordTrace (prefixWord ++ tailWord_51702) baseStart_51702 baseEnd_51702 := by
    simpa [prefixWord, tailWord_51702, baseEnd_51702] using wordTrace_append hprefix tailTrace_51702
  have hstable : (prefixWord ++ tailWord_51702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51702).length < 2 ^ (prefixWord ++ tailWord_51702).sum := by decide
  have hdescent : baseEnd_51702 < baseStart_51702 := by decide
  rcases family_descends (prefixWord ++ tailWord_51702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51761 : List Nat := [1, 2, 2, 3, 1, 1, 4, 2, 5]
def baseStart_51761 : Nat := 118140960795 + 51761 * 2 ^ 59
def prefixEnd_51761 : Nat := 4983230072969 + 3 ^ 40 * 51761 * 2
def baseEnd_51761 : Nat := 11812565403323208244205

theorem tailTrace_51761 : CollatzResearch.WordTrace tailWord_51761 prefixEnd_51761 11812565403323208244205 := by
  unfold tailWord_51761
  simp only [CollatzResearch.WordTrace]
  refine ⟨1887878765486211920115137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1258585843657474613410091 1887878765486211920115137)
  ·
    refine ⟨1415909074114658940086353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1887878765486211920115137 1415909074114658940086353)
    ·
      refine ⟨1061931805585994205064765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1415909074114658940086353 1061931805585994205064765)
      ·
        refine ⟨398224427094747826899287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1061931805585994205064765 398224427094747826899287)
        ·
          refine ⟨597336640642121740348931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398224427094747826899287 597336640642121740348931)
          ·
            refine ⟨896004960963182610523397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597336640642121740348931 896004960963182610523397)
            ·
              refine ⟨168000930180596739473137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 896004960963182610523397 168000930180596739473137)
              ·
                refine ⟨126000697635447554604853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168000930180596739473137 126000697635447554604853)
                ·
                  refine ⟨11812565403323208244205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 126000697635447554604853 11812565403323208244205)
                  ·
                    rfl

theorem cell21_51761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 5].length) (baseStart_51761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_51761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_51761 prefixEnd_51761 := by exact prefixLift 51761
  have htrace : WordTrace (prefixWord ++ tailWord_51761) baseStart_51761 baseEnd_51761 := by
    simpa [prefixWord, tailWord_51761, baseEnd_51761] using wordTrace_append hprefix tailTrace_51761
  have hstable : (prefixWord ++ tailWord_51761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51761).length < 2 ^ (prefixWord ++ tailWord_51761).sum := by decide
  have hdescent : baseEnd_51761 < baseStart_51761 := by decide
  rcases family_descends (prefixWord ++ tailWord_51761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51775 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 8]
def baseStart_51775 : Nat := 118140960795 + 51775 * 2 ^ 59
def prefixEnd_51775 : Nat := 4983230072969 + 3 ^ 40 * 51775 * 2
def baseEnd_51775 : Nat := 11815760394062295010843

theorem tailTrace_51775 : CollatzResearch.WordTrace tailWord_51775 prefixEnd_51775 11815760394062295010843 := by
  unfold tailWord_51775
  simp only [CollatzResearch.WordTrace]
  refine ⟨1888389387435492311124779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1258926258290328207416519 1888389387435492311124779)
  ·
    refine ⟨2832584081153238466687169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1888389387435492311124779 2832584081153238466687169)
    ·
      refine ⟨2124438060864928850015377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2832584081153238466687169 2124438060864928850015377)
      ·
        refine ⟨1593328545648696637511533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2124438060864928850015377 1593328545648696637511533)
        ·
          refine ⟨597498204618261239066825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1593328545648696637511533 597498204618261239066825)
          ·
            refine ⟨448123653463695929300119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 597498204618261239066825 448123653463695929300119)
            ·
              refine ⟨672185480195543893950179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448123653463695929300119 672185480195543893950179)
              ·
                refine ⟨1008278220293315840925269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672185480195543893950179 1008278220293315840925269)
                ·
                  refine ⟨11815760394062295010843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1008278220293315840925269 11815760394062295010843)
                  ·
                    rfl

theorem cell21_51775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 8].length) (baseStart_51775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_51775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_51775 prefixEnd_51775 := by exact prefixLift 51775
  have htrace : WordTrace (prefixWord ++ tailWord_51775) baseStart_51775 baseEnd_51775 := by
    simpa [prefixWord, tailWord_51775, baseEnd_51775] using wordTrace_append hprefix tailTrace_51775
  have hstable : (prefixWord ++ tailWord_51775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51775).length < 2 ^ (prefixWord ++ tailWord_51775).sum := by decide
  have hdescent : baseEnd_51775 < baseStart_51775 := by decide
  rcases family_descends (prefixWord ++ tailWord_51775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51809 : List Nat := [1, 2, 3, 1, 1, 4, 4, 1, 4]
def baseStart_51809 : Nat := 118140960795 + 51809 * 2 ^ 59
def prefixEnd_51809 : Nat := 4983230072969 + 3 ^ 40 * 51809 * 2
def baseEnd_51809 : Nat := 11823519657285791444107

theorem tailTrace_51809 : CollatzResearch.WordTrace tailWord_51809 prefixEnd_51809 11823519657285791444107 := by
  unfold tailWord_51809
  simp only [CollatzResearch.WordTrace]
  refine ⟨1889629469312316117862481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1259752979541544078574987 1889629469312316117862481)
  ·
    refine ⟨1417222101984237088396861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1889629469312316117862481 1417222101984237088396861)
    ·
      refine ⟨531458288244088908148823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1417222101984237088396861 531458288244088908148823)
      ·
        refine ⟨797187432366133362223235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531458288244088908148823 797187432366133362223235)
        ·
          refine ⟨1195781148549200043334853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 797187432366133362223235 1195781148549200043334853)
          ·
            refine ⟨224208965352975008125285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1195781148549200043334853 224208965352975008125285)
            ·
              refine ⟨42039181003682814023491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 224208965352975008125285 42039181003682814023491)
              ·
                refine ⟨63058771505524221035237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42039181003682814023491 63058771505524221035237)
                ·
                  refine ⟨11823519657285791444107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63058771505524221035237 11823519657285791444107)
                  ·
                    rfl

theorem cell21_51809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 4].length) (baseStart_51809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_51809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_51809 prefixEnd_51809 := by exact prefixLift 51809
  have htrace : WordTrace (prefixWord ++ tailWord_51809) baseStart_51809 baseEnd_51809 := by
    simpa [prefixWord, tailWord_51809, baseEnd_51809] using wordTrace_append hprefix tailTrace_51809
  have hstable : (prefixWord ++ tailWord_51809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51809).length < 2 ^ (prefixWord ++ tailWord_51809).sum := by decide
  have hdescent : baseEnd_51809 < baseStart_51809 := by decide
  rcases family_descends (prefixWord ++ tailWord_51809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51975 : List Nat := [1, 1, 4, 4, 1, 2, 2, 6]
def baseStart_51975 : Nat := 118140960795 + 51975 * 2 ^ 59
def prefixEnd_51975 : Nat := 4983230072969 + 3 ^ 40 * 51975 * 2
def baseEnd_51975 : Nat := 3953801039635463892367

theorem tailTrace_51975 : CollatzResearch.WordTrace tailWord_51975 prefixEnd_51975 3953801039635463892367 := by
  unfold tailWord_51975
  simp only [CollatzResearch.WordTrace]
  refine ⟨1895683986710926468405379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1263789324473950978936919 1895683986710926468405379)
  ·
    refine ⟨2843525980066389702608069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1895683986710926468405379 2843525980066389702608069)
    ·
      refine ⟨533161121262448069239013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2843525980066389702608069 533161121262448069239013)
      ·
        refine ⟨99967710236709012982315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 533161121262448069239013 99967710236709012982315)
        ·
          refine ⟨149951565355063519473473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99967710236709012982315 149951565355063519473473)
          ·
            refine ⟨112463674016297639605105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149951565355063519473473 112463674016297639605105)
            ·
              refine ⟨84347755512223229703829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112463674016297639605105 84347755512223229703829)
              ·
                refine ⟨3953801039635463892367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84347755512223229703829 3953801039635463892367)
                ·
                  rfl

theorem cell21_51975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 6].length) (baseStart_51975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_51975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_51975 prefixEnd_51975 := by exact prefixLift 51975
  have htrace : WordTrace (prefixWord ++ tailWord_51975) baseStart_51975 baseEnd_51975 := by
    simpa [prefixWord, tailWord_51975, baseEnd_51975] using wordTrace_append hprefix tailTrace_51975
  have hstable : (prefixWord ++ tailWord_51975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51975).length < 2 ^ (prefixWord ++ tailWord_51975).sum := by decide
  have hdescent : baseEnd_51975 < baseStart_51975 := by decide
  rcases family_descends (prefixWord ++ tailWord_51975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52048 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 7]
def baseStart_52048 : Nat := 118140960795 + 52048 * 2 ^ 59
def prefixEnd_52048 : Nat := 4983230072969 + 3 ^ 40 * 52048 * 2
def baseEnd_52048 : Nat := 11878062713474486960285

theorem tailTrace_52048 : CollatzResearch.WordTrace tailWord_52048 prefixEnd_52048 11878062713474486960285 := by
  unfold tailWord_52048
  simp only [CollatzResearch.WordTrace]
  refine ⟨949173257723229967906399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1265564343630973290541865 949173257723229967906399)
  ·
    refine ⟨1423759886584844951859599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 949173257723229967906399 1423759886584844951859599)
    ·
      refine ⟨2135639829877267427789399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1423759886584844951859599 2135639829877267427789399)
      ·
        refine ⟨3203459744815901141684099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2135639829877267427789399 3203459744815901141684099)
        ·
          refine ⟨4805189617223851712526149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3203459744815901141684099 4805189617223851712526149)
          ·
            refine ⟨900973053229472196098653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4805189617223851712526149 900973053229472196098653)
            ·
              refine ⟨337864894961052073536995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 900973053229472196098653 337864894961052073536995)
              ·
                refine ⟨506797342441578110305493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 337864894961052073536995 506797342441578110305493)
                ·
                  refine ⟨11878062713474486960285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 506797342441578110305493 11878062713474486960285)
                  ·
                    rfl

theorem cell21_52048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 7].length) (baseStart_52048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_52048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_52048 prefixEnd_52048 := by exact prefixLift 52048
  have htrace : WordTrace (prefixWord ++ tailWord_52048) baseStart_52048 baseEnd_52048 := by
    simpa [prefixWord, tailWord_52048, baseEnd_52048] using wordTrace_append hprefix tailTrace_52048
  have hstable : (prefixWord ++ tailWord_52048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52048).length < 2 ^ (prefixWord ++ tailWord_52048).sum := by decide
  have hdescent : baseEnd_52048 < baseStart_52048 := by decide
  rcases family_descends (prefixWord ++ tailWord_52048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52082 : List Nat := [3, 2, 1, 2, 1, 1, 4, 4, 3]
def baseStart_52082 : Nat := 118140960795 + 52082 * 2 ^ 59
def prefixEnd_52082 : Nat := 4983230072969 + 3 ^ 40 * 52082 * 2
def baseEnd_52082 : Nat := 11885821976697983393549

theorem tailTrace_52082 : CollatzResearch.WordTrace tailWord_52082 prefixEnd_52082 11885821976697983393549 := by
  unfold tailWord_52082
  simp only [CollatzResearch.WordTrace]
  refine ⟨474896649330820935637625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1266391064882189161700333 474896649330820935637625)
  ·
    refine ⟨356172486998115701728219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 474896649330820935637625 356172486998115701728219)
    ·
      refine ⟨534258730497173552592329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356172486998115701728219 534258730497173552592329)
      ·
        refine ⟨400694047872880164444247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 534258730497173552592329 400694047872880164444247)
        ·
          refine ⟨601041071809320246666371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400694047872880164444247 601041071809320246666371)
          ·
            refine ⟨901561607713980369999557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601041071809320246666371 901561607713980369999557)
            ·
              refine ⟨169042801446371319374917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 901561607713980369999557 169042801446371319374917)
              ·
                refine ⟨31695525271194622382797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169042801446371319374917 31695525271194622382797)
                ·
                  refine ⟨11885821976697983393549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31695525271194622382797 11885821976697983393549)
                  ·
                    rfl

theorem cell21_52082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_52082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_52082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_52082 prefixEnd_52082 := by exact prefixLift 52082
  have htrace : WordTrace (prefixWord ++ tailWord_52082) baseStart_52082 baseEnd_52082 := by
    simpa [prefixWord, tailWord_52082, baseEnd_52082] using wordTrace_append hprefix tailTrace_52082
  have hstable : (prefixWord ++ tailWord_52082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52082).length < 2 ^ (prefixWord ++ tailWord_52082).sum := by decide
  have hdescent : baseEnd_52082 < baseStart_52082 := by decide
  rcases family_descends (prefixWord ++ tailWord_52082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52189 : List Nat := [1, 4, 3, 1, 2, 2, 2, 2, 4]
def baseStart_52189 : Nat := 118140960795 + 52189 * 2 ^ 59
def prefixEnd_52189 : Nat := 4983230072969 + 3 ^ 40 * 52189 * 2
def baseEnd_52189 : Nat := 11910240834489575109997

theorem tailTrace_52189 : CollatzResearch.WordTrace tailWord_52189 prefixEnd_52189 11910240834489575109997 := by
  unfold tailWord_52189
  simp only [CollatzResearch.WordTrace]
  refine ⟨1903489207935641016695621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1268992805290427344463747 1903489207935641016695621)
  ·
    refine ⟨356904226487932690630429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1903489207935641016695621 356904226487932690630429)
    ·
      refine ⟨133839084932974758986411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356904226487932690630429 133839084932974758986411)
      ·
        refine ⟨200758627399462138479617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133839084932974758986411 200758627399462138479617)
        ·
          refine ⟨150568970549596603859713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200758627399462138479617 150568970549596603859713)
          ·
            refine ⟨112926727912197452894785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150568970549596603859713 112926727912197452894785)
            ·
              refine ⟨84695045934148089671089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112926727912197452894785 84695045934148089671089)
              ·
                refine ⟨63521284450611067253317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84695045934148089671089 63521284450611067253317)
                ·
                  refine ⟨11910240834489575109997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63521284450611067253317 11910240834489575109997)
                  ·
                    rfl

theorem cell21_52189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_52189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_52189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_52189 prefixEnd_52189 := by exact prefixLift 52189
  have htrace : WordTrace (prefixWord ++ tailWord_52189) baseStart_52189 baseEnd_52189 := by
    simpa [prefixWord, tailWord_52189, baseEnd_52189] using wordTrace_append hprefix tailTrace_52189
  have hstable : (prefixWord ++ tailWord_52189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52189).length < 2 ^ (prefixWord ++ tailWord_52189).sum := by decide
  have hdescent : baseEnd_52189 < baseStart_52189 := by decide
  rcases family_descends (prefixWord ++ tailWord_52189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52231 : List Nat := [1, 1, 4, 3, 1, 1, 2, 2, 6]
def baseStart_52231 : Nat := 118140960795 + 52231 * 2 ^ 59
def prefixEnd_52231 : Nat := 4983230072969 + 3 ^ 40 * 52231 * 2
def baseEnd_52231 : Nat := 11919825806706835409911

theorem tailTrace_52231 : CollatzResearch.WordTrace tailWord_52231 prefixEnd_52231 11919825806706835409911 := by
  unfold tailWord_52231
  simp only [CollatzResearch.WordTrace]
  refine ⟨1905021073783482189724547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1270014049188988126483031 1905021073783482189724547)
  ·
    refine ⟨2857531610675223284586821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1905021073783482189724547 2857531610675223284586821)
    ·
      refine ⟨535787177001604365860029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2857531610675223284586821 535787177001604365860029)
      ·
        refine ⟨200920191375601637197511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 535787177001604365860029 200920191375601637197511)
        ·
          refine ⟨301380287063402455796267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200920191375601637197511 301380287063402455796267)
          ·
            refine ⟨452070430595103683694401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301380287063402455796267 452070430595103683694401)
            ·
              refine ⟨339052822946327762770801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 452070430595103683694401 339052822946327762770801)
              ·
                refine ⟨254289617209745822078101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339052822946327762770801 254289617209745822078101)
                ·
                  refine ⟨11919825806706835409911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 254289617209745822078101 11919825806706835409911)
                  ·
                    rfl

theorem cell21_52231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 6].length) (baseStart_52231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_52231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_52231 prefixEnd_52231 := by exact prefixLift 52231
  have htrace : WordTrace (prefixWord ++ tailWord_52231) baseStart_52231 baseEnd_52231 := by
    simpa [prefixWord, tailWord_52231, baseEnd_52231] using wordTrace_append hprefix tailTrace_52231
  have hstable : (prefixWord ++ tailWord_52231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52231).length < 2 ^ (prefixWord ++ tailWord_52231).sum := by decide
  have hdescent : baseEnd_52231 < baseStart_52231 := by decide
  rcases family_descends (prefixWord ++ tailWord_52231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52234 : List Nat := [3, 1, 2, 2, 3, 1, 1, 5, 3]
def baseStart_52234 : Nat := 118140960795 + 52234 * 2 ^ 59
def prefixEnd_52234 : Nat := 4983230072969 + 3 ^ 40 * 52234 * 2
def baseEnd_52234 : Nat := 11920510447579496859905

theorem tailTrace_52234 : CollatzResearch.WordTrace tailWord_52234 prefixEnd_52234 11920510447579496859905 := by
  unfold tailWord_52234
  simp only [CollatzResearch.WordTrace]
  refine ⟨476282623193153425520939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1270086995181742468055837 476282623193153425520939)
  ·
    refine ⟨714423934789730138281409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 476282623193153425520939 714423934789730138281409)
    ·
      refine ⟨535817951092297603711057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 714423934789730138281409 535817951092297603711057)
      ·
        refine ⟨401863463319223202783293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 535817951092297603711057 401863463319223202783293)
        ·
          refine ⟨150698798744708701043735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 401863463319223202783293 150698798744708701043735)
          ·
            refine ⟨226048198117063051565603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150698798744708701043735 226048198117063051565603)
            ·
              refine ⟨339072297175594577348405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226048198117063051565603 339072297175594577348405)
              ·
                refine ⟨31788027860211991626413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 339072297175594577348405 31788027860211991626413)
                ·
                  refine ⟨11920510447579496859905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31788027860211991626413 11920510447579496859905)
                  ·
                    rfl

theorem cell21_52234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5, 3].length) (baseStart_52234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_52234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_52234 prefixEnd_52234 := by exact prefixLift 52234
  have htrace : WordTrace (prefixWord ++ tailWord_52234) baseStart_52234 baseEnd_52234 := by
    simpa [prefixWord, tailWord_52234, baseEnd_52234] using wordTrace_append hprefix tailTrace_52234
  have hstable : (prefixWord ++ tailWord_52234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52234).length < 2 ^ (prefixWord ++ tailWord_52234).sum := by decide
  have hdescent : baseEnd_52234 < baseStart_52234 := by decide
  rcases family_descends (prefixWord ++ tailWord_52234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52248 : List Nat := [2, 1, 2, 3, 2, 2, 3, 2, 4]
def baseStart_52248 : Nat := 118140960795 + 52248 * 2 ^ 59
def prefixEnd_52248 : Nat := 4983230072969 + 3 ^ 40 * 52248 * 2
def baseEnd_52248 : Nat := 11923705438318583626543

theorem tailTrace_52248 : CollatzResearch.WordTrace tailWord_52248 prefixEnd_52248 11923705438318583626543 := by
  unfold tailWord_52248
  simp only [CollatzResearch.WordTrace]
  refine ⟨952820557360947046546699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1270427409814596062062265 952820557360947046546699)
  ·
    refine ⟨1429230836041420569820049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 952820557360947046546699 1429230836041420569820049)
    ·
      refine ⟨1071923127031065427365037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1429230836041420569820049 1071923127031065427365037)
      ·
        refine ⟨401971172636649535261889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1071923127031065427365037 401971172636649535261889)
        ·
          refine ⟨301478379477487151446417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401971172636649535261889 301478379477487151446417)
          ·
            refine ⟨226108784608115363584813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301478379477487151446417 226108784608115363584813)
            ·
              refine ⟨84790794228043261344305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226108784608115363584813 84790794228043261344305)
              ·
                refine ⟨63593095671032446008229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84790794228043261344305 63593095671032446008229)
                ·
                  refine ⟨11923705438318583626543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63593095671032446008229 11923705438318583626543)
                  ·
                    rfl

theorem cell21_52248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 4].length) (baseStart_52248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_52248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_52248 prefixEnd_52248 := by exact prefixLift 52248
  have htrace : WordTrace (prefixWord ++ tailWord_52248) baseStart_52248 baseEnd_52248 := by
    simpa [prefixWord, tailWord_52248, baseEnd_52248] using wordTrace_append hprefix tailTrace_52248
  have hstable : (prefixWord ++ tailWord_52248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52248).length < 2 ^ (prefixWord ++ tailWord_52248).sum := by decide
  have hdescent : baseEnd_52248 < baseStart_52248 := by decide
  rcases family_descends (prefixWord ++ tailWord_52248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52321 : List Nat := [1, 2, 3, 1, 1, 2, 3, 8]
def baseStart_52321 : Nat := 118140960795 + 52321 * 2 ^ 59
def prefixEnd_52321 : Nat := 4983230072969 + 3 ^ 40 * 52321 * 2
def baseEnd_52321 : Nat := 3980121677628892969909

theorem tailTrace_52321 : CollatzResearch.WordTrace tailWord_52321 prefixEnd_52321 3980121677628892969909 := by
  unfold tailWord_52321
  simp only [CollatzResearch.WordTrace]
  refine ⟨1908303643457427560500817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1272202428971618373667211 1908303643457427560500817)
  ·
    refine ⟨1431227732593070670375613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1908303643457427560500817 1431227732593070670375613)
    ·
      refine ⟨536710399722401501390855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1431227732593070670375613 536710399722401501390855)
      ·
        refine ⟨805065599583602252086283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536710399722401501390855 805065599583602252086283)
        ·
          refine ⟨1207598399375403378129425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 805065599583602252086283 1207598399375403378129425)
          ·
            refine ⟨905698799531552533597069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1207598399375403378129425 905698799531552533597069)
            ·
              refine ⟨339637049824332200098901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 905698799531552533597069 339637049824332200098901)
              ·
                refine ⟨3980121677628892969909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 339637049824332200098901 3980121677628892969909)
                ·
                  rfl

theorem cell21_52321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 8].length) (baseStart_52321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_52321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_52321 prefixEnd_52321 := by exact prefixLift 52321
  have htrace : WordTrace (prefixWord ++ tailWord_52321) baseStart_52321 baseEnd_52321 := by
    simpa [prefixWord, tailWord_52321, baseEnd_52321] using wordTrace_append hprefix tailTrace_52321
  have hstable : (prefixWord ++ tailWord_52321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52321).length < 2 ^ (prefixWord ++ tailWord_52321).sum := by decide
  have hdescent : baseEnd_52321 < baseStart_52321 := by decide
  rcases family_descends (prefixWord ++ tailWord_52321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52386 : List Nat := [3, 3, 1, 3, 2, 1, 1, 2, 5]
def baseStart_52386 : Nat := 118140960795 + 52386 * 2 ^ 59
def prefixEnd_52386 : Nat := 4983230072969 + 3 ^ 40 * 52386 * 2
def baseEnd_52386 : Nat := 11955198918461010326261

theorem tailTrace_52386 : CollatzResearch.WordTrace tailWord_52386 prefixEnd_52386 11955198918461010326261 := by
  unfold tailWord_52386
  simp only [CollatzResearch.WordTrace]
  refine ⟨477668597055485915404253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1273782925481295774411341 477668597055485915404253)
  ·
    refine ⟨179125723895807218276595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 477668597055485915404253 179125723895807218276595)
    ·
      refine ⟨268688585843710827414893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179125723895807218276595 268688585843710827414893)
      ·
        refine ⟨100758219691391560280585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268688585843710827414893 100758219691391560280585)
        ·
          refine ⟨75568664768543670210439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100758219691391560280585 75568664768543670210439)
          ·
            refine ⟨113352997152815505315659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75568664768543670210439 113352997152815505315659)
            ·
              refine ⟨170029495729223257973489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113352997152815505315659 170029495729223257973489)
              ·
                refine ⟨127522121796917443480117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170029495729223257973489 127522121796917443480117)
                ·
                  refine ⟨11955198918461010326261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127522121796917443480117 11955198918461010326261)
                  ·
                    rfl

theorem cell21_52386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_52386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_52386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_52386 prefixEnd_52386 := by exact prefixLift 52386
  have htrace : WordTrace (prefixWord ++ tailWord_52386) baseStart_52386 baseEnd_52386 := by
    simpa [prefixWord, tailWord_52386, baseEnd_52386] using wordTrace_append hprefix tailTrace_52386
  have hstable : (prefixWord ++ tailWord_52386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52386).length < 2 ^ (prefixWord ++ tailWord_52386).sum := by decide
  have hdescent : baseEnd_52386 < baseStart_52386 := by decide
  rcases family_descends (prefixWord ++ tailWord_52386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52414 : List Nat := [4, 2, 1, 1, 3, 2, 8]
def baseStart_52414 : Nat := 118140960795 + 52414 * 2 ^ 59
def prefixEnd_52414 : Nat := 4983230072969 + 3 ^ 40 * 52414 * 2
def baseEnd_52414 : Nat := 1329065433326575984393

theorem tailTrace_52414 : CollatzResearch.WordTrace tailWord_52414 prefixEnd_52414 1329065433326575984393 := by
  unfold tailWord_52414
  simp only [CollatzResearch.WordTrace]
  refine ⟨238961954015063055454537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1274463754747002962424197 238961954015063055454537)
  ·
    refine ⟨179221465511297291590903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238961954015063055454537 179221465511297291590903)
    ·
      refine ⟨268832198266945937386355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179221465511297291590903 268832198266945937386355)
      ·
        refine ⟨403248297400418906079533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268832198266945937386355 403248297400418906079533)
        ·
          refine ⟨151218111525157089779825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 403248297400418906079533 151218111525157089779825)
          ·
            refine ⟨113413583643867817334869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151218111525157089779825 113413583643867817334869)
            ·
              refine ⟨1329065433326575984393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 113413583643867817334869 1329065433326575984393)
              ·
                rfl

theorem cell21_52414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 8].length) (baseStart_52414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_52414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_52414 prefixEnd_52414 := by exact prefixLift 52414
  have htrace : WordTrace (prefixWord ++ tailWord_52414) baseStart_52414 baseEnd_52414 := by
    simpa [prefixWord, tailWord_52414, baseEnd_52414] using wordTrace_append hprefix tailTrace_52414
  have hstable : (prefixWord ++ tailWord_52414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52414).length < 2 ^ (prefixWord ++ tailWord_52414).sum := by decide
  have hdescent : baseEnd_52414 < baseStart_52414 := by decide
  rcases family_descends (prefixWord ++ tailWord_52414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52417 : List Nat := [1, 2, 6, 1, 1, 1, 3, 2, 4]
def baseStart_52417 : Nat := 118140960795 + 52417 * 2 ^ 59
def prefixEnd_52417 : Nat := 4983230072969 + 3 ^ 40 * 52417 * 2
def baseEnd_52417 : Nat := 11962273540811845309531

theorem tailTrace_52417 : CollatzResearch.WordTrace tailWord_52417 prefixEnd_52417 11962273540811845309531 := by
  unfold tailWord_52417
  simp only [CollatzResearch.WordTrace]
  refine ⟨1911805051109635955995505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1274536700739757303997003 1911805051109635955995505)
  ·
    refine ⟨1433853788332226966996629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1911805051109635955995505 1433853788332226966996629)
    ·
      refine ⟨67211896328073139077967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1433853788332226966996629 67211896328073139077967)
      ·
        refine ⟨100817844492109708616951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67211896328073139077967 100817844492109708616951)
        ·
          refine ⟨151226766738164562925427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100817844492109708616951 151226766738164562925427)
          ·
            refine ⟨226840150107246844388141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151226766738164562925427 226840150107246844388141)
            ·
              refine ⟨85065056290217566645553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226840150107246844388141 85065056290217566645553)
              ·
                refine ⟨63798792217663174984165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85065056290217566645553 63798792217663174984165)
                ·
                  refine ⟨11962273540811845309531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63798792217663174984165 11962273540811845309531)
                  ·
                    rfl

theorem cell21_52417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 4].length) (baseStart_52417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_52417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_52417 prefixEnd_52417 := by exact prefixLift 52417
  have htrace : WordTrace (prefixWord ++ tailWord_52417) baseStart_52417 baseEnd_52417 := by
    simpa [prefixWord, tailWord_52417, baseEnd_52417] using wordTrace_append hprefix tailTrace_52417
  have hstable : (prefixWord ++ tailWord_52417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52417).length < 2 ^ (prefixWord ++ tailWord_52417).sum := by decide
  have hdescent : baseEnd_52417 < baseStart_52417 := by decide
  rcases family_descends (prefixWord ++ tailWord_52417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52462 : List Nat := [4, 1, 2, 1, 1, 1, 5, 3, 3]
def baseStart_52462 : Nat := 118140960795 + 52462 * 2 ^ 59
def prefixEnd_52462 : Nat := 4983230072969 + 3 ^ 40 * 52462 * 2
def baseEnd_52462 : Nat := 11972543153901767059439

theorem tailTrace_52462 : CollatzResearch.WordTrace tailWord_52462 prefixEnd_52462 11972543153901767059439 := by
  unfold tailWord_52462
  simp only [CollatzResearch.WordTrace]
  refine ⟨239180791993326080172955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1275630890631072427589093 239180791993326080172955)
  ·
    refine ⟨358771187989989120259433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239180791993326080172955 358771187989989120259433)
    ·
      refine ⟨269078390992491840194575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358771187989989120259433 269078390992491840194575)
      ·
        refine ⟨403617586488737760291863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269078390992491840194575 403617586488737760291863)
        ·
          refine ⟨605426379733106640437795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403617586488737760291863 605426379733106640437795)
          ·
            refine ⟨908139569599659960656693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605426379733106640437795 908139569599659960656693)
            ·
              refine ⟨85138084649968121311565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 908139569599659960656693 85138084649968121311565)
              ·
                refine ⟨31926781743738045491837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85138084649968121311565 31926781743738045491837)
                ·
                  refine ⟨11972543153901767059439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31926781743738045491837 11972543153901767059439)
                  ·
                    rfl

theorem cell21_52462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_52462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_52462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_52462 prefixEnd_52462 := by exact prefixLift 52462
  have htrace : WordTrace (prefixWord ++ tailWord_52462) baseStart_52462 baseEnd_52462 := by
    simpa [prefixWord, tailWord_52462, baseEnd_52462] using wordTrace_append hprefix tailTrace_52462
  have hstable : (prefixWord ++ tailWord_52462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52462).length < 2 ^ (prefixWord ++ tailWord_52462).sum := by decide
  have hdescent : baseEnd_52462 < baseStart_52462 := by decide
  rcases family_descends (prefixWord ++ tailWord_52462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52586 : List Nat := [3, 1, 3, 3, 3, 1, 1, 2, 4]
def baseStart_52586 : Nat := 118140960795 + 52586 * 2 ^ 59
def prefixEnd_52586 : Nat := 4983230072969 + 3 ^ 40 * 52586 * 2
def baseEnd_52586 : Nat := 12000841643305106992519

theorem tailTrace_52586 : CollatzResearch.WordTrace tailWord_52586 prefixEnd_52586 12000841643305106992519 := by
  unfold tailWord_52586
  simp only [CollatzResearch.WordTrace]
  refine ⟨479492246874344454724403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1278645991664918545931741 479492246874344454724403)
  ·
    refine ⟨719238370311516682086605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 479492246874344454724403 719238370311516682086605)
    ·
      refine ⟨269714388866818755782477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 719238370311516682086605 269714388866818755782477)
      ·
        refine ⟨101142895825057033418429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269714388866818755782477 101142895825057033418429)
        ·
          refine ⟨37928585934396387531911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101142895825057033418429 37928585934396387531911)
          ·
            refine ⟨56892878901594581297867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37928585934396387531911 56892878901594581297867)
            ·
              refine ⟨85339318352391871946801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56892878901594581297867 85339318352391871946801)
              ·
                refine ⟨64004488764293903960101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85339318352391871946801 64004488764293903960101)
                ·
                  refine ⟨12000841643305106992519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64004488764293903960101 12000841643305106992519)
                  ·
                    rfl

theorem cell21_52586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 4].length) (baseStart_52586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_52586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_52586 prefixEnd_52586 := by exact prefixLift 52586
  have htrace : WordTrace (prefixWord ++ tailWord_52586) baseStart_52586 baseEnd_52586 := by
    simpa [prefixWord, tailWord_52586, baseEnd_52586] using wordTrace_append hprefix tailTrace_52586
  have hstable : (prefixWord ++ tailWord_52586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52586).length < 2 ^ (prefixWord ++ tailWord_52586).sum := by decide
  have hdescent : baseEnd_52586 < baseStart_52586 := by decide
  rcases family_descends (prefixWord ++ tailWord_52586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52642 : List Nat := [3, 3, 1, 2, 1, 4, 7]
def baseStart_52642 : Nat := 118140960795 + 52642 * 2 ^ 59
def prefixEnd_52642 : Nat := 4983230072969 + 3 ^ 40 * 52642 * 2
def baseEnd_52642 : Nat := 1334846845140161562119

theorem tailTrace_52642 : CollatzResearch.WordTrace tailWord_52642 prefixEnd_52642 1334846845140161562119 := by
  unfold tailWord_52642
  simp only [CollatzResearch.WordTrace]
  refine ⟨480002868823624845734045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1280007650196332921957453 480002868823624845734045)
  ·
    refine ⟨180001075808859317150267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 480002868823624845734045 180001075808859317150267)
    ·
      refine ⟨270001613713288975725401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180001075808859317150267 270001613713288975725401)
      ·
        refine ⟨202501210284966731794051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270001613713288975725401 202501210284966731794051)
        ·
          refine ⟨303751815427450097691077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202501210284966731794051 303751815427450097691077)
          ·
            refine ⟨56953465392646893317077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 303751815427450097691077 56953465392646893317077)
            ·
              refine ⟨1334846845140161562119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 56953465392646893317077 1334846845140161562119)
              ·
                rfl

theorem cell21_52642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 7].length) (baseStart_52642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_52642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_52642 prefixEnd_52642 := by exact prefixLift 52642
  have htrace : WordTrace (prefixWord ++ tailWord_52642) baseStart_52642 baseEnd_52642 := by
    simpa [prefixWord, tailWord_52642, baseEnd_52642] using wordTrace_append hprefix tailTrace_52642
  have hstable : (prefixWord ++ tailWord_52642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52642).length < 2 ^ (prefixWord ++ tailWord_52642).sum := by decide
  have hdescent : baseEnd_52642 < baseStart_52642 := by decide
  rcases family_descends (prefixWord ++ tailWord_52642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52648 : List Nat := [2, 1, 6, 1, 2, 1, 3, 2, 3]
def baseStart_52648 : Nat := 118140960795 + 52648 * 2 ^ 59
def prefixEnd_52648 : Nat := 4983230072969 + 3 ^ 40 * 52648 * 2
def baseEnd_52648 : Nat := 12014990888006776959059

theorem tailTrace_52648 : CollatzResearch.WordTrace tailWord_52648 prefixEnd_52648 12014990888006776959059 := by
  unfold tailWord_52648
  simp only [CollatzResearch.WordTrace]
  refine ⟨960115156636381203827299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1280153542181841605103065 960115156636381203827299)
  ·
    refine ⟨1440172734954571805740949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 960115156636381203827299 1440172734954571805740949)
    ·
      refine ⟨67508096950995553394107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1440172734954571805740949 67508096950995553394107)
      ·
        refine ⟨101262145426493330091161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67508096950995553394107 101262145426493330091161)
        ·
          refine ⟨75946609069869997568371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101262145426493330091161 75946609069869997568371)
          ·
            refine ⟨113919913604804996352557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75946609069869997568371 113919913604804996352557)
            ·
              refine ⟨42719967601801873632209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113919913604804996352557 42719967601801873632209)
              ·
                refine ⟨32039975701351405224157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42719967601801873632209 32039975701351405224157)
                ·
                  refine ⟨12014990888006776959059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32039975701351405224157 12014990888006776959059)
                  ·
                    rfl

theorem cell21_52648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2, 3].length) (baseStart_52648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_52648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_52648 prefixEnd_52648 := by exact prefixLift 52648
  have htrace : WordTrace (prefixWord ++ tailWord_52648) baseStart_52648 baseEnd_52648 := by
    simpa [prefixWord, tailWord_52648, baseEnd_52648] using wordTrace_append hprefix tailTrace_52648
  have hstable : (prefixWord ++ tailWord_52648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52648).length < 2 ^ (prefixWord ++ tailWord_52648).sum := by decide
  have hdescent : baseEnd_52648 < baseStart_52648 := by decide
  rcases family_descends (prefixWord ++ tailWord_52648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52701 : List Nat := [1, 4, 3, 1, 1, 11]
def baseStart_52701 : Nat := 118140960795 + 52701 * 2 ^ 59
def prefixEnd_52701 : Nat := 4983230072969 + 3 ^ 40 * 52701 * 2
def baseEnd_52701 : Nat := 445447637410757873171

theorem tailTrace_52701 : CollatzResearch.WordTrace tailWord_52701 prefixEnd_52701 445447637410757873171 := by
  unfold tailWord_52701
  simp only [CollatzResearch.WordTrace]
  refine ⟨1922163382080752459333957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1281442254720501639555971 1922163382080752459333957)
  ·
    refine ⟨360405634140141086125117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1922163382080752459333957 360405634140141086125117)
    ·
      refine ⟨135152112802552907296919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360405634140141086125117 135152112802552907296919)
      ·
        refine ⟨202728169203829360945379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135152112802552907296919 202728169203829360945379)
        ·
          refine ⟨304092253805744041418069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202728169203829360945379 304092253805744041418069)
          ·
            refine ⟨445447637410757873171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 304092253805744041418069 445447637410757873171)
            ·
              rfl

theorem cell21_52701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 11].length) (baseStart_52701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_52701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_52701 prefixEnd_52701 := by exact prefixLift 52701
  have htrace : WordTrace (prefixWord ++ tailWord_52701) baseStart_52701 baseEnd_52701 := by
    simpa [prefixWord, tailWord_52701, baseEnd_52701] using wordTrace_append hprefix tailTrace_52701
  have hstable : (prefixWord ++ tailWord_52701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52701).length < 2 ^ (prefixWord ++ tailWord_52701).sum := by decide
  have hdescent : baseEnd_52701 < baseStart_52701 := by decide
  rcases family_descends (prefixWord ++ tailWord_52701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52707 : List Nat := [1, 1, 1, 6, 2, 3, 2, 2, 3]
def baseStart_52707 : Nat := 118140960795 + 52707 * 2 ^ 59
def prefixEnd_52707 : Nat := 4983230072969 + 3 ^ 40 * 52707 * 2
def baseEnd_52707 : Nat := 12028455491835785475605

theorem tailTrace_52707 : CollatzResearch.WordTrace tailWord_52707 prefixEnd_52707 12028455491835785475605 := by
  unfold tailWord_52707
  simp only [CollatzResearch.WordTrace]
  refine ⟨1922382220059015484052375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1281588146706010322701583 1922382220059015484052375)
  ·
    refine ⟨2883573330088523226078563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1922382220059015484052375 2883573330088523226078563)
    ·
      refine ⟨4325359995132784839117845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2883573330088523226078563 4325359995132784839117845)
      ·
        refine ⟨202751249771849289333649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4325359995132784839117845 202751249771849289333649)
        ·
          refine ⟨152063437328886967000237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202751249771849289333649 152063437328886967000237)
          ·
            refine ⟨57023788998332612625089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152063437328886967000237 57023788998332612625089)
            ·
              refine ⟨42767841748749459468817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57023788998332612625089 42767841748749459468817)
              ·
                refine ⟨32075881311562094601613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42767841748749459468817 32075881311562094601613)
                ·
                  refine ⟨12028455491835785475605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32075881311562094601613 12028455491835785475605)
                  ·
                    rfl

theorem cell21_52707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2, 3].length) (baseStart_52707 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_52707 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_52707 prefixEnd_52707 := by exact prefixLift 52707
  have htrace : WordTrace (prefixWord ++ tailWord_52707) baseStart_52707 baseEnd_52707 := by
    simpa [prefixWord, tailWord_52707, baseEnd_52707] using wordTrace_append hprefix tailTrace_52707
  have hstable : (prefixWord ++ tailWord_52707).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52707).length < 2 ^ (prefixWord ++ tailWord_52707).sum := by decide
  have hdescent : baseEnd_52707 < baseStart_52707 := by decide
  rcases family_descends (prefixWord ++ tailWord_52707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52912 : List Nat := [2, 1, 1, 1, 2, 1, 4, 9]
def baseStart_52912 : Nat := 118140960795 + 52912 * 2 ^ 59
def prefixEnd_52912 : Nat := 4983230072969 + 3 ^ 40 * 52912 * 2
def baseEnd_52912 : Nat := 4025079761600328186173

theorem tailTrace_52912 : CollatzResearch.WordTrace tailWord_52912 prefixEnd_52912 4025079761600328186173 := by
  unfold tailWord_52912
  simp only [CollatzResearch.WordTrace]
  refine ⟨964929592158167747632495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1286572789544223663509993 964929592158167747632495)
  ·
    refine ⟨1447394388237251621448743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 964929592158167747632495 1447394388237251621448743)
    ·
      refine ⟨2171091582355877432173115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1447394388237251621448743 2171091582355877432173115)
      ·
        refine ⟨3256637373533816148259673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2171091582355877432173115 3256637373533816148259673)
        ·
          refine ⟨2442478030150362111194755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3256637373533816148259673 2442478030150362111194755)
          ·
            refine ⟨3663717045225543166792133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2442478030150362111194755 3663717045225543166792133)
            ·
              refine ⟨686946945979789343773525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3663717045225543166792133 686946945979789343773525)
              ·
                refine ⟨4025079761600328186173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 686946945979789343773525 4025079761600328186173)
                ·
                  rfl

theorem cell21_52912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 9].length) (baseStart_52912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_52912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_52912 prefixEnd_52912 := by exact prefixLift 52912
  have htrace : WordTrace (prefixWord ++ tailWord_52912) baseStart_52912 baseEnd_52912 := by
    simpa [prefixWord, tailWord_52912, baseEnd_52912] using wordTrace_append hprefix tailTrace_52912
  have hstable : (prefixWord ++ tailWord_52912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52912).length < 2 ^ (prefixWord ++ tailWord_52912).sum := by decide
  have hdescent : baseEnd_52912 < baseStart_52912 := by decide
  rcases family_descends (prefixWord ++ tailWord_52912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52963 : List Nat := [1, 1, 1, 7, 2, 2, 2, 5]
def baseStart_52963 : Nat := 118140960795 + 52963 * 2 ^ 59
def prefixEnd_52963 : Nat := 4983230072969 + 3 ^ 40 * 52963 * 2
def baseEnd_52963 : Nat := 4028959393212076402805

theorem tailTrace_52963 : CollatzResearch.WordTrace tailWord_52963 prefixEnd_52963 4028959393212076402805 := by
  unfold tailWord_52963
  simp only [CollatzResearch.WordTrace]
  refine ⟨1931719307131571205371543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1287812871421047470247695 1931719307131571205371543)
  ·
    refine ⟨2897578960697356808057315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1931719307131571205371543 2897578960697356808057315)
    ·
      refine ⟨4346368441046035212085973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2897578960697356808057315 4346368441046035212085973)
      ·
        refine ⟨101868010337016450283265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 4346368441046035212085973 101868010337016450283265)
        ·
          refine ⟨76401007752762337712449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101868010337016450283265 76401007752762337712449)
          ·
            refine ⟨57300755814571753284337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76401007752762337712449 57300755814571753284337)
            ·
              refine ⟨42975566860928814963253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57300755814571753284337 42975566860928814963253)
              ·
                refine ⟨4028959393212076402805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42975566860928814963253 4028959393212076402805)
                ·
                  rfl

theorem cell21_52963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 5].length) (baseStart_52963 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_52963 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_52963 prefixEnd_52963 := by exact prefixLift 52963
  have htrace : WordTrace (prefixWord ++ tailWord_52963) baseStart_52963 baseEnd_52963 := by
    simpa [prefixWord, tailWord_52963, baseEnd_52963] using wordTrace_append hprefix tailTrace_52963
  have hstable : (prefixWord ++ tailWord_52963).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52963).length < 2 ^ (prefixWord ++ tailWord_52963).sum := by decide
  have hdescent : baseEnd_52963 < baseStart_52963 := by decide
  rcases family_descends (prefixWord ++ tailWord_52963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52974 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 8]
def baseStart_52974 : Nat := 118140960795 + 52974 * 2 ^ 59
def prefixEnd_52974 : Nat := 4983230072969 + 3 ^ 40 * 52974 * 2
def baseEnd_52974 : Nat := 12089388529502654525059

theorem tailTrace_52974 : CollatzResearch.WordTrace tailWord_52974 prefixEnd_52974 12089388529502654525059 := by
  unfold tailWord_52974
  simp only [CollatzResearch.WordTrace]
  refine ⟨241515063761465010502747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1288080340061146722681317 241515063761465010502747)
  ·
    refine ⟨362272595642197515754121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241515063761465010502747 362272595642197515754121)
    ·
      refine ⟨271704446731648136815591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362272595642197515754121 271704446731648136815591)
      ·
        refine ⟨407556670097472205223387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271704446731648136815591 407556670097472205223387)
        ·
          refine ⟨611335005146208307835081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407556670097472205223387 611335005146208307835081)
          ·
            refine ⟨458501253859656230876311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 611335005146208307835081 458501253859656230876311)
            ·
              refine ⟨687751880789484346314467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458501253859656230876311 687751880789484346314467)
              ·
                refine ⟨1031627821184226519471701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 687751880789484346314467 1031627821184226519471701)
                ·
                  refine ⟨12089388529502654525059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1031627821184226519471701 12089388529502654525059)
                  ·
                    rfl

theorem cell21_52974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_52974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_52974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_52974 prefixEnd_52974 := by exact prefixLift 52974
  have htrace : WordTrace (prefixWord ++ tailWord_52974) baseStart_52974 baseEnd_52974 := by
    simpa [prefixWord, tailWord_52974, baseEnd_52974] using wordTrace_append hprefix tailTrace_52974
  have hstable : (prefixWord ++ tailWord_52974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52974).length < 2 ^ (prefixWord ++ tailWord_52974).sum := by decide
  have hdescent : baseEnd_52974 < baseStart_52974 := by decide
  rcases family_descends (prefixWord ++ tailWord_52974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52977 : List Nat := [1, 2, 2, 2, 2, 3, 3, 3, 3]
def baseStart_52977 : Nat := 118140960795 + 52977 * 2 ^ 59
def prefixEnd_52977 : Nat := 4983230072969 + 3 ^ 40 * 52977 * 2
def baseEnd_52977 : Nat := 12090073170375315975053

theorem tailTrace_52977 : CollatzResearch.WordTrace tailWord_52977 prefixEnd_52977 12090073170375315975053 := by
  unfold tailWord_52977
  simp only [CollatzResearch.WordTrace]
  refine ⟨1932229929080851596381185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1288153286053901064254123 1932229929080851596381185)
  ·
    refine ⟨1449172446810638697285889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1932229929080851596381185 1449172446810638697285889)
    ·
      refine ⟨1086879335107979022964417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1449172446810638697285889 1086879335107979022964417)
      ·
        refine ⟨815159501330984267223313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1086879335107979022964417 815159501330984267223313)
        ·
          refine ⟨611369625998238200417485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 815159501330984267223313 611369625998238200417485)
          ·
            refine ⟨229263609749339325156557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 611369625998238200417485 229263609749339325156557)
            ·
              refine ⟨85973853656002246933709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229263609749339325156557 85973853656002246933709)
              ·
                refine ⟨32240195121000842600141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85973853656002246933709 32240195121000842600141)
                ·
                  refine ⟨12090073170375315975053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32240195121000842600141 12090073170375315975053)
                  ·
                    rfl

theorem cell21_52977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3].length) (baseStart_52977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_52977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_52977 prefixEnd_52977 := by exact prefixLift 52977
  have htrace : WordTrace (prefixWord ++ tailWord_52977) baseStart_52977 baseEnd_52977 := by
    simpa [prefixWord, tailWord_52977, baseEnd_52977] using wordTrace_append hprefix tailTrace_52977
  have hstable : (prefixWord ++ tailWord_52977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52977).length < 2 ^ (prefixWord ++ tailWord_52977).sum := by decide
  have hdescent : baseEnd_52977 < baseStart_52977 := by decide
  rcases family_descends (prefixWord ++ tailWord_52977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53081 : List Nat := [1, 2, 1, 2, 2, 3, 5, 5]
def baseStart_53081 : Nat := 118140960795 + 53081 * 2 ^ 59
def prefixEnd_53081 : Nat := 4983230072969 + 3 ^ 40 * 53081 * 2
def baseEnd_53081 : Nat := 4037935795764748747169

theorem tailTrace_53081 : CollatzResearch.WordTrace tailWord_53081 prefixEnd_53081 4037935795764748747169 := by
  unfold tailWord_53081
  simp only [CollatzResearch.WordTrace]
  refine ⟨1936023120704077358167097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1290682080469384905444731 1936023120704077358167097)
  ·
    refine ⟨1452017340528058018625323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1936023120704077358167097 1452017340528058018625323)
    ·
      refine ⟨2178026010792087027937985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1452017340528058018625323 2178026010792087027937985)
      ·
        refine ⟨1633519508094065270953489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2178026010792087027937985 1633519508094065270953489)
        ·
          refine ⟨1225139631070548953215117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1633519508094065270953489 1225139631070548953215117)
          ·
            refine ⟨459427361651455857455669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1225139631070548953215117 459427361651455857455669)
            ·
              refine ⟨43071315154823986636469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 459427361651455857455669 43071315154823986636469)
              ·
                refine ⟨4037935795764748747169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43071315154823986636469 4037935795764748747169)
                ·
                  rfl

theorem cell21_53081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 5].length) (baseStart_53081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_53081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_53081 prefixEnd_53081 := by exact prefixLift 53081
  have htrace : WordTrace (prefixWord ++ tailWord_53081) baseStart_53081 baseEnd_53081 := by
    simpa [prefixWord, tailWord_53081, baseEnd_53081] using wordTrace_append hprefix tailTrace_53081
  have hstable : (prefixWord ++ tailWord_53081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53081).length < 2 ^ (prefixWord ++ tailWord_53081).sum := by decide
  have hdescent : baseEnd_53081 < baseStart_53081 := by decide
  rcases family_descends (prefixWord ++ tailWord_53081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53095 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 7]
def baseStart_53095 : Nat := 118140960795 + 53095 * 2 ^ 59
def prefixEnd_53095 : Nat := 4983230072969 + 3 ^ 40 * 53095 * 2
def baseEnd_53095 : Nat := 12117002378033333008145

theorem tailTrace_53095 : CollatzResearch.WordTrace tailWord_53095 prefixEnd_53095 12117002378033333008145 := by
  unfold tailWord_53095
  simp only [CollatzResearch.WordTrace]
  refine ⟨1936533742653357749176739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1291022495102238499451159 1936533742653357749176739)
  ·
    refine ⟨2904800613980036623765109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1936533742653357749176739 2904800613980036623765109)
    ·
      refine ⟨272325057560628433477979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2904800613980036623765109 272325057560628433477979)
      ·
        refine ⟨408487586340942650216969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272325057560628433477979 408487586340942650216969)
        ·
          refine ⟨306365689755706987662727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408487586340942650216969 306365689755706987662727)
          ·
            refine ⟨459548534633560481494091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306365689755706987662727 459548534633560481494091)
            ·
              refine ⟨689322801950340722241137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459548534633560481494091 689322801950340722241137)
              ·
                refine ⟨516992101462755541680853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 689322801950340722241137 516992101462755541680853)
                ·
                  refine ⟨12117002378033333008145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 516992101462755541680853 12117002378033333008145)
                  ·
                    rfl

theorem cell21_53095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 7].length) (baseStart_53095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_53095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_53095 prefixEnd_53095 := by exact prefixLift 53095
  have htrace : WordTrace (prefixWord ++ tailWord_53095) baseStart_53095 baseEnd_53095 := by
    simpa [prefixWord, tailWord_53095, baseEnd_53095] using wordTrace_append hprefix tailTrace_53095
  have hstable : (prefixWord ++ tailWord_53095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53095).length < 2 ^ (prefixWord ++ tailWord_53095).sum := by decide
  have hdescent : baseEnd_53095 < baseStart_53095 := by decide
  rcases family_descends (prefixWord ++ tailWord_53095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53098 : List Nat := [3, 1, 3, 4, 1, 1, 8]
def baseStart_53098 : Nat := 118140960795 + 53098 * 2 ^ 59
def prefixEnd_53098 : Nat := 4983230072969 + 3 ^ 40 * 53098 * 2
def baseEnd_53098 : Nat := 1346409668767332717571

theorem tailTrace_53098 : CollatzResearch.WordTrace tailWord_53098 prefixEnd_53098 1346409668767332717571 := by
  unfold tailWord_53098
  simp only [CollatzResearch.WordTrace]
  refine ⟨484160790410622315383987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1291095441094992841023965 484160790410622315383987)
  ·
    refine ⟨726241185615933473075981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 484160790410622315383987 726241185615933473075981)
    ·
      refine ⟨272340444605975052403493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 726241185615933473075981 272340444605975052403493)
      ·
        refine ⟨51063833363620322325655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272340444605975052403493 51063833363620322325655)
        ·
          refine ⟨76595750045430483488483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51063833363620322325655 76595750045430483488483)
          ·
            refine ⟨114893625068145725232725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76595750045430483488483 114893625068145725232725)
            ·
              refine ⟨1346409668767332717571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 114893625068145725232725 1346409668767332717571)
              ·
                rfl

theorem cell21_53098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 8].length) (baseStart_53098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_53098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_53098 prefixEnd_53098 := by exact prefixLift 53098
  have htrace : WordTrace (prefixWord ++ tailWord_53098) baseStart_53098 baseEnd_53098 := by
    simpa [prefixWord, tailWord_53098, baseEnd_53098] using wordTrace_append hprefix tailTrace_53098
  have hstable : (prefixWord ++ tailWord_53098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53098).length < 2 ^ (prefixWord ++ tailWord_53098).sum := by decide
  have hdescent : baseEnd_53098 < baseStart_53098 := by decide
  rcases family_descends (prefixWord ++ tailWord_53098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53146 : List Nat := [3, 1, 1, 4, 2, 3, 1, 3, 3]
def baseStart_53146 : Nat := 118140960795 + 53146 * 2 ^ 59
def prefixEnd_53146 : Nat := 4983230072969 + 3 ^ 40 * 53146 * 2
def baseEnd_53146 : Nat := 12128641272868577658041

theorem tailTrace_53146 : CollatzResearch.WordTrace tailWord_53146 prefixEnd_53146 12128641272868577658041 := by
  unfold tailWord_53146
  simp only [CollatzResearch.WordTrace]
  refine ⟨484598466367148364820823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1292262576979062306188861 484598466367148364820823)
  ·
    refine ⟨726897699550722547231235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 484598466367148364820823 726897699550722547231235)
    ·
      refine ⟨1090346549326083820846853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 726897699550722547231235 1090346549326083820846853)
      ·
        refine ⟨204439977998640716408785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1090346549326083820846853 204439977998640716408785)
        ·
          refine ⟨153329983498980537306589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204439977998640716408785 153329983498980537306589)
          ·
            refine ⟨57498743812117701489971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153329983498980537306589 57498743812117701489971)
            ·
              refine ⟨86248115718176552234957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57498743812117701489971 86248115718176552234957)
              ·
                refine ⟨32343043394316207088109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86248115718176552234957 32343043394316207088109)
                ·
                  refine ⟨12128641272868577658041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32343043394316207088109 12128641272868577658041)
                  ·
                    rfl

theorem cell21_53146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3, 3].length) (baseStart_53146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_53146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_53146 prefixEnd_53146 := by exact prefixLift 53146
  have htrace : WordTrace (prefixWord ++ tailWord_53146) baseStart_53146 baseEnd_53146 := by
    simpa [prefixWord, tailWord_53146, baseEnd_53146] using wordTrace_append hprefix tailTrace_53146
  have hstable : (prefixWord ++ tailWord_53146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53146).length < 2 ^ (prefixWord ++ tailWord_53146).sum := by decide
  have hdescent : baseEnd_53146 < baseStart_53146 := by decide
  rcases family_descends (prefixWord ++ tailWord_53146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53219 : List Nat := [1, 1, 1, 6, 1, 3, 2, 2, 4]
def baseStart_53219 : Nat := 118140960795 + 53219 * 2 ^ 59
def prefixEnd_53219 : Nat := 4983230072969 + 3 ^ 40 * 53219 * 2
def baseEnd_53219 : Nat := 12145300867436672941225

theorem tailTrace_53219 : CollatzResearch.WordTrace tailWord_53219 prefixEnd_53219 12145300867436672941225 := by
  unfold tailWord_53219
  simp only [CollatzResearch.WordTrace]
  refine ⟨1941056394204126926690711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1294037596136084617793807 1941056394204126926690711)
  ·
    refine ⟨2911584591306190390036067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1941056394204126926690711 2911584591306190390036067)
    ·
      refine ⟨4367376886959285585054101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2911584591306190390036067 4367376886959285585054101)
      ·
        refine ⟨204720791576216511799411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4367376886959285585054101 204720791576216511799411)
        ·
          refine ⟨307081187364324767699117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204720791576216511799411 307081187364324767699117)
          ·
            refine ⟨115155445261621787887169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 307081187364324767699117 115155445261621787887169)
            ·
              refine ⟨86366583946216340915377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115155445261621787887169 86366583946216340915377)
              ·
                refine ⟨64774937959662255686533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86366583946216340915377 64774937959662255686533)
                ·
                  refine ⟨12145300867436672941225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64774937959662255686533 12145300867436672941225)
                  ·
                    rfl

theorem cell21_53219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 4].length) (baseStart_53219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_53219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_53219 prefixEnd_53219 := by exact prefixLift 53219
  have htrace : WordTrace (prefixWord ++ tailWord_53219) baseStart_53219 baseEnd_53219 := by
    simpa [prefixWord, tailWord_53219, baseEnd_53219] using wordTrace_append hprefix tailTrace_53219
  have hstable : (prefixWord ++ tailWord_53219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53219).length < 2 ^ (prefixWord ++ tailWord_53219).sum := by decide
  have hdescent : baseEnd_53219 < baseStart_53219 := by decide
  rcases family_descends (prefixWord ++ tailWord_53219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53337 : List Nat := [1, 2, 1, 2, 2, 1, 3, 3, 6]
def baseStart_53337 : Nat := 118140960795 + 53337 * 2 ^ 59
def prefixEnd_53337 : Nat := 4983230072969 + 3 ^ 40 * 53337 * 2
def baseEnd_53337 : Nat := 12172230075094689974317

theorem tailTrace_53337 : CollatzResearch.WordTrace tailWord_53337 prefixEnd_53337 12172230075094689974317 := by
  unfold tailWord_53337
  simp only [CollatzResearch.WordTrace]
  refine ⟨1945360207776633079486265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1296906805184422052990843 1945360207776633079486265)
  ·
    refine ⟨1459020155832474809614699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1945360207776633079486265 1459020155832474809614699)
    ·
      refine ⟨2188530233748712214422049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1459020155832474809614699 2188530233748712214422049)
      ·
        refine ⟨1641397675311534160816537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2188530233748712214422049 1641397675311534160816537)
        ·
          refine ⟨1231048256483650620612403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1641397675311534160816537 1231048256483650620612403)
          ·
            refine ⟨1846572384725475930918605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1231048256483650620612403 1846572384725475930918605)
            ·
              refine ⟨692464644272053474094477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1846572384725475930918605 692464644272053474094477)
              ·
                refine ⟨259674241602020052785429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 692464644272053474094477 259674241602020052785429)
                ·
                  refine ⟨12172230075094689974317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 259674241602020052785429 12172230075094689974317)
                  ·
                    rfl

theorem cell21_53337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 6].length) (baseStart_53337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_53337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_53337 prefixEnd_53337 := by exact prefixLift 53337
  have htrace : WordTrace (prefixWord ++ tailWord_53337) baseStart_53337 baseEnd_53337 := by
    simpa [prefixWord, tailWord_53337, baseEnd_53337] using wordTrace_append hprefix tailTrace_53337
  have hstable : (prefixWord ++ tailWord_53337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53337).length < 2 ^ (prefixWord ++ tailWord_53337).sum := by decide
  have hdescent : baseEnd_53337 < baseStart_53337 := by decide
  rcases family_descends (prefixWord ++ tailWord_53337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53340 : List Nat := [2, 2, 4, 1, 1, 2, 3, 1, 5]
def baseStart_53340 : Nat := 118140960795 + 53340 * 2 ^ 59
def prefixEnd_53340 : Nat := 4983230072969 + 3 ^ 40 * 53340 * 2
def baseEnd_53340 : Nat := 12172914715967351424311

theorem tailTrace_53340 : CollatzResearch.WordTrace tailWord_53340 prefixEnd_53340 12172914715967351424311 := by
  unfold tailWord_53340
  simp only [CollatzResearch.WordTrace]
  refine ⟨972734813382882295922737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1296979751177176394563649 972734813382882295922737)
  ·
    refine ⟨729551110037161721942053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 972734813382882295922737 729551110037161721942053)
    ·
      refine ⟨136790833131967822864135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 729551110037161721942053 136790833131967822864135)
      ·
        refine ⟨205186249697951734296203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136790833131967822864135 205186249697951734296203)
        ·
          refine ⟨307779374546927601444305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205186249697951734296203 307779374546927601444305)
          ·
            refine ⟨230834530910195701083229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307779374546927601444305 230834530910195701083229)
            ·
              refine ⟨86562949091323387906211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230834530910195701083229 86562949091323387906211)
              ·
                refine ⟨129844423636985081859317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86562949091323387906211 129844423636985081859317)
                ·
                  refine ⟨12172914715967351424311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129844423636985081859317 12172914715967351424311)
                  ·
                    rfl

theorem cell21_53340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_53340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_53340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_53340 prefixEnd_53340 := by exact prefixLift 53340
  have htrace : WordTrace (prefixWord ++ tailWord_53340) baseStart_53340 baseEnd_53340 := by
    simpa [prefixWord, tailWord_53340, baseEnd_53340] using wordTrace_append hprefix tailTrace_53340
  have hstable : (prefixWord ++ tailWord_53340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53340).length < 2 ^ (prefixWord ++ tailWord_53340).sum := by decide
  have hdescent : baseEnd_53340 < baseStart_53340 := by decide
  rcases family_descends (prefixWord ++ tailWord_53340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53346 : List Nat := [3, 3, 2, 2, 3, 1, 2, 1, 4]
def baseStart_53346 : Nat := 118140960795 + 53346 * 2 ^ 59
def prefixEnd_53346 : Nat := 4983230072969 + 3 ^ 40 * 53346 * 2
def baseEnd_53346 : Nat := 12174283997712674324299

theorem tailTrace_53346 : CollatzResearch.WordTrace tailWord_53346 prefixEnd_53346 12174283997712674324299 := by
  unfold tailWord_53346
  simp only [CollatzResearch.WordTrace]
  refine ⟨486422116186006904140973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1297125643162685077709261 486422116186006904140973)
  ·
    refine ⟨182408293569752589052865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 486422116186006904140973 182408293569752589052865)
    ·
      refine ⟨136806220177314441789649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182408293569752589052865 136806220177314441789649)
      ·
        refine ⟨102604665132985831342237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136806220177314441789649 102604665132985831342237)
        ·
          refine ⟨38476749424869686753339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102604665132985831342237 38476749424869686753339)
          ·
            refine ⟨57715124137304530130009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38476749424869686753339 57715124137304530130009)
            ·
              refine ⟨43286343102978397597507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57715124137304530130009 43286343102978397597507)
              ·
                refine ⟨64929514654467596396261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43286343102978397597507 64929514654467596396261)
                ·
                  refine ⟨12174283997712674324299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64929514654467596396261 12174283997712674324299)
                  ·
                    rfl

theorem cell21_53346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_53346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_53346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_53346 prefixEnd_53346 := by exact prefixLift 53346
  have htrace : WordTrace (prefixWord ++ tailWord_53346) baseStart_53346 baseEnd_53346 := by
    simpa [prefixWord, tailWord_53346, baseEnd_53346] using wordTrace_append hprefix tailTrace_53346
  have hstable : (prefixWord ++ tailWord_53346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53346).length < 2 ^ (prefixWord ++ tailWord_53346).sum := by decide
  have hdescent : baseEnd_53346 < baseStart_53346 := by decide
  rcases family_descends (prefixWord ++ tailWord_53346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53402 : List Nat := [3, 1, 1, 5, 2, 2, 1, 6]
def baseStart_53402 : Nat := 118140960795 + 53402 * 2 ^ 59
def prefixEnd_53402 : Nat := 4983230072969 + 3 ^ 40 * 53402 * 2
def baseEnd_53402 : Nat := 4062354653556340463617

theorem tailTrace_53402 : CollatzResearch.WordTrace tailWord_53402 prefixEnd_53402 4062354653556340463617 := by
  unfold tailWord_53402
  simp only [CollatzResearch.WordTrace]
  refine ⟨486932738135287295150615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1298487301694099453734973 486932738135287295150615)
  ·
    refine ⟨730399107202930942725923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 486932738135287295150615 730399107202930942725923)
    ·
      refine ⟨1095598660804396414088885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 730399107202930942725923 1095598660804396414088885)
      ·
        refine ⟨102712374450412163820833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1095598660804396414088885 102712374450412163820833)
        ·
          refine ⟨77034280837809122865625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102712374450412163820833 77034280837809122865625)
          ·
            refine ⟨57775710628356842149219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77034280837809122865625 57775710628356842149219)
            ·
              refine ⟨86663565942535263223829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57775710628356842149219 86663565942535263223829)
              ·
                refine ⟨4062354653556340463617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86663565942535263223829 4062354653556340463617)
                ·
                  rfl

theorem cell21_53402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 6].length) (baseStart_53402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_53402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_53402 prefixEnd_53402 := by exact prefixLift 53402
  have htrace : WordTrace (prefixWord ++ tailWord_53402) baseStart_53402 baseEnd_53402 := by
    simpa [prefixWord, tailWord_53402, baseEnd_53402] using wordTrace_append hprefix tailTrace_53402
  have hstable : (prefixWord ++ tailWord_53402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53402).length < 2 ^ (prefixWord ++ tailWord_53402).sum := by decide
  have hdescent : baseEnd_53402 < baseStart_53402 := by decide
  rcases family_descends (prefixWord ++ tailWord_53402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53489 : List Nat := [1, 2, 2, 2, 2, 1, 3, 2, 6]
def baseStart_53489 : Nat := 118140960795 + 53489 * 2 ^ 59
def prefixEnd_53489 : Nat := 4983230072969 + 3 ^ 40 * 53489 * 2
def baseEnd_53489 : Nat := 12206918545976203440673

theorem tailTrace_53489 : CollatzResearch.WordTrace tailWord_53489 prefixEnd_53489 12206918545976203440673 := by
  unfold tailWord_53489
  simp only [CollatzResearch.WordTrace]
  refine ⟨1950904103225963039019521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1300602735483975359346347 1950904103225963039019521)
  ·
    refine ⟨1463178077419472279264641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1950904103225963039019521 1463178077419472279264641)
    ·
      refine ⟨1097383558064604209448481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1463178077419472279264641 1097383558064604209448481)
      ·
        refine ⟨823037668548453157086361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1097383558064604209448481 823037668548453157086361)
        ·
          refine ⟨617278251411339867814771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 823037668548453157086361 617278251411339867814771)
          ·
            refine ⟨925917377117009801722157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617278251411339867814771 925917377117009801722157)
            ·
              refine ⟨347219016418878675645809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 925917377117009801722157 347219016418878675645809)
              ·
                refine ⟨260414262314159006734357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347219016418878675645809 260414262314159006734357)
                ·
                  refine ⟨12206918545976203440673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 260414262314159006734357 12206918545976203440673)
                  ·
                    rfl

theorem cell21_53489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 6].length) (baseStart_53489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_53489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_53489 prefixEnd_53489 := by exact prefixLift 53489
  have htrace : WordTrace (prefixWord ++ tailWord_53489) baseStart_53489 baseEnd_53489 := by
    simpa [prefixWord, tailWord_53489, baseEnd_53489] using wordTrace_append hprefix tailTrace_53489
  have hstable : (prefixWord ++ tailWord_53489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53489).length < 2 ^ (prefixWord ++ tailWord_53489).sum := by decide
  have hdescent : baseEnd_53489 < baseStart_53489 := by decide
  rcases family_descends (prefixWord ++ tailWord_53489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53579 : List Nat := [1, 1, 1, 1, 3, 1, 1, 12]
def baseStart_53579 : Nat := 118140960795 + 53579 * 2 ^ 59
def prefixEnd_53579 : Nat := 4983230072969 + 3 ^ 40 * 53579 * 2
def baseEnd_53579 : Nat := 4075819257385348980163

theorem tailTrace_53579 : CollatzResearch.WordTrace tailWord_53579 prefixEnd_53579 4075819257385348980163 := by
  unfold tailWord_53579
  simp only [CollatzResearch.WordTrace]
  refine ⟨1954186672899908409795791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1302791115266605606530527 1954186672899908409795791)
  ·
    refine ⟨2931280009349862614693687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1954186672899908409795791 2931280009349862614693687)
    ·
      refine ⟨4396920014024793922040531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2931280009349862614693687 4396920014024793922040531)
      ·
        refine ⟨6595380021037190883060797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4396920014024793922040531 6595380021037190883060797)
        ·
          refine ⟨2473267507888946581147799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6595380021037190883060797 2473267507888946581147799)
          ·
            refine ⟨3709901261833419871721699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2473267507888946581147799 3709901261833419871721699)
            ·
              refine ⟨5564851892750129807582549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3709901261833419871721699 5564851892750129807582549)
              ·
                refine ⟨4075819257385348980163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 5564851892750129807582549 4075819257385348980163)
                ·
                  rfl

theorem cell21_53579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 12].length) (baseStart_53579 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_53579 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_53579 prefixEnd_53579 := by exact prefixLift 53579
  have htrace : WordTrace (prefixWord ++ tailWord_53579) baseStart_53579 baseEnd_53579 := by
    simpa [prefixWord, tailWord_53579, baseEnd_53579] using wordTrace_append hprefix tailTrace_53579
  have hstable : (prefixWord ++ tailWord_53579).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53579).length < 2 ^ (prefixWord ++ tailWord_53579).sum := by decide
  have hdescent : baseEnd_53579 < baseStart_53579 := by decide
  rcases family_descends (prefixWord ++ tailWord_53579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53627 : List Nat := [1, 1, 1, 1, 1, 8, 2, 1, 5]
def baseStart_53627 : Nat := 118140960795 + 53627 * 2 ^ 59
def prefixEnd_53627 : Nat := 4983230072969 + 3 ^ 40 * 53627 * 2
def baseEnd_53627 : Nat := 12238412026118630140391

theorem tailTrace_53627 : CollatzResearch.WordTrace tailWord_53627 prefixEnd_53627 12238412026118630140391 := by
  unfold tailWord_53627
  simp only [CollatzResearch.WordTrace]
  refine ⟨1955937376726012607543135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1303958251150675071695423 1955937376726012607543135)
  ·
    refine ⟨2933906065089018911314703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1955937376726012607543135 2933906065089018911314703)
    ·
      refine ⟨4400859097633528366972055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2933906065089018911314703 4400859097633528366972055)
      ·
        refine ⟨6601288646450292550458083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4400859097633528366972055 6601288646450292550458083)
        ·
          refine ⟨9901932969675438825687125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6601288646450292550458083 9901932969675438825687125)
          ·
            refine ⟨116038276988384048738521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 9901932969675438825687125 116038276988384048738521)
            ·
              refine ⟨87028707741288036553891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116038276988384048738521 87028707741288036553891)
              ·
                refine ⟨130543061611932054830837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87028707741288036553891 130543061611932054830837)
                ·
                  refine ⟨12238412026118630140391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130543061611932054830837 12238412026118630140391)
                  ·
                    rfl

theorem cell21_53627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 5].length) (baseStart_53627 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_53627 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_53627 prefixEnd_53627 := by exact prefixLift 53627
  have htrace : WordTrace (prefixWord ++ tailWord_53627) baseStart_53627 baseEnd_53627 := by
    simpa [prefixWord, tailWord_53627, baseEnd_53627] using wordTrace_append hprefix tailTrace_53627
  have hstable : (prefixWord ++ tailWord_53627).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53627).length < 2 ^ (prefixWord ++ tailWord_53627).sum := by decide
  have hdescent : baseEnd_53627 < baseStart_53627 := by decide
  rcases family_descends (prefixWord ++ tailWord_53627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53692 : List Nat := [2, 2, 2, 4, 1, 3, 2, 1, 4]
def baseStart_53692 : Nat := 118140960795 + 53692 * 2 ^ 59
def prefixEnd_53692 : Nat := 4983230072969 + 3 ^ 40 * 53692 * 2
def baseEnd_53692 : Nat := 12253245911692961556925

theorem tailTrace_53692 : CollatzResearch.WordTrace tailWord_53692 prefixEnd_53692 12253245911692961556925 := by
  unfold tailWord_53692
  simp only [CollatzResearch.WordTrace]
  refine ⟨979154060745264354329665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1305538747660352472439553 979154060745264354329665)
  ·
    refine ⟨734365545558948265747249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 979154060745264354329665 734365545558948265747249)
    ·
      refine ⟨550774159169211199310437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 734365545558948265747249 550774159169211199310437)
      ·
        refine ⟨103270154844227099870707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 550774159169211199310437 103270154844227099870707)
        ·
          refine ⟨154905232266340649806061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103270154844227099870707 154905232266340649806061)
          ·
            refine ⟨58089462099877743677273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154905232266340649806061 58089462099877743677273)
            ·
              refine ⟨43567096574908307757955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58089462099877743677273 43567096574908307757955)
              ·
                refine ⟨65350644862362461636933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43567096574908307757955 65350644862362461636933)
                ·
                  refine ⟨12253245911692961556925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65350644862362461636933 12253245911692961556925)
                  ·
                    rfl

theorem cell21_53692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_53692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_53692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_53692 prefixEnd_53692 := by exact prefixLift 53692
  have htrace : WordTrace (prefixWord ++ tailWord_53692) baseStart_53692 baseEnd_53692 := by
    simpa [prefixWord, tailWord_53692, baseEnd_53692] using wordTrace_append hprefix tailTrace_53692
  have hstable : (prefixWord ++ tailWord_53692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53692).length < 2 ^ (prefixWord ++ tailWord_53692).sum := by decide
  have hdescent : baseEnd_53692 < baseStart_53692 := by decide
  rcases family_descends (prefixWord ++ tailWord_53692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53731 : List Nat := [1, 1, 1, 6, 12]
def baseStart_53731 : Nat := 118140960795 + 53731 * 2 ^ 59
def prefixEnd_53731 : Nat := 4983230072969 + 3 ^ 40 * 53731 * 2
def baseEnd_53731 : Nat := 151384521518982227245

theorem tailTrace_53731 : CollatzResearch.WordTrace tailWord_53731 prefixEnd_53731 151384521518982227245 := by
  unfold tailWord_53731
  simp only [CollatzResearch.WordTrace]
  refine ⟨1959730568349238369329047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1306487045566158912886031 1959730568349238369329047)
  ·
    refine ⟨2939595852523857553993571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1959730568349238369329047 2939595852523857553993571)
    ·
      refine ⟨4409393778785786330990357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2939595852523857553993571 4409393778785786330990357)
      ·
        refine ⟨206690333380583734265173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4409393778785786330990357 206690333380583734265173)
        ·
          refine ⟨151384521518982227245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 206690333380583734265173 151384521518982227245)
          ·
            rfl

theorem cell21_53731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 12].length) (baseStart_53731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_53731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_53731 prefixEnd_53731 := by exact prefixLift 53731
  have htrace : WordTrace (prefixWord ++ tailWord_53731) baseStart_53731 baseEnd_53731 := by
    simpa [prefixWord, tailWord_53731, baseEnd_53731] using wordTrace_append hprefix tailTrace_53731
  have hstable : (prefixWord ++ tailWord_53731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53731).length < 2 ^ (prefixWord ++ tailWord_53731).sum := by decide
  have hdescent : baseEnd_53731 < baseStart_53731 := by decide
  rcases family_descends (prefixWord ++ tailWord_53731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53793 : List Nat := [1, 2, 3, 2, 2, 1, 3, 1, 6]
def baseStart_53793 : Nat := 118140960795 + 53793 * 2 ^ 59
def prefixEnd_53793 : Nat := 4983230072969 + 3 ^ 40 * 53793 * 2
def baseEnd_53793 : Nat := 12276295487739230373385

theorem tailTrace_53793 : CollatzResearch.WordTrace tailWord_53793 prefixEnd_53793 12276295487739230373385 := by
  unfold tailWord_53793
  simp only [CollatzResearch.WordTrace]
  refine ⟨1961991894124622958086033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1307994596083081972057355 1961991894124622958086033)
  ·
    refine ⟨1471493920593467218564525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1961991894124622958086033 1471493920593467218564525)
    ·
      refine ⟨551810220222550206961697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1471493920593467218564525 551810220222550206961697)
      ·
        refine ⟨413857665166912655221273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 551810220222550206961697 413857665166912655221273)
        ·
          refine ⟨310393248875184491415955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413857665166912655221273 310393248875184491415955)
          ·
            refine ⟨465589873312776737123933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310393248875184491415955 465589873312776737123933)
            ·
              refine ⟨174596202492291276421475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 465589873312776737123933 174596202492291276421475)
              ·
                refine ⟨261894303738436914632213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174596202492291276421475 261894303738436914632213)
                ·
                  refine ⟨12276295487739230373385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 261894303738436914632213 12276295487739230373385)
                  ·
                    rfl

theorem cell21_53793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 6].length) (baseStart_53793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_53793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_53793 prefixEnd_53793 := by exact prefixLift 53793
  have htrace : WordTrace (prefixWord ++ tailWord_53793) baseStart_53793 baseEnd_53793 := by
    simpa [prefixWord, tailWord_53793, baseEnd_53793] using wordTrace_append hprefix tailTrace_53793
  have hstable : (prefixWord ++ tailWord_53793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53793).length < 2 ^ (prefixWord ++ tailWord_53793).sum := by decide
  have hdescent : baseEnd_53793 < baseStart_53793 := by decide
  rcases family_descends (prefixWord ++ tailWord_53793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53824 : List Nat := [2, 1, 1, 2, 2, 2, 6, 5]
def baseStart_53824 : Nat := 118140960795 + 53824 * 2 ^ 59
def prefixEnd_53824 : Nat := 4983230072969 + 3 ^ 40 * 53824 * 2
def baseEnd_53824 : Nat := 4094456703363355118885

theorem tailTrace_53824 : CollatzResearch.WordTrace tailWord_53824 prefixEnd_53824 4094456703363355118885 := by
  unfold tailWord_53824
  simp only [CollatzResearch.WordTrace]
  refine ⟨981561278506157626232263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1308748371341543501643017 981561278506157626232263)
  ·
    refine ⟨1472341917759236439348395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 981561278506157626232263 1472341917759236439348395)
    ·
      refine ⟨2208512876638854659022593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1472341917759236439348395 2208512876638854659022593)
      ·
        refine ⟨1656384657479140994266945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2208512876638854659022593 1656384657479140994266945)
        ·
          refine ⟨1242288493109355745700209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1656384657479140994266945 1242288493109355745700209)
          ·
            refine ⟨931716369832016809275157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1242288493109355745700209 931716369832016809275157)
            ·
              refine ⟨43674204835875787934773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 931716369832016809275157 43674204835875787934773)
              ·
                refine ⟨4094456703363355118885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43674204835875787934773 4094456703363355118885)
                ·
                  rfl

theorem cell21_53824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 5].length) (baseStart_53824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_53824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_53824 prefixEnd_53824 := by exact prefixLift 53824
  have htrace : WordTrace (prefixWord ++ tailWord_53824) baseStart_53824 baseEnd_53824 := by
    simpa [prefixWord, tailWord_53824, baseEnd_53824] using wordTrace_append hprefix tailTrace_53824
  have hstable : (prefixWord ++ tailWord_53824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53824).length < 2 ^ (prefixWord ++ tailWord_53824).sum := by decide
  have hdescent : baseEnd_53824 < baseStart_53824 := by decide
  rcases family_descends (prefixWord ++ tailWord_53824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53830 : List Nat := [6, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_53830 : Nat := 118140960795 + 53830 * 2 ^ 59
def prefixEnd_53830 : Nat := 4983230072969 + 3 ^ 40 * 53830 * 2
def baseEnd_53830 : Nat := 12284739391835388256643

theorem tailTrace_53830 : CollatzResearch.WordTrace tailWord_53830 prefixEnd_53830 12284739391835388256643 := by
  unfold tailWord_53830
  simp only [CollatzResearch.WordTrace]
  refine ⟨61354418593455571161967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1308894263327052184788629 61354418593455571161967)
  ·
    refine ⟨92031627890183356742951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61354418593455571161967 92031627890183356742951)
    ·
      refine ⟨138047441835275035114427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92031627890183356742951 138047441835275035114427)
      ·
        refine ⟨207071162752912552671641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138047441835275035114427 207071162752912552671641)
        ·
          refine ⟨155303372064684414503731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207071162752912552671641 155303372064684414503731)
          ·
            refine ⟨232955058097026621755597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155303372064684414503731 232955058097026621755597)
            ·
              refine ⟨87358146786384983158349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232955058097026621755597 87358146786384983158349)
              ·
                refine ⟨32759305044894368684381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87358146786384983158349 32759305044894368684381)
                ·
                  refine ⟨12284739391835388256643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32759305044894368684381 12284739391835388256643)
                  ·
                    rfl

theorem cell21_53830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_53830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_53830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_53830 prefixEnd_53830 := by exact prefixLift 53830
  have htrace : WordTrace (prefixWord ++ tailWord_53830) baseStart_53830 baseEnd_53830 := by
    simpa [prefixWord, tailWord_53830, baseEnd_53830] using wordTrace_append hprefix tailTrace_53830
  have hstable : (prefixWord ++ tailWord_53830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53830).length < 2 ^ (prefixWord ++ tailWord_53830).sum := by decide
  have hdescent : baseEnd_53830 < baseStart_53830 := by decide
  rcases family_descends (prefixWord ++ tailWord_53830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53838 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 7]
def baseStart_53838 : Nat := 118140960795 + 53838 * 2 ^ 59
def prefixEnd_53838 : Nat := 4983230072969 + 3 ^ 40 * 53838 * 2
def baseEnd_53838 : Nat := 12286565100829152123293

theorem tailTrace_53838 : CollatzResearch.WordTrace tailWord_53838 prefixEnd_53838 12286565100829152123293 := by
  unfold tailWord_53838
  simp only [CollatzResearch.WordTrace]
  refine ⟨245454147370199455434271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1309088785974397095649445 245454147370199455434271)
  ·
    refine ⟨368181221055299183151407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245454147370199455434271 368181221055299183151407)
    ·
      refine ⟨552271831582948774727111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368181221055299183151407 552271831582948774727111)
      ·
        refine ⟨828407747374423162090667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552271831582948774727111 828407747374423162090667)
        ·
          refine ⟨1242611621061634743136001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 828407747374423162090667 1242611621061634743136001)
          ·
            refine ⟨931958715796226057352001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1242611621061634743136001 931958715796226057352001)
            ·
              refine ⟨698969036847169543014001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 931958715796226057352001 698969036847169543014001)
              ·
                refine ⟨524226777635377157260501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 698969036847169543014001 524226777635377157260501)
                ·
                  refine ⟨12286565100829152123293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 524226777635377157260501 12286565100829152123293)
                  ·
                    rfl

theorem cell21_53838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_53838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_53838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_53838 prefixEnd_53838 := by exact prefixLift 53838
  have htrace : WordTrace (prefixWord ++ tailWord_53838) baseStart_53838 baseEnd_53838 := by
    simpa [prefixWord, tailWord_53838, baseEnd_53838] using wordTrace_append hprefix tailTrace_53838
  have hstable : (prefixWord ++ tailWord_53838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53838).length < 2 ^ (prefixWord ++ tailWord_53838).sum := by decide
  have hdescent : baseEnd_53838 < baseStart_53838 := by decide
  rcases family_descends (prefixWord ++ tailWord_53838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53855 : List Nat := [1, 1, 2, 3, 1, 1, 1, 8, 3]
def baseStart_53855 : Nat := 118140960795 + 53855 * 2 ^ 59
def prefixEnd_53855 : Nat := 4983230072969 + 3 ^ 40 * 53855 * 2
def baseEnd_53855 : Nat := 12290444732440900339925

theorem tailTrace_53855 : CollatzResearch.WordTrace tailWord_53855 prefixEnd_53855 12290444732440900339925 := by
  unfold tailWord_53855
  simp only [CollatzResearch.WordTrace]
  refine ⟨1964253219900007546843019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1309502146600005031228679 1964253219900007546843019)
  ·
    refine ⟨2946379829850011320264529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1964253219900007546843019 2946379829850011320264529)
    ·
      refine ⟨2209784872387508490198397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2946379829850011320264529 2209784872387508490198397)
      ·
        refine ⟨828669327145315683824399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2209784872387508490198397 828669327145315683824399)
        ·
          refine ⟨1243003990717973525736599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 828669327145315683824399 1243003990717973525736599)
          ·
            refine ⟨1864505986076960288604899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243003990717973525736599 1864505986076960288604899)
            ·
              refine ⟨2796758979115440432907349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1864505986076960288604899 2796758979115440432907349)
              ·
                refine ⟨32774519286509067573133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2796758979115440432907349 32774519286509067573133)
                ·
                  refine ⟨12290444732440900339925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32774519286509067573133 12290444732440900339925)
                  ·
                    rfl

theorem cell21_53855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8, 3].length) (baseStart_53855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_53855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_53855 prefixEnd_53855 := by exact prefixLift 53855
  have htrace : WordTrace (prefixWord ++ tailWord_53855) baseStart_53855 baseEnd_53855 := by
    simpa [prefixWord, tailWord_53855, baseEnd_53855] using wordTrace_append hprefix tailTrace_53855
  have hstable : (prefixWord ++ tailWord_53855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53855).length < 2 ^ (prefixWord ++ tailWord_53855).sum := by decide
  have hdescent : baseEnd_53855 < baseStart_53855 := by decide
  rcases family_descends (prefixWord ++ tailWord_53855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53858 : List Nat := [3, 3, 2, 3, 1, 1, 2, 6]
def baseStart_53858 : Nat := 118140960795 + 53858 * 2 ^ 59
def prefixEnd_53858 : Nat := 4983230072969 + 3 ^ 40 * 53858 * 2
def baseEnd_53858 : Nat := 4097043124437853929973

theorem tailTrace_53858 : CollatzResearch.WordTrace tailWord_53858 prefixEnd_53858 4097043124437853929973 := by
  unfold tailWord_53858
  simp only [CollatzResearch.WordTrace]
  refine ⟨491090659722284764800557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1309575092592759372801485 491090659722284764800557)
  ·
    refine ⟨184158997395856786800209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 491090659722284764800557 184158997395856786800209)
    ·
      refine ⟨138119248046892590100157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184158997395856786800209 138119248046892590100157)
      ·
        refine ⟨51794718017584721287559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138119248046892590100157 51794718017584721287559)
        ·
          refine ⟨77692077026377081931339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51794718017584721287559 77692077026377081931339)
          ·
            refine ⟨116538115539565622897009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77692077026377081931339 116538115539565622897009)
            ·
              refine ⟨87403586654674217172757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116538115539565622897009 87403586654674217172757)
              ·
                refine ⟨4097043124437853929973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87403586654674217172757 4097043124437853929973)
                ·
                  rfl

theorem cell21_53858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 6].length) (baseStart_53858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_53858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_53858 prefixEnd_53858 := by exact prefixLift 53858
  have htrace : WordTrace (prefixWord ++ tailWord_53858) baseStart_53858 baseEnd_53858 := by
    simpa [prefixWord, tailWord_53858, baseEnd_53858] using wordTrace_append hprefix tailTrace_53858
  have hstable : (prefixWord ++ tailWord_53858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53858).length < 2 ^ (prefixWord ++ tailWord_53858).sum := by decide
  have hdescent : baseEnd_53858 < baseStart_53858 := by decide
  rcases family_descends (prefixWord ++ tailWord_53858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53906 : List Nat := [3, 2, 3, 1, 2, 3, 2, 2, 3]
def baseStart_53906 : Nat := 118140960795 + 53906 * 2 ^ 59
def prefixEnd_53906 : Nat := 4983230072969 + 3 ^ 40 * 53906 * 2
def baseEnd_53906 : Nat := 12302083627276144989821

theorem tailTrace_53906 : CollatzResearch.WordTrace tailWord_53906 prefixEnd_53906 12302083627276144989821 := by
  unfold tailWord_53906
  simp only [CollatzResearch.WordTrace]
  refine ⟨491528335678810814237393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1310742228476828837966381 491528335678810814237393)
  ·
    refine ⟨368646251759108110678045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 491528335678810814237393 368646251759108110678045)
    ·
      refine ⟨138242344409665541504267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368646251759108110678045 138242344409665541504267)
      ·
        refine ⟨207363516614498312256401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138242344409665541504267 207363516614498312256401)
        ·
          refine ⟨155522637460873734192301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207363516614498312256401 155522637460873734192301)
          ·
            refine ⟨58320989047827650322113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155522637460873734192301 58320989047827650322113)
            ·
              refine ⟨43740741785870737741585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58320989047827650322113 43740741785870737741585)
              ·
                refine ⟨32805556339403053306189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43740741785870737741585 32805556339403053306189)
                ·
                  refine ⟨12302083627276144989821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32805556339403053306189 12302083627276144989821)
                  ·
                    rfl

theorem cell21_53906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_53906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_53906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_53906 prefixEnd_53906 := by exact prefixLift 53906
  have htrace : WordTrace (prefixWord ++ tailWord_53906) baseStart_53906 baseEnd_53906 := by
    simpa [prefixWord, tailWord_53906, baseEnd_53906] using wordTrace_append hprefix tailTrace_53906
  have hstable : (prefixWord ++ tailWord_53906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53906).length < 2 ^ (prefixWord ++ tailWord_53906).sum := by decide
  have hdescent : baseEnd_53906 < baseStart_53906 := by decide
  rcases family_descends (prefixWord ++ tailWord_53906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53934 : List Nat := [4, 1, 4, 1, 1, 2, 3, 5]
def baseStart_53934 : Nat := 118140960795 + 53934 * 2 ^ 59
def prefixEnd_53934 : Nat := 4983230072969 + 3 ^ 40 * 53934 * 2
def baseEnd_53934 : Nat := 4102824536251439507699

theorem tailTrace_53934 : CollatzResearch.WordTrace tailWord_53934 prefixEnd_53934 4102824536251439507699 := by
  unfold tailWord_53934
  simp only [CollatzResearch.WordTrace]
  refine ⟨245891823326725504871107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1311423057742536025979237 245891823326725504871107)
  ·
    refine ⟨368837734990088257306661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245891823326725504871107 368837734990088257306661)
    ·
      refine ⟨69157075310641548244999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 368837734990088257306661 69157075310641548244999)
      ·
        refine ⟨103735612965962322367499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69157075310641548244999 103735612965962322367499)
        ·
          refine ⟨155603419448943483551249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103735612965962322367499 155603419448943483551249)
          ·
            refine ⟨116702564586707612663437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155603419448943483551249 116702564586707612663437)
            ·
              refine ⟨43763461720015354748789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116702564586707612663437 43763461720015354748789)
              ·
                refine ⟨4102824536251439507699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43763461720015354748789 4102824536251439507699)
                ·
                  rfl

theorem cell21_53934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_53934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_53934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_53934 prefixEnd_53934 := by exact prefixLift 53934
  have htrace : WordTrace (prefixWord ++ tailWord_53934) baseStart_53934 baseEnd_53934 := by
    simpa [prefixWord, tailWord_53934, baseEnd_53934] using wordTrace_append hprefix tailTrace_53934
  have hstable : (prefixWord ++ tailWord_53934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53934).length < 2 ^ (prefixWord ++ tailWord_53934).sum := by decide
  have hdescent : baseEnd_53934 < baseStart_53934 := by decide
  rcases family_descends (prefixWord ++ tailWord_53934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53948 : List Nat := [2, 2, 2, 3, 1, 1, 4, 3, 3]
def baseStart_53948 : Nat := 118140960795 + 53948 * 2 ^ 59
def prefixEnd_53948 : Nat := 4983230072969 + 3 ^ 40 * 53948 * 2
def baseEnd_53948 : Nat := 12311668599493405289735

theorem tailTrace_53948 : CollatzResearch.WordTrace tailWord_53948 prefixEnd_53948 12311668599493405289735 := by
  unfold tailWord_53948
  simp only [CollatzResearch.WordTrace]
  refine ⟨983822604281542214989249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1311763472375389619985665 983822604281542214989249)
  ·
    refine ⟨737866953211156661241937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 983822604281542214989249 737866953211156661241937)
    ·
      refine ⟨553400214908367495931453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 737866953211156661241937 553400214908367495931453)
      ·
        refine ⟨207525080590637810974295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 553400214908367495931453 207525080590637810974295)
        ·
          refine ⟨311287620885956716461443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207525080590637810974295 311287620885956716461443)
          ·
            refine ⟨466931431328935074692165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311287620885956716461443 466931431328935074692165)
            ·
              refine ⟨87549643374175326504781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 466931431328935074692165 87549643374175326504781)
              ·
                refine ⟨32831116265315747439293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87549643374175326504781 32831116265315747439293)
                ·
                  refine ⟨12311668599493405289735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32831116265315747439293 12311668599493405289735)
                  ·
                    rfl

theorem cell21_53948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3, 3].length) (baseStart_53948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_53948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_53948 prefixEnd_53948 := by exact prefixLift 53948
  have htrace : WordTrace (prefixWord ++ tailWord_53948) baseStart_53948 baseEnd_53948 := by
    simpa [prefixWord, tailWord_53948, baseEnd_53948] using wordTrace_append hprefix tailTrace_53948
  have hstable : (prefixWord ++ tailWord_53948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53948).length < 2 ^ (prefixWord ++ tailWord_53948).sum := by decide
  have hdescent : baseEnd_53948 < baseStart_53948 := by decide
  rcases family_descends (prefixWord ++ tailWord_53948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53962 : List Nat := [3, 1, 2, 1, 4, 1, 3, 2, 4]
def baseStart_53962 : Nat := 118140960795 + 53962 * 2 ^ 59
def prefixEnd_53962 : Nat := 4983230072969 + 3 ^ 40 * 53962 * 2
def baseEnd_53962 : Nat := 12314863590232492056373

theorem tailTrace_53962 : CollatzResearch.WordTrace tailWord_53962 prefixEnd_53962 12314863590232492056373 := by
  unfold tailWord_53962
  simp only [CollatzResearch.WordTrace]
  refine ⟨492038957628091205247035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1312103887008243213992093 492038957628091205247035)
  ·
    refine ⟨738058436442136807870553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 492038957628091205247035 738058436442136807870553)
    ·
      refine ⟨553543827331602605902915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 738058436442136807870553 553543827331602605902915)
      ·
        refine ⟨830315740997403908854373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553543827331602605902915 830315740997403908854373)
        ·
          refine ⟨155684201437013232910195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 830315740997403908854373 155684201437013232910195)
          ·
            refine ⟨233526302155519849365293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155684201437013232910195 233526302155519849365293)
            ·
              refine ⟨87572363308319943511985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233526302155519849365293 87572363308319943511985)
              ·
                refine ⟨65679272481239957633989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87572363308319943511985 65679272481239957633989)
                ·
                  refine ⟨12314863590232492056373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65679272481239957633989 12314863590232492056373)
                  ·
                    rfl

theorem cell21_53962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_53962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_53962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_53962 prefixEnd_53962 := by exact prefixLift 53962
  have htrace : WordTrace (prefixWord ++ tailWord_53962) baseStart_53962 baseEnd_53962 := by
    simpa [prefixWord, tailWord_53962, baseEnd_53962] using wordTrace_append hprefix tailTrace_53962
  have hstable : (prefixWord ++ tailWord_53962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53962).length < 2 ^ (prefixWord ++ tailWord_53962).sum := by decide
  have hdescent : baseEnd_53962 < baseStart_53962 := by decide
  rcases family_descends (prefixWord ++ tailWord_53962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53965 : List Nat := [1, 6, 2, 1, 2, 1, 2, 1, 5]
def baseStart_53965 : Nat := 118140960795 + 53965 * 2 ^ 59
def prefixEnd_53965 : Nat := 4983230072969 + 3 ^ 40 * 53965 * 2
def baseEnd_53965 : Nat := 12315548231105153506367

theorem tailTrace_53965 : CollatzResearch.WordTrace tailWord_53965 prefixEnd_53965 12315548231105153506367 := by
  unfold tailWord_53965
  simp only [CollatzResearch.WordTrace]
  refine ⟨1968265249501496333347349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1312176833000997555564899 1968265249501496333347349)
  ·
    refine ⟨92262433570382640625657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1968265249501496333347349 92262433570382640625657)
    ·
      refine ⟨69196825177786980469243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92262433570382640625657 69196825177786980469243)
      ·
        refine ⟨103795237766680470703865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69196825177786980469243 103795237766680470703865)
        ·
          refine ⟨77846428325010353027899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103795237766680470703865 77846428325010353027899)
          ·
            refine ⟨116769642487515529541849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77846428325010353027899 116769642487515529541849)
            ·
              refine ⟨87577231865636647156387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116769642487515529541849 87577231865636647156387)
              ·
                refine ⟨131365847798454970734581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87577231865636647156387 131365847798454970734581)
                ·
                  refine ⟨12315548231105153506367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 131365847798454970734581 12315548231105153506367)
                  ·
                    rfl

theorem cell21_53965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_53965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_53965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_53965 prefixEnd_53965 := by exact prefixLift 53965
  have htrace : WordTrace (prefixWord ++ tailWord_53965) baseStart_53965 baseEnd_53965 := by
    simpa [prefixWord, tailWord_53965, baseEnd_53965] using wordTrace_append hprefix tailTrace_53965
  have hstable : (prefixWord ++ tailWord_53965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53965).length < 2 ^ (prefixWord ++ tailWord_53965).sum := by decide
  have hdescent : baseEnd_53965 < baseStart_53965 := by decide
  rcases family_descends (prefixWord ++ tailWord_53965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54035 : List Nat := [1, 1, 1, 2, 1, 3, 6, 6]
def baseStart_54035 : Nat := 118140960795 + 54035 * 2 ^ 59
def prefixEnd_54035 : Nat := 4983230072969 + 3 ^ 40 * 54035 * 2
def baseEnd_54035 : Nat := 4110507728266862446519

theorem tailTrace_54035 : CollatzResearch.WordTrace tailWord_54035 prefixEnd_54035 4110507728266862446519 := by
  unfold tailWord_54035
  simp only [CollatzResearch.WordTrace]
  refine ⟨1970818359247898288395559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1313878906165265525597039 1970818359247898288395559)
  ·
    refine ⟨2956227538871847432593339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1970818359247898288395559 2956227538871847432593339)
    ·
      refine ⟨4434341308307771148890009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2956227538871847432593339 4434341308307771148890009)
      ·
        refine ⟨3325755981230828361667507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4434341308307771148890009 3325755981230828361667507)
        ·
          refine ⟨4988633971846242542501261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3325755981230828361667507 4988633971846242542501261)
          ·
            refine ⟨1870737739442340953437973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4988633971846242542501261 1870737739442340953437973)
            ·
              refine ⟨87690831536359732192405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1870737739442340953437973 87690831536359732192405)
              ·
                refine ⟨4110507728266862446519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87690831536359732192405 4110507728266862446519)
                ·
                  rfl

theorem cell21_54035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 6].length) (baseStart_54035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_54035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_54035 prefixEnd_54035 := by exact prefixLift 54035
  have htrace : WordTrace (prefixWord ++ tailWord_54035) baseStart_54035 baseEnd_54035 := by
    simpa [prefixWord, tailWord_54035, baseEnd_54035] using wordTrace_append hprefix tailTrace_54035
  have hstable : (prefixWord ++ tailWord_54035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54035).length < 2 ^ (prefixWord ++ tailWord_54035).sum := by decide
  have hdescent : baseEnd_54035 < baseStart_54035 := by decide
  rcases family_descends (prefixWord ++ tailWord_54035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54080 : List Nat := [2, 1, 1, 2, 2, 1, 1, 5, 6]
def baseStart_54080 : Nat := 118140960795 + 54080 * 2 ^ 59
def prefixEnd_54080 : Nat := 4983230072969 + 3 ^ 40 * 54080 * 2
def baseEnd_54080 : Nat := 12341792797890509089465

theorem tailTrace_54080 : CollatzResearch.WordTrace tailWord_54080 prefixEnd_54080 12341792797890509089465 := by
  unfold tailWord_54080
  simp only [CollatzResearch.WordTrace]
  refine ⟨986229822042435486891847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1314973096056580649189129 986229822042435486891847)
  ·
    refine ⟨1479344733063653230337771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 986229822042435486891847 1479344733063653230337771)
    ·
      refine ⟨2219017099595479845506657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1479344733063653230337771 2219017099595479845506657)
      ·
        refine ⟨1664262824696609884129993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2219017099595479845506657 1664262824696609884129993)
        ·
          refine ⟨1248197118522457413097495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1664262824696609884129993 1248197118522457413097495)
          ·
            refine ⟨1872295677783686119646243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1248197118522457413097495 1872295677783686119646243)
            ·
              refine ⟨2808443516675529179469365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1872295677783686119646243 2808443516675529179469365)
              ·
                refine ⟨263291579688330860575253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2808443516675529179469365 263291579688330860575253)
                ·
                  refine ⟨12341792797890509089465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 263291579688330860575253 12341792797890509089465)
                  ·
                    rfl

theorem cell21_54080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_54080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_54080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_54080 prefixEnd_54080 := by exact prefixLift 54080
  have htrace : WordTrace (prefixWord ++ tailWord_54080) baseStart_54080 baseEnd_54080 := by
    simpa [prefixWord, tailWord_54080, baseEnd_54080] using wordTrace_append hprefix tailTrace_54080
  have hstable : (prefixWord ++ tailWord_54080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54080).length < 2 ^ (prefixWord ++ tailWord_54080).sum := by decide
  have hdescent : baseEnd_54080 < baseStart_54080 := by decide
  rcases family_descends (prefixWord ++ tailWord_54080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54083 : List Nat := [1, 1, 1, 3, 1, 4, 3, 4, 3]
def baseStart_54083 : Nat := 118140960795 + 54083 * 2 ^ 59
def prefixEnd_54083 : Nat := 4983230072969 + 3 ^ 40 * 54083 * 2
def baseEnd_54083 : Nat := 12342477438763170539459

theorem tailTrace_54083 : CollatzResearch.WordTrace tailWord_54083 prefixEnd_54083 12342477438763170539459 := by
  unfold tailWord_54083
  simp only [CollatzResearch.WordTrace]
  refine ⟨1972569063074002486142903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1315046042049334990761935 1972569063074002486142903)
  ·
    refine ⟨2958853594611003729214355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1972569063074002486142903 2958853594611003729214355)
    ·
      refine ⟨4438280391916505593821533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2958853594611003729214355 4438280391916505593821533)
      ·
        refine ⟨1664355146968689597683075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4438280391916505593821533 1664355146968689597683075)
        ·
          refine ⟨2496532720453034396524613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1664355146968689597683075 2496532720453034396524613)
          ·
            refine ⟨468099885084943949348365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2496532720453034396524613 468099885084943949348365)
            ·
              refine ⟨175537456906853981005637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 468099885084943949348365 175537456906853981005637)
              ·
                refine ⟨32913273170035121438557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175537456906853981005637 32913273170035121438557)
                ·
                  refine ⟨12342477438763170539459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32913273170035121438557 12342477438763170539459)
                  ·
                    rfl

theorem cell21_54083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4, 3].length) (baseStart_54083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_54083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_54083 prefixEnd_54083 := by exact prefixLift 54083
  have htrace : WordTrace (prefixWord ++ tailWord_54083) baseStart_54083 baseEnd_54083 := by
    simpa [prefixWord, tailWord_54083, baseEnd_54083] using wordTrace_append hprefix tailTrace_54083
  have hstable : (prefixWord ++ tailWord_54083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54083).length < 2 ^ (prefixWord ++ tailWord_54083).sum := by decide
  have hdescent : baseEnd_54083 < baseStart_54083 := by decide
  rcases family_descends (prefixWord ++ tailWord_54083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54162 : List Nat := [3, 2, 3, 2, 2, 2, 2, 5]
def baseStart_54162 : Nat := 118140960795 + 54162 * 2 ^ 59
def prefixEnd_54162 : Nat := 4983230072969 + 3 ^ 40 * 54162 * 2
def baseEnd_54162 : Nat := 4120168771692196240877

theorem tailTrace_54162 : CollatzResearch.WordTrace tailWord_54162 prefixEnd_54162 4120168771692196240877 := by
  unfold tailWord_54162
  simp only [CollatzResearch.WordTrace]
  refine ⟨493862607446949744567185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1316966953191865985512493 493862607446949744567185)
  ·
    refine ⟨370396955585212308425389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 493862607446949744567185 370396955585212308425389)
    ·
      refine ⟨138898858344454615659521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 370396955585212308425389 138898858344454615659521)
      ·
        refine ⟨104174143758340961744641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138898858344454615659521 104174143758340961744641)
        ·
          refine ⟨78130607818755721308481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104174143758340961744641 78130607818755721308481)
          ·
            refine ⟨58597955864066790981361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78130607818755721308481 58597955864066790981361)
            ·
              refine ⟨43948466898050093236021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58597955864066790981361 43948466898050093236021)
              ·
                refine ⟨4120168771692196240877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43948466898050093236021 4120168771692196240877)
                ·
                  rfl

theorem cell21_54162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 5].length) (baseStart_54162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_54162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_54162 prefixEnd_54162 := by exact prefixLift 54162
  have htrace : WordTrace (prefixWord ++ tailWord_54162) baseStart_54162 baseEnd_54162 := by
    simpa [prefixWord, tailWord_54162, baseEnd_54162] using wordTrace_append hprefix tailTrace_54162
  have hstable : (prefixWord ++ tailWord_54162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54162).length < 2 ^ (prefixWord ++ tailWord_54162).sum := by decide
  have hdescent : baseEnd_54162 < baseStart_54162 := by decide
  rcases family_descends (prefixWord ++ tailWord_54162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54193 : List Nat := [1, 2, 2, 4, 3, 1, 3, 2, 3]
def baseStart_54193 : Nat := 118140960795 + 54193 * 2 ^ 59
def prefixEnd_54193 : Nat := 4983230072969 + 3 ^ 40 * 54193 * 2
def baseEnd_54193 : Nat := 12367580937427423705901

theorem tailTrace_54193 : CollatzResearch.WordTrace tailWord_54193 prefixEnd_54193 12367580937427423705901 := by
  unfold tailWord_54193
  simp only [CollatzResearch.WordTrace]
  refine ⟨1976581092675491272647233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1317720728450327515098155 1976581092675491272647233)
  ·
    refine ⟨1482435819506618454485425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1976581092675491272647233 1482435819506618454485425)
    ·
      refine ⟨1111826864629963840864069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1482435819506618454485425 1111826864629963840864069)
      ·
        refine ⟨208467537118118220162013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1111826864629963840864069 208467537118118220162013)
        ·
          refine ⟨78175326419294332560755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208467537118118220162013 78175326419294332560755)
          ·
            refine ⟨117262989628941498841133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78175326419294332560755 117262989628941498841133)
            ·
              refine ⟨43973621110853062065425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117262989628941498841133 43973621110853062065425)
              ·
                refine ⟨32980215833139796549069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43973621110853062065425 32980215833139796549069)
                ·
                  refine ⟨12367580937427423705901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32980215833139796549069 12367580937427423705901)
                  ·
                    rfl

theorem cell21_54193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2, 3].length) (baseStart_54193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_54193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_54193 prefixEnd_54193 := by exact prefixLift 54193
  have htrace : WordTrace (prefixWord ++ tailWord_54193) baseStart_54193 baseEnd_54193 := by
    simpa [prefixWord, tailWord_54193, baseEnd_54193] using wordTrace_append hprefix tailTrace_54193
  have hstable : (prefixWord ++ tailWord_54193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54193).length < 2 ^ (prefixWord ++ tailWord_54193).sum := by decide
  have hdescent : baseEnd_54193 < baseStart_54193 := by decide
  rcases family_descends (prefixWord ++ tailWord_54193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54280 : List Nat := [2, 1, 3, 2, 1, 4, 3, 5]
def baseStart_54280 : Nat := 118140960795 + 54280 * 2 ^ 59
def prefixEnd_54280 : Nat := 4983230072969 + 3 ^ 40 * 54280 * 2
def baseEnd_54280 : Nat := 4129145174244868585241

theorem tailTrace_54280 : CollatzResearch.WordTrace tailWord_54280 prefixEnd_54280 4129145174244868585241 := by
  unfold tailWord_54280
  simp only [CollatzResearch.WordTrace]
  refine ⟨989877121680152565532147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1319836162240203420709529 989877121680152565532147)
  ·
    refine ⟨1484815682520228848298221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 989877121680152565532147 1484815682520228848298221)
    ·
      refine ⟨556805880945085818111833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1484815682520228848298221 556805880945085818111833)
      ·
        refine ⟨417604410708814363583875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 556805880945085818111833 417604410708814363583875)
        ·
          refine ⟨626406616063221545375813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417604410708814363583875 626406616063221545375813)
          ·
            refine ⟨117451240511854039757965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 626406616063221545375813 117451240511854039757965)
            ·
              refine ⟨44044215191945264909237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117451240511854039757965 44044215191945264909237)
              ·
                refine ⟨4129145174244868585241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44044215191945264909237 4129145174244868585241)
                ·
                  rfl

theorem cell21_54280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 5].length) (baseStart_54280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_54280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_54280 prefixEnd_54280 := by exact prefixLift 54280
  have htrace : WordTrace (prefixWord ++ tailWord_54280) baseStart_54280 baseEnd_54280 := by
    simpa [prefixWord, tailWord_54280, baseEnd_54280] using wordTrace_append hprefix tailTrace_54280
  have hstable : (prefixWord ++ tailWord_54280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54280).length < 2 ^ (prefixWord ++ tailWord_54280).sum := by decide
  have hdescent : baseEnd_54280 < baseStart_54280 := by decide
  rcases family_descends (prefixWord ++ tailWord_54280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54311 : List Nat := [1, 1, 7, 1, 1, 1, 1, 3, 5]
def baseStart_54311 : Nat := 118140960795 + 54311 * 2 ^ 59
def prefixEnd_54311 : Nat := 4983230072969 + 3 ^ 40 * 54311 * 2
def baseEnd_54311 : Nat := 12394510145085440738993

theorem tailTrace_54311 : CollatzResearch.WordTrace tailWord_54311 prefixEnd_54311 12394510145085440738993 := by
  unfold tailWord_54311
  simp only [CollatzResearch.WordTrace]
  refine ⟨1980884906247997425442787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1320589937498664950295191 1980884906247997425442787)
  ·
    refine ⟨2971327359371996138164181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1980884906247997425442787 2971327359371996138164181)
    ·
      refine ⟨69640484985281159488223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 2971327359371996138164181 69640484985281159488223)
      ·
        refine ⟨104460727477921739232335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69640484985281159488223 104460727477921739232335)
        ·
          refine ⟨156691091216882608848503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104460727477921739232335 156691091216882608848503)
          ·
            refine ⟨235036636825323913272755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156691091216882608848503 235036636825323913272755)
            ·
              refine ⟨352554955237985869909133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235036636825323913272755 352554955237985869909133)
              ·
                refine ⟨132208108214244701215925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 352554955237985869909133 132208108214244701215925)
                ·
                  refine ⟨12394510145085440738993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132208108214244701215925 12394510145085440738993)
                  ·
                    rfl

theorem cell21_54311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 5].length) (baseStart_54311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_54311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_54311 prefixEnd_54311 := by exact prefixLift 54311
  have htrace : WordTrace (prefixWord ++ tailWord_54311) baseStart_54311 baseEnd_54311 := by
    simpa [prefixWord, tailWord_54311, baseEnd_54311] using wordTrace_append hprefix tailTrace_54311
  have hstable : (prefixWord ++ tailWord_54311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54311).length < 2 ^ (prefixWord ++ tailWord_54311).sum := by decide
  have hdescent : baseEnd_54311 < baseStart_54311 := by decide
  rcases family_descends (prefixWord ++ tailWord_54311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54342 : List Nat := [6, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_54342 : Nat := 118140960795 + 54342 * 2 ^ 59
def prefixEnd_54342 : Nat := 4983230072969 + 3 ^ 40 * 54342 * 2
def baseEnd_54342 : Nat := 12401584767436275722263

theorem tailTrace_54342 : CollatzResearch.WordTrace tailWord_54342 prefixEnd_54342 12401584767436275722263 := by
  unfold tailWord_54342
  simp only [CollatzResearch.WordTrace]
  refine ⟨61937986535490303744415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1321343712757126479880853 61937986535490303744415)
  ·
    refine ⟨92906979803235455616623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61937986535490303744415 92906979803235455616623)
    ·
      refine ⟨139360469704853183424935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92906979803235455616623 139360469704853183424935)
      ·
        refine ⟨209040704557279775137403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139360469704853183424935 209040704557279775137403)
        ·
          refine ⟨313561056835919662706105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209040704557279775137403 313561056835919662706105)
          ·
            refine ⟨235170792626939747029579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313561056835919662706105 235170792626939747029579)
            ·
              refine ⟨352756188940409620544369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235170792626939747029579 352756188940409620544369)
              ·
                refine ⟨264567141705307215408277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 352756188940409620544369 264567141705307215408277)
                ·
                  refine ⟨12401584767436275722263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 264567141705307215408277 12401584767436275722263)
                  ·
                    rfl

theorem cell21_54342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_54342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_54342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_54342 prefixEnd_54342 := by exact prefixLift 54342
  have htrace : WordTrace (prefixWord ++ tailWord_54342) baseStart_54342 baseEnd_54342 := by
    simpa [prefixWord, tailWord_54342, baseEnd_54342] using wordTrace_append hprefix tailTrace_54342
  have hstable : (prefixWord ++ tailWord_54342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54342).length < 2 ^ (prefixWord ++ tailWord_54342).sum := by decide
  have hdescent : baseEnd_54342 < baseStart_54342 := by decide
  rcases family_descends (prefixWord ++ tailWord_54342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54353 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 7]
def baseStart_54353 : Nat := 118140960795 + 54353 * 2 ^ 59
def prefixEnd_54353 : Nat := 4983230072969 + 3 ^ 40 * 54353 * 2
def baseEnd_54353 : Nat := 12404095117302701038907

theorem tailTrace_54353 : CollatzResearch.WordTrace tailWord_54353 prefixEnd_54353 12404095117302701038907 := by
  unfold tailWord_54353
  simp only [CollatzResearch.WordTrace]
  refine ⟨1982416772095838598471713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1321611181397225732314475 1982416772095838598471713)
  ·
    refine ⟨1486812579071878948853785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1982416772095838598471713 1486812579071878948853785)
    ·
      refine ⟨1115109434303909211640339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1486812579071878948853785 1115109434303909211640339)
      ·
        refine ⟨1672664151455863817460509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1115109434303909211640339 1672664151455863817460509)
        ·
          refine ⟨627249056795948931547691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1672664151455863817460509 627249056795948931547691)
          ·
            refine ⟨940873585193923397321537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627249056795948931547691 940873585193923397321537)
            ·
              refine ⟨705655188895442547991153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 940873585193923397321537 705655188895442547991153)
              ·
                refine ⟨529241391671581910993365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 705655188895442547991153 529241391671581910993365)
                ·
                  refine ⟨12404095117302701038907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 529241391671581910993365 12404095117302701038907)
                  ·
                    rfl

theorem cell21_54353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 7].length) (baseStart_54353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_54353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_54353 prefixEnd_54353 := by exact prefixLift 54353
  have htrace : WordTrace (prefixWord ++ tailWord_54353) baseStart_54353 baseEnd_54353 := by
    simpa [prefixWord, tailWord_54353, baseEnd_54353] using wordTrace_append hprefix tailTrace_54353
  have hstable : (prefixWord ++ tailWord_54353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54353).length < 2 ^ (prefixWord ++ tailWord_54353).sum := by decide
  have hdescent : baseEnd_54353 < baseStart_54353 := by decide
  rcases family_descends (prefixWord ++ tailWord_54353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54376 : List Nat := [2, 1, 4, 4, 1, 2, 2, 1, 4]
def baseStart_54376 : Nat := 118140960795 + 54376 * 2 ^ 59
def prefixEnd_54376 : Nat := 4983230072969 + 3 ^ 40 * 54376 * 2
def baseEnd_54376 : Nat := 12409344030659772155527

theorem tailTrace_54376 : CollatzResearch.WordTrace tailWord_54376 prefixEnd_54376 12409344030659772155527 := by
  unfold tailWord_54376
  simp only [CollatzResearch.WordTrace]
  refine ⟨991627825506256763279491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1322170434008342351039321 991627825506256763279491)
  ·
    refine ⟨1487441738259385144919237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 991627825506256763279491 1487441738259385144919237)
    ·
      refine ⟨278895325923634714672357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1487441738259385144919237 278895325923634714672357)
      ·
        refine ⟨52292873610681509001067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278895325923634714672357 52292873610681509001067)
        ·
          refine ⟨78439310416022263501601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52292873610681509001067 78439310416022263501601)
          ·
            refine ⟨58829482812016697626201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78439310416022263501601 58829482812016697626201)
            ·
              refine ⟨44122112109012523219651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58829482812016697626201 44122112109012523219651)
              ·
                refine ⟨66183168163518784829477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44122112109012523219651 66183168163518784829477)
                ·
                  refine ⟨12409344030659772155527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66183168163518784829477 12409344030659772155527)
                  ·
                    rfl

theorem cell21_54376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 4].length) (baseStart_54376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_54376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_54376 prefixEnd_54376 := by exact prefixLift 54376
  have htrace : WordTrace (prefixWord ++ tailWord_54376) baseStart_54376 baseEnd_54376 := by
    simpa [prefixWord, tailWord_54376, baseEnd_54376] using wordTrace_append hprefix tailTrace_54376
  have hstable : (prefixWord ++ tailWord_54376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54376).length < 2 ^ (prefixWord ++ tailWord_54376).sum := by decide
  have hdescent : baseEnd_54376 < baseStart_54376 := by decide
  rcases family_descends (prefixWord ++ tailWord_54376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54418 : List Nat := [3, 2, 3, 1, 1, 3, 2, 2, 4]
def baseStart_54418 : Nat := 118140960795 + 54418 * 2 ^ 59
def prefixEnd_54418 : Nat := 4983230072969 + 3 ^ 40 * 54418 * 2
def baseEnd_54418 : Nat := 12418929002877032455441

theorem tailTrace_54418 : CollatzResearch.WordTrace tailWord_54418 prefixEnd_54418 12418929002877032455441 := by
  unfold tailWord_54418
  simp only [CollatzResearch.WordTrace]
  refine ⟨496196879215088674896977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1323191677906903133058605 496196879215088674896977)
  ·
    refine ⟨372147659411316506172733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 496196879215088674896977 372147659411316506172733)
    ·
      refine ⟨139555372279243689814775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 372147659411316506172733 139555372279243689814775)
      ·
        refine ⟨209333058418865534722163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139555372279243689814775 209333058418865534722163)
        ·
          refine ⟨313999587628298302083245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209333058418865534722163 313999587628298302083245)
          ·
            refine ⟨117749845360611863281217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 313999587628298302083245 117749845360611863281217)
            ·
              refine ⟨88312384020458897460913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117749845360611863281217 88312384020458897460913)
              ·
                refine ⟨66234288015344173095685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88312384020458897460913 66234288015344173095685)
                ·
                  refine ⟨12418929002877032455441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66234288015344173095685 12418929002877032455441)
                  ·
                    rfl

theorem cell21_54418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_54418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_54418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_54418 prefixEnd_54418 := by exact prefixLift 54418
  have htrace : WordTrace (prefixWord ++ tailWord_54418) baseStart_54418 baseEnd_54418 := by
    simpa [prefixWord, tailWord_54418, baseEnd_54418] using wordTrace_append hprefix tailTrace_54418
  have hstable : (prefixWord ++ tailWord_54418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54418).length < 2 ^ (prefixWord ++ tailWord_54418).sum := by decide
  have hdescent : baseEnd_54418 < baseStart_54418 := by decide
  rcases family_descends (prefixWord ++ tailWord_54418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54508 : List Nat := [2, 2, 1, 1, 2, 6, 2, 5]
def baseStart_54508 : Nat := 118140960795 + 54508 * 2 ^ 59
def prefixEnd_54508 : Nat := 4983230072969 + 3 ^ 40 * 54508 * 2
def baseEnd_54508 : Nat := 4146489409685625318419

theorem tailTrace_54508 : CollatzResearch.WordTrace tailWord_54508 prefixEnd_54508 4146489409685625318419 := by
  unfold tailWord_54508
  simp only [CollatzResearch.WordTrace]
  refine ⟨994035043267150035182089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1325380057689533380242785 994035043267150035182089)
  ·
    refine ⟨745526282450362526386567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 994035043267150035182089 745526282450362526386567)
    ·
      refine ⟨1118289423675543789579851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 745526282450362526386567 1118289423675543789579851)
      ·
        refine ⟨1677434135513315684369777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1118289423675543789579851 1677434135513315684369777)
        ·
          refine ⟨1258075601634986763277333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1677434135513315684369777 1258075601634986763277333)
          ·
            refine ⟨58972293826640004528625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1258075601634986763277333 58972293826640004528625)
            ·
              refine ⟨44229220369980003396469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58972293826640004528625 44229220369980003396469)
              ·
                refine ⟨4146489409685625318419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44229220369980003396469 4146489409685625318419)
                ·
                  rfl

theorem cell21_54508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 5].length) (baseStart_54508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_54508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_54508 prefixEnd_54508 := by exact prefixLift 54508
  have htrace : WordTrace (prefixWord ++ tailWord_54508) baseStart_54508 baseEnd_54508 := by
    simpa [prefixWord, tailWord_54508, baseEnd_54508] using wordTrace_append hprefix tailTrace_54508
  have hstable : (prefixWord ++ tailWord_54508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54508).length < 2 ^ (prefixWord ++ tailWord_54508).sum := by decide
  have hdescent : baseEnd_54508 < baseStart_54508 := by decide
  rcases family_descends (prefixWord ++ tailWord_54508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54632 : List Nat := [2, 1, 4, 2, 3, 1, 2, 3, 3]
def baseStart_54632 : Nat := 118140960795 + 54632 * 2 ^ 59
def prefixEnd_54632 : Nat := 4983230072969 + 3 ^ 40 * 54632 * 2
def baseEnd_54632 : Nat := 12467766718460215888337

theorem tailTrace_54632 : CollatzResearch.WordTrace tailWord_54632 prefixEnd_54632 12467766718460215888337 := by
  unfold tailWord_54632
  simp only [CollatzResearch.WordTrace]
  refine ⟨996296369042534623939075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1328395158723379498585433 996296369042534623939075)
  ·
    refine ⟨1494444553563801935908613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 996296369042534623939075 1494444553563801935908613)
    ·
      refine ⟨280208353793212862982865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1494444553563801935908613 280208353793212862982865)
      ·
        refine ⟨210156265344909647237149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280208353793212862982865 210156265344909647237149)
        ·
          refine ⟨78808599504341117713931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210156265344909647237149 78808599504341117713931)
          ·
            refine ⟨118212899256511676570897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78808599504341117713931 118212899256511676570897)
            ·
              refine ⟨88659674442383757428173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118212899256511676570897 88659674442383757428173)
              ·
                refine ⟨33247377915893909035565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88659674442383757428173 33247377915893909035565)
                ·
                  refine ⟨12467766718460215888337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33247377915893909035565 12467766718460215888337)
                  ·
                    rfl

theorem cell21_54632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3, 3].length) (baseStart_54632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_54632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_54632 prefixEnd_54632 := by exact prefixLift 54632
  have htrace : WordTrace (prefixWord ++ tailWord_54632) baseStart_54632 baseEnd_54632 := by
    simpa [prefixWord, tailWord_54632, baseEnd_54632] using wordTrace_append hprefix tailTrace_54632
  have hstable : (prefixWord ++ tailWord_54632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54632).length < 2 ^ (prefixWord ++ tailWord_54632).sum := by decide
  have hdescent : baseEnd_54632 < baseStart_54632 := by decide
  rcases family_descends (prefixWord ++ tailWord_54632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54767 : List Nat := [1, 1, 2, 1, 4, 1, 6, 2, 3]
def baseStart_54767 : Nat := 118140960795 + 54767 * 2 ^ 59
def prefixEnd_54767 : Nat := 4983230072969 + 3 ^ 40 * 54767 * 2
def baseEnd_54767 : Nat := 12498575557729981138061

theorem tailTrace_54767 : CollatzResearch.WordTrace tailWord_54767 prefixEnd_54767 12498575557729981138061 := by
  unfold tailWord_54767
  simp only [CollatzResearch.WordTrace]
  refine ⟨1997516592595987304042555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1331677728397324869361703 1997516592595987304042555)
  ·
    refine ⟨2996274888893980956063833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1997516592595987304042555 2996274888893980956063833)
    ·
      refine ⟨2247206166670485717047875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2996274888893980956063833 2247206166670485717047875)
      ·
        refine ⟨3370809250005728575571813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2247206166670485717047875 3370809250005728575571813)
        ·
          refine ⟨632026734376074107919715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3370809250005728575571813 632026734376074107919715)
          ·
            refine ⟨948040101564111161879573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632026734376074107919715 948040101564111161879573)
            ·
              refine ⟨44439379760817710713105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 948040101564111161879573 44439379760817710713105)
              ·
                refine ⟨33329534820613283034829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44439379760817710713105 33329534820613283034829)
                ·
                  refine ⟨12498575557729981138061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33329534820613283034829 12498575557729981138061)
                  ·
                    rfl

theorem cell21_54767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2, 3].length) (baseStart_54767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_54767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_54767 prefixEnd_54767 := by exact prefixLift 54767
  have htrace : WordTrace (prefixWord ++ tailWord_54767) baseStart_54767 baseEnd_54767 := by
    simpa [prefixWord, tailWord_54767, baseEnd_54767] using wordTrace_append hprefix tailTrace_54767
  have hstable : (prefixWord ++ tailWord_54767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54767).length < 2 ^ (prefixWord ++ tailWord_54767).sum := by decide
  have hdescent : baseEnd_54767 < baseStart_54767 := by decide
  rcases family_descends (prefixWord ++ tailWord_54767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54826 : List Nat := [3, 1, 4, 1, 1, 1, 4, 1, 5]
def baseStart_54826 : Nat := 118140960795 + 54826 * 2 ^ 59
def prefixEnd_54826 : Nat := 4983230072969 + 3 ^ 40 * 54826 * 2
def baseEnd_54826 : Nat := 12512040161558989654607

theorem tailTrace_54826 : CollatzResearch.WordTrace tailWord_54826 prefixEnd_54826 12512040161558989654607 := by
  unfold tailWord_54826
  simp only [CollatzResearch.WordTrace]
  refine ⟨499917124845560095110083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1333112332921493586960221 499917124845560095110083)
  ·
    refine ⟨749875687268340142665125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 499917124845560095110083 749875687268340142665125)
    ·
      refine ⟨140601691362813776749711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 749875687268340142665125 140601691362813776749711)
      ·
        refine ⟨210902537044220665124567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140601691362813776749711 210902537044220665124567)
        ·
          refine ⟨316353805566330997686851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210902537044220665124567 316353805566330997686851)
          ·
            refine ⟨474530708349496496530277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316353805566330997686851 474530708349496496530277)
            ·
              refine ⟨88974507815530593099427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 474530708349496496530277 88974507815530593099427)
              ·
                refine ⟨133461761723295889649141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88974507815530593099427 133461761723295889649141)
                ·
                  refine ⟨12512040161558989654607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133461761723295889649141 12512040161558989654607)
                  ·
                    rfl

theorem cell21_54826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_54826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_54826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_54826 prefixEnd_54826 := by exact prefixLift 54826
  have htrace : WordTrace (prefixWord ++ tailWord_54826) baseStart_54826 baseEnd_54826 := by
    simpa [prefixWord, tailWord_54826, baseEnd_54826] using wordTrace_append hprefix tailTrace_54826
  have hstable : (prefixWord ++ tailWord_54826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54826).length < 2 ^ (prefixWord ++ tailWord_54826).sum := by decide
  have hdescent : baseEnd_54826 < baseStart_54826 := by decide
  rcases family_descends (prefixWord ++ tailWord_54826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54877 : List Nat := [1, 4, 4, 2, 2, 1, 1, 1, 5]
def baseStart_54877 : Nat := 118140960795 + 54877 * 2 ^ 59
def prefixEnd_54877 : Nat := 4983230072969 + 3 ^ 40 * 54877 * 2
def baseEnd_54877 : Nat := 12523679056394234304503

theorem tailTrace_54877 : CollatzResearch.WordTrace tailWord_54877 prefixEnd_54877 12523679056394234304503 := by
  unfold tailWord_54877
  simp only [CollatzResearch.WordTrace]
  refine ⟨2001528622197476090546885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1334352414798317393697923 2001528622197476090546885)
  ·
    refine ⟨375286616662026766977541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2001528622197476090546885 375286616662026766977541)
    ·
      refine ⟨70366240624130018808289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 375286616662026766977541 70366240624130018808289)
      ·
        refine ⟨52774680468097514106217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70366240624130018808289 52774680468097514106217)
        ·
          refine ⟨39581010351073135579663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52774680468097514106217 39581010351073135579663)
          ·
            refine ⟨59371515526609703369495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39581010351073135579663 59371515526609703369495)
            ·
              refine ⟨89057273289914555054243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59371515526609703369495 89057273289914555054243)
              ·
                refine ⟨133585909934871832581365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89057273289914555054243 133585909934871832581365)
                ·
                  refine ⟨12523679056394234304503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133585909934871832581365 12523679056394234304503)
                  ·
                    rfl

theorem cell21_54877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_54877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_54877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_54877 prefixEnd_54877 := by exact prefixLift 54877
  have htrace : WordTrace (prefixWord ++ tailWord_54877) baseStart_54877 baseEnd_54877 := by
    simpa [prefixWord, tailWord_54877, baseEnd_54877] using wordTrace_append hprefix tailTrace_54877
  have hstable : (prefixWord ++ tailWord_54877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54877).length < 2 ^ (prefixWord ++ tailWord_54877).sum := by decide
  have hdescent : baseEnd_54877 < baseStart_54877 := by decide
  rcases family_descends (prefixWord ++ tailWord_54877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54930 : List Nat := [3, 2, 3, 1, 12]
def baseStart_54930 : Nat := 118140960795 + 54930 * 2 ^ 59
def prefixEnd_54930 : Nat := 4983230072969 + 3 ^ 40 * 54930 * 2
def baseEnd_54930 : Nat := 154762646647875554581

theorem tailTrace_54930 : CollatzResearch.WordTrace tailWord_54930 prefixEnd_54930 154762646647875554581 := by
  unfold tailWord_54930
  simp only [CollatzResearch.WordTrace]
  refine ⟨500865422751366535556561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1335641127336977428150829 500865422751366535556561)
  ·
    refine ⟨375649067063524901667421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 500865422751366535556561 375649067063524901667421)
    ·
      refine ⟨140868400148821838125283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375649067063524901667421 140868400148821838125283)
      ·
        refine ⟨211302600223232757187925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140868400148821838125283 211302600223232757187925)
        ·
          refine ⟨154762646647875554581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 211302600223232757187925 154762646647875554581)
          ·
            rfl

theorem cell21_54930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 12].length) (baseStart_54930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_54930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_54930 prefixEnd_54930 := by exact prefixLift 54930
  have htrace : WordTrace (prefixWord ++ tailWord_54930) baseStart_54930 baseEnd_54930 := by
    simpa [prefixWord, tailWord_54930, baseEnd_54930] using wordTrace_append hprefix tailTrace_54930
  have hstable : (prefixWord ++ tailWord_54930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54930).length < 2 ^ (prefixWord ++ tailWord_54930).sum := by decide
  have hdescent : baseEnd_54930 < baseStart_54930 := by decide
  rcases family_descends (prefixWord ++ tailWord_54930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54936 : List Nat := [2, 1, 2, 4, 1, 4, 2, 2, 3]
def baseStart_54936 : Nat := 118140960795 + 54936 * 2 ^ 59
def prefixEnd_54936 : Nat := 4983230072969 + 3 ^ 40 * 54936 * 2
def baseEnd_54936 : Nat := 12537143660223242821049

theorem tailTrace_54936 : CollatzResearch.WordTrace tailWord_54936 prefixEnd_54936 12537143660223242821049 := by
  unfold tailWord_54936
  simp only [CollatzResearch.WordTrace]
  refine ⟨1001840264491864583472331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1335787019322486111296441 1001840264491864583472331)
  ·
    refine ⟨1502760396737796875208497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1001840264491864583472331 1502760396737796875208497)
    ·
      refine ⟨1127070297553347656406373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1502760396737796875208497 1127070297553347656406373)
      ·
        refine ⟨211325680791252685576195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1127070297553347656406373 211325680791252685576195)
        ·
          refine ⟨316988521186879028364293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211325680791252685576195 316988521186879028364293)
          ·
            refine ⟨59435347722539817818305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 316988521186879028364293 59435347722539817818305)
            ·
              refine ⟨44576510791904863363729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59435347722539817818305 44576510791904863363729)
              ·
                refine ⟨33432383093928647522797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44576510791904863363729 33432383093928647522797)
                ·
                  refine ⟨12537143660223242821049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33432383093928647522797 12537143660223242821049)
                  ·
                    rfl

theorem cell21_54936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2, 3].length) (baseStart_54936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_54936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_54936 prefixEnd_54936 := by exact prefixLift 54936
  have htrace : WordTrace (prefixWord ++ tailWord_54936) baseStart_54936 baseEnd_54936 := by
    simpa [prefixWord, tailWord_54936, baseEnd_54936] using wordTrace_append hprefix tailTrace_54936
  have hstable : (prefixWord ++ tailWord_54936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54936).length < 2 ^ (prefixWord ++ tailWord_54936).sum := by decide
  have hdescent : baseEnd_54936 < baseStart_54936 := by decide
  rcases family_descends (prefixWord ++ tailWord_54936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54975 : List Nat := [1, 1, 2, 2, 2, 3, 2, 2, 6]
def baseStart_54975 : Nat := 118140960795 + 54975 * 2 ^ 59
def prefixEnd_54975 : Nat := 4983230072969 + 3 ^ 40 * 54975 * 2
def baseEnd_54975 : Nat := 12546043991567841670969

theorem tailTrace_54975 : CollatzResearch.WordTrace tailWord_54975 prefixEnd_54975 12546043991567841670969 := by
  unfold tailWord_54975
  simp only [CollatzResearch.WordTrace]
  refine ⟨2005102975842438827614379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1336735317228292551742919 2005102975842438827614379)
  ·
    refine ⟨3007654463763658241421569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2005102975842438827614379 3007654463763658241421569)
    ·
      refine ⟨2255740847822743681066177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3007654463763658241421569 2255740847822743681066177)
      ·
        refine ⟨1691805635867057760799633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2255740847822743681066177 1691805635867057760799633)
        ·
          refine ⟨1268854226900293320599725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1691805635867057760799633 1268854226900293320599725)
          ·
            refine ⟨475820335087609995224897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1268854226900293320599725 475820335087609995224897)
            ·
              refine ⟨356865251315707496418673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 475820335087609995224897 356865251315707496418673)
              ·
                refine ⟨267648938486780622314005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356865251315707496418673 267648938486780622314005)
                ·
                  refine ⟨12546043991567841670969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 267648938486780622314005 12546043991567841670969)
                  ·
                    rfl

theorem cell21_54975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 6].length) (baseStart_54975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_54975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_54975 prefixEnd_54975 := by exact prefixLift 54975
  have htrace : WordTrace (prefixWord ++ tailWord_54975) baseStart_54975 baseEnd_54975 := by
    simpa [prefixWord, tailWord_54975, baseEnd_54975] using wordTrace_append hprefix tailTrace_54975
  have hstable : (prefixWord ++ tailWord_54975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54975).length < 2 ^ (prefixWord ++ tailWord_54975).sum := by decide
  have hdescent : baseEnd_54975 < baseStart_54975 := by decide
  rcases family_descends (prefixWord ++ tailWord_54975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55051 : List Nat := [1, 1, 1, 1, 5, 1, 4, 1, 6]
def baseStart_55051 : Nat := 118140960795 + 55051 * 2 ^ 59
def prefixEnd_55051 : Nat := 4983230072969 + 3 ^ 40 * 55051 * 2
def baseEnd_55051 : Nat := 12563388227008598404147

theorem tailTrace_55051 : CollatzResearch.WordTrace tailWord_55051 prefixEnd_55051 12563388227008598404147 := by
  unfold tailWord_55051
  simp only [CollatzResearch.WordTrace]
  refine ⟨2007874923567103807381007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1338583282378069204920671 2007874923567103807381007)
  ·
    refine ⟨3011812385350655711071511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2007874923567103807381007 3011812385350655711071511)
    ·
      refine ⟨4517718578025983566607267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3011812385350655711071511 4517718578025983566607267)
      ·
        refine ⟨6776577867038975349910901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4517718578025983566607267 6776577867038975349910901)
        ·
          refine ⟨635304175034903939054147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6776577867038975349910901 635304175034903939054147)
          ·
            refine ⟨952956262552355908581221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635304175034903939054147 952956262552355908581221)
            ·
              refine ⟨178679299228566732858979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 952956262552355908581221 178679299228566732858979)
              ·
                refine ⟨268018948842850099288469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178679299228566732858979 268018948842850099288469)
                ·
                  refine ⟨12563388227008598404147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 268018948842850099288469 12563388227008598404147)
                  ·
                    rfl

theorem cell21_55051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 6].length) (baseStart_55051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_55051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_55051 prefixEnd_55051 := by exact prefixLift 55051
  have htrace : WordTrace (prefixWord ++ tailWord_55051) baseStart_55051 baseEnd_55051 := by
    simpa [prefixWord, tailWord_55051, baseEnd_55051] using wordTrace_append hprefix tailTrace_55051
  have hstable : (prefixWord ++ tailWord_55051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55051).length < 2 ^ (prefixWord ++ tailWord_55051).sum := by decide
  have hdescent : baseEnd_55051 < baseStart_55051 := by decide
  rcases family_descends (prefixWord ++ tailWord_55051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55054 : List Nat := [4, 1, 1, 2, 1, 1, 2, 6, 3]
def baseStart_55054 : Nat := 118140960795 + 55054 * 2 ^ 59
def prefixEnd_55054 : Nat := 4983230072969 + 3 ^ 40 * 55054 * 2
def baseEnd_55054 : Nat := 12564072867881259854141

theorem tailTrace_55054 : CollatzResearch.WordTrace tailWord_55054 prefixEnd_55054 12564072867881259854141 := by
  unfold tailWord_55054
  simp only [CollatzResearch.WordTrace]
  refine ⟨250998042819529414967527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1338656228370823546493477 250998042819529414967527)
  ·
    refine ⟨376497064229294122451291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250998042819529414967527 376497064229294122451291)
    ·
      refine ⟨564745596343941183676937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376497064229294122451291 564745596343941183676937)
      ·
        refine ⟨423559197257955887757703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 564745596343941183676937 423559197257955887757703)
        ·
          refine ⟨635338795886933831636555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423559197257955887757703 635338795886933831636555)
          ·
            refine ⟨953008193830400747454833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635338795886933831636555 953008193830400747454833)
            ·
              refine ⟨714756145372800560591125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 953008193830400747454833 714756145372800560591125)
              ·
                refine ⟨33504194314350026277709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 714756145372800560591125 33504194314350026277709)
                ·
                  refine ⟨12564072867881259854141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33504194314350026277709 12564072867881259854141)
                  ·
                    rfl

theorem cell21_55054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_55054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_55054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_55054 prefixEnd_55054 := by exact prefixLift 55054
  have htrace : WordTrace (prefixWord ++ tailWord_55054) baseStart_55054 baseEnd_55054 := by
    simpa [prefixWord, tailWord_55054, baseEnd_55054] using wordTrace_append hprefix tailTrace_55054
  have hstable : (prefixWord ++ tailWord_55054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55054).length < 2 ^ (prefixWord ++ tailWord_55054).sum := by decide
  have hdescent : baseEnd_55054 < baseStart_55054 := by decide
  rcases family_descends (prefixWord ++ tailWord_55054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55068 : List Nat := [2, 2, 3, 1, 1, 2, 3, 3, 4]
def baseStart_55068 : Nat := 118140960795 + 55068 * 2 ^ 59
def prefixEnd_55068 : Nat := 4983230072969 + 3 ^ 40 * 55068 * 2
def baseEnd_55068 : Nat := 12567267858620346620779

theorem tailTrace_55068 : CollatzResearch.WordTrace tailWord_55068 prefixEnd_55068 12567267858620346620779 := by
  unfold tailWord_55068
  simp only [CollatzResearch.WordTrace]
  refine ⟨1004247482252757855374929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1338996643003677140499905 1004247482252757855374929)
  ·
    refine ⟨753185611689568391531197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1004247482252757855374929 753185611689568391531197)
    ·
      refine ⟨282444604383588146824199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 753185611689568391531197 282444604383588146824199)
      ·
        refine ⟨423666906575382220236299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282444604383588146824199 423666906575382220236299)
        ·
          refine ⟨635500359863073330354449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423666906575382220236299 635500359863073330354449)
          ·
            refine ⟨476625269897304997765837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 635500359863073330354449 476625269897304997765837)
            ·
              refine ⟨178734476211489374162189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 476625269897304997765837 178734476211489374162189)
              ·
                refine ⟨67025428579308515310821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178734476211489374162189 67025428579308515310821)
                ·
                  refine ⟨12567267858620346620779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67025428579308515310821 12567267858620346620779)
                  ·
                    rfl

theorem cell21_55068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_55068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_55068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_55068 prefixEnd_55068 := by exact prefixLift 55068
  have htrace : WordTrace (prefixWord ++ tailWord_55068) baseStart_55068 baseEnd_55068 := by
    simpa [prefixWord, tailWord_55068, baseEnd_55068] using wordTrace_append hprefix tailTrace_55068
  have hstable : (prefixWord ++ tailWord_55068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55068).length < 2 ^ (prefixWord ++ tailWord_55068).sum := by decide
  have hdescent : baseEnd_55068 < baseStart_55068 := by decide
  rcases family_descends (prefixWord ++ tailWord_55068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55116 : List Nat := [2, 2, 1, 3, 5, 1, 1, 6]
def baseStart_55116 : Nat := 118140960795 + 55116 * 2 ^ 59
def prefixEnd_55116 : Nat := 4983230072969 + 3 ^ 40 * 55116 * 2
def baseEnd_55116 : Nat := 4192740704194309940227

theorem tailTrace_55116 : CollatzResearch.WordTrace tailWord_55116 prefixEnd_55116 4192740704194309940227 := by
  unfold tailWord_55116
  simp only [CollatzResearch.WordTrace]
  refine ⟨1005122834165809954248601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1340163778887746605664801 1005122834165809954248601)
  ·
    refine ⟨753842125624357465686451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1005122834165809954248601 753842125624357465686451)
    ·
      refine ⟨1130763188436536198529677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 753842125624357465686451 1130763188436536198529677)
      ·
        refine ⟨424036195663701074448629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1130763188436536198529677 424036195663701074448629)
        ·
          refine ⟨39753393343471975729559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 424036195663701074448629 39753393343471975729559)
          ·
            refine ⟨59630090015207963594339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39753393343471975729559 59630090015207963594339)
            ·
              refine ⟨89445135022811945391509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59630090015207963594339 89445135022811945391509)
              ·
                refine ⟨4192740704194309940227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89445135022811945391509 4192740704194309940227)
                ·
                  rfl

theorem cell21_55116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 6].length) (baseStart_55116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_55116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_55116 prefixEnd_55116 := by exact prefixLift 55116
  have htrace : WordTrace (prefixWord ++ tailWord_55116) baseStart_55116 baseEnd_55116 := by
    simpa [prefixWord, tailWord_55116, baseEnd_55116] using wordTrace_append hprefix tailTrace_55116
  have hstable : (prefixWord ++ tailWord_55116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55116).length < 2 ^ (prefixWord ++ tailWord_55116).sum := by decide
  have hdescent : baseEnd_55116 < baseStart_55116 := by decide
  rcases family_descends (prefixWord ++ tailWord_55116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55178 : List Nat := [3, 1, 2, 4, 2, 1, 3, 1, 4]
def baseStart_55178 : Nat := 118140960795 + 55178 * 2 ^ 59
def prefixEnd_55178 : Nat := 4983230072969 + 3 ^ 40 * 55178 * 2
def baseEnd_55178 : Nat := 12592371357284599787221

theorem tailTrace_55178 : CollatzResearch.WordTrace tailWord_55178 prefixEnd_55178 12592371357284599787221 := by
  unfold tailWord_55178
  simp only [CollatzResearch.WordTrace]
  refine ⟨503126748526751124313547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1341671329404669664836125 503126748526751124313547)
  ·
    refine ⟨754690122790126686470321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 503126748526751124313547 754690122790126686470321)
    ·
      refine ⟨566017592092595014852741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 754690122790126686470321 566017592092595014852741)
      ·
        refine ⟨106128298517361565284889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 566017592092595014852741 106128298517361565284889)
        ·
          refine ⟨79596223888021173963667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106128298517361565284889 79596223888021173963667)
          ·
            refine ⟨119394335832031760945501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79596223888021173963667 119394335832031760945501)
            ·
              refine ⟨44772875937011910354563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119394335832031760945501 44772875937011910354563)
              ·
                refine ⟨67159313905517865531845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44772875937011910354563 67159313905517865531845)
                ·
                  refine ⟨12592371357284599787221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67159313905517865531845 12592371357284599787221)
                  ·
                    rfl

theorem cell21_55178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_55178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_55178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_55178 prefixEnd_55178 := by exact prefixLift 55178
  have htrace : WordTrace (prefixWord ++ tailWord_55178) baseStart_55178 baseEnd_55178 := by
    simpa [prefixWord, tailWord_55178, baseEnd_55178] using wordTrace_append hprefix tailTrace_55178
  have hstable : (prefixWord ++ tailWord_55178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55178).length < 2 ^ (prefixWord ++ tailWord_55178).sum := by decide
  have hdescent : baseEnd_55178 < baseStart_55178 := by decide
  rcases family_descends (prefixWord ++ tailWord_55178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55198 : List Nat := [4, 3, 1, 3, 2, 1, 1, 3, 3]
def baseStart_55198 : Nat := 118140960795 + 55198 * 2 ^ 59
def prefixEnd_55198 : Nat := 4983230072969 + 3 ^ 40 * 55198 * 2
def baseEnd_55198 : Nat := 12596935629769009453847

theorem tailTrace_55198 : CollatzResearch.WordTrace tailWord_55198 prefixEnd_55198 12596935629769009453847 := by
  unfold tailWord_55198
  simp only [CollatzResearch.WordTrace]
  refine ⟨251654556754318489122781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1342157636023031941988165 251654556754318489122781)
  ·
    refine ⟨94370458782869433421043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251654556754318489122781 94370458782869433421043)
    ·
      refine ⟨141555688174304150131565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94370458782869433421043 141555688174304150131565)
      ·
        refine ⟨53083383065364056299337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141555688174304150131565 53083383065364056299337)
        ·
          refine ⟨39812537299023042224503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53083383065364056299337 39812537299023042224503)
          ·
            refine ⟨59718805948534563336755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39812537299023042224503 59718805948534563336755)
            ·
              refine ⟨89578208922801845005133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59718805948534563336755 89578208922801845005133)
              ·
                refine ⟨33591828346050691876925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89578208922801845005133 33591828346050691876925)
                ·
                  refine ⟨12596935629769009453847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33591828346050691876925 12596935629769009453847)
                  ·
                    rfl

theorem cell21_55198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_55198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_55198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_55198 prefixEnd_55198 := by exact prefixLift 55198
  have htrace : WordTrace (prefixWord ++ tailWord_55198) baseStart_55198 baseEnd_55198 := by
    simpa [prefixWord, tailWord_55198, baseEnd_55198] using wordTrace_append hprefix tailTrace_55198
  have hstable : (prefixWord ++ tailWord_55198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55198).length < 2 ^ (prefixWord ++ tailWord_55198).sum := by decide
  have hdescent : baseEnd_55198 < baseStart_55198 := by decide
  rcases family_descends (prefixWord ++ tailWord_55198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55248 : List Nat := [2, 1, 1, 1, 1, 2, 4, 4, 5]
def baseStart_55248 : Nat := 118140960795 + 55248 * 2 ^ 59
def prefixEnd_55248 : Nat := 4983230072969 + 3 ^ 40 * 55248 * 2
def baseEnd_55248 : Nat := 12608346310980033620411

theorem tailTrace_55248 : CollatzResearch.WordTrace tailWord_55248 prefixEnd_55248 12608346310980033620411 := by
  unfold tailWord_55248
  simp only [CollatzResearch.WordTrace]
  refine ⟨1007530051926703226151199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1343373402568937634868265 1007530051926703226151199)
  ·
    refine ⟨1511295077890054839226799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1007530051926703226151199 1511295077890054839226799)
    ·
      refine ⟨2266942616835082258840199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1511295077890054839226799 2266942616835082258840199)
      ·
        refine ⟨3400413925252623388260299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2266942616835082258840199 3400413925252623388260299)
        ·
          refine ⟨5100620887878935082390449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3400413925252623388260299 5100620887878935082390449)
          ·
            refine ⟨3825465665909201311792837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5100620887878935082390449 3825465665909201311792837)
            ·
              refine ⟨717274812357975245961157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3825465665909201311792837 717274812357975245961157)
              ·
                refine ⟨134489027317120358617717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 717274812357975245961157 134489027317120358617717)
                ·
                  refine ⟨12608346310980033620411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134489027317120358617717 12608346310980033620411)
                  ·
                    rfl

theorem cell21_55248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 5].length) (baseStart_55248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_55248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_55248 prefixEnd_55248 := by exact prefixLift 55248
  have htrace : WordTrace (prefixWord ++ tailWord_55248) baseStart_55248 baseEnd_55248 := by
    simpa [prefixWord, tailWord_55248, baseEnd_55248] using wordTrace_append hprefix tailTrace_55248
  have hstable : (prefixWord ++ tailWord_55248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55248).length < 2 ^ (prefixWord ++ tailWord_55248).sum := by decide
  have hdescent : baseEnd_55248 < baseStart_55248 := by decide
  rcases family_descends (prefixWord ++ tailWord_55248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55369 : List Nat := [1, 2, 1, 1, 2, 2, 5, 7]
def baseStart_55369 : Nat := 118140960795 + 55369 * 2 ^ 59
def prefixEnd_55369 : Nat := 4983230072969 + 3 ^ 40 * 55369 * 2
def baseEnd_55369 : Nat := 4211986719836904034499

theorem tailTrace_55369 : CollatzResearch.WordTrace tailWord_55369 prefixEnd_55369 4211986719836904034499 := by
  unfold tailWord_55369
  simp only [CollatzResearch.WordTrace]
  refine ⟨2019473336415044117457161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1346315557610029411638107 2019473336415044117457161)
  ·
    refine ⟨1514605002311283088092871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2019473336415044117457161 1514605002311283088092871)
    ·
      refine ⟨2271907503466924632139307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1514605002311283088092871 2271907503466924632139307)
      ·
        refine ⟨3407861255200386948208961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2271907503466924632139307 3407861255200386948208961)
        ·
          refine ⟨2555895941400290211156721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3407861255200386948208961 2555895941400290211156721)
          ·
            refine ⟨1916921956050217658367541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2555895941400290211156721 1916921956050217658367541)
            ·
              refine ⟨179711433379707905471957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1916921956050217658367541 179711433379707905471957)
              ·
                refine ⟨4211986719836904034499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 179711433379707905471957 4211986719836904034499)
                ·
                  rfl

theorem cell21_55369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 7].length) (baseStart_55369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_55369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_55369 prefixEnd_55369 := by exact prefixLift 55369
  have htrace : WordTrace (prefixWord ++ tailWord_55369) baseStart_55369 baseEnd_55369 := by
    simpa [prefixWord, tailWord_55369, baseEnd_55369] using wordTrace_append hprefix tailTrace_55369
  have hstable : (prefixWord ++ tailWord_55369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55369).length < 2 ^ (prefixWord ++ tailWord_55369).sum := by decide
  have hdescent : baseEnd_55369 < baseStart_55369 := by decide
  rcases family_descends (prefixWord ++ tailWord_55369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55493 : List Nat := [1, 3, 1, 1, 1, 1, 5, 5, 3]
def baseStart_55493 : Nat := 118140960795 + 55493 * 2 ^ 59
def prefixEnd_55493 : Nat := 4983230072969 + 3 ^ 40 * 55493 * 2
def baseEnd_55493 : Nat := 12664258648914052036577

theorem tailTrace_55493 : CollatzResearch.WordTrace tailWord_55493 prefixEnd_55493 12664258648914052036577 := by
  unfold tailWord_55493
  simp only [CollatzResearch.WordTrace]
  refine ⟨2023995987965813294971133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1349330658643875529980755 2023995987965813294971133)
  ·
    refine ⟨758998495487179985614175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2023995987965813294971133 758998495487179985614175)
    ·
      refine ⟨1138497743230769978421263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 758998495487179985614175 1138497743230769978421263)
      ·
        refine ⟨1707746614846154967631895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1138497743230769978421263 1707746614846154967631895)
        ·
          refine ⟨2561619922269232451447843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1707746614846154967631895 2561619922269232451447843)
          ·
            refine ⟨3842429883403848677171765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2561619922269232451447843 3842429883403848677171765)
            ·
              refine ⟨360227801569110813484853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3842429883403848677171765 360227801569110813484853)
              ·
                refine ⟨33771356397104138764205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 360227801569110813484853 33771356397104138764205)
                ·
                  refine ⟨12664258648914052036577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33771356397104138764205 12664258648914052036577)
                  ·
                    rfl

theorem cell21_55493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5, 3].length) (baseStart_55493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_55493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_55493 prefixEnd_55493 := by exact prefixLift 55493
  have htrace : WordTrace (prefixWord ++ tailWord_55493) baseStart_55493 baseEnd_55493 := by
    simpa [prefixWord, tailWord_55493, baseEnd_55493] using wordTrace_append hprefix tailTrace_55493
  have hstable : (prefixWord ++ tailWord_55493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55493).length < 2 ^ (prefixWord ++ tailWord_55493).sum := by decide
  have hdescent : baseEnd_55493 < baseStart_55493 := by decide
  rcases family_descends (prefixWord ++ tailWord_55493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55510 : List Nat := [5, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_55510 : Nat := 118140960795 + 55510 * 2 ^ 59
def prefixEnd_55510 : Nat := 4983230072969 + 3 ^ 40 * 55510 * 2
def baseEnd_55510 : Nat := 12668138280525800253209

theorem tailTrace_55510 : CollatzResearch.WordTrace tailWord_55510 prefixEnd_55510 12668138280525800253209 := by
  unfold tailWord_55510
  simp only [CollatzResearch.WordTrace]
  refine ⟨126538501806514074896249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1349744019269483465559989 126538501806514074896249)
  ·
    refine ⟨94903876354885556172187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126538501806514074896249 94903876354885556172187)
    ·
      refine ⟨142355814532328334258281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94903876354885556172187 142355814532328334258281)
      ·
        refine ⟨106766860899246250693711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142355814532328334258281 106766860899246250693711)
        ·
          refine ⟨160150291348869376040567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106766860899246250693711 160150291348869376040567)
          ·
            refine ⟨240225437023304064060851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160150291348869376040567 240225437023304064060851)
            ·
              refine ⟨360338155534956096091277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240225437023304064060851 360338155534956096091277)
              ·
                refine ⟨135126808325608536034229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 360338155534956096091277 135126808325608536034229)
                ·
                  refine ⟨12668138280525800253209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135126808325608536034229 12668138280525800253209)
                  ·
                    rfl

theorem cell21_55510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_55510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_55510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_55510 prefixEnd_55510 := by exact prefixLift 55510
  have htrace : WordTrace (prefixWord ++ tailWord_55510) baseStart_55510 baseEnd_55510 := by
    simpa [prefixWord, tailWord_55510, baseEnd_55510] using wordTrace_append hprefix tailTrace_55510
  have hstable : (prefixWord ++ tailWord_55510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55510).length < 2 ^ (prefixWord ++ tailWord_55510).sum := by decide
  have hdescent : baseEnd_55510 < baseStart_55510 := by decide
  rcases family_descends (prefixWord ++ tailWord_55510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55521 : List Nat := [1, 2, 3, 1, 3, 1, 2, 8]
def baseStart_55521 : Nat := 118140960795 + 55521 * 2 ^ 59
def prefixEnd_55521 : Nat := 4983230072969 + 3 ^ 40 * 55521 * 2
def baseEnd_55521 : Nat := 4223549543464075189951

theorem tailTrace_55521 : CollatzResearch.WordTrace tailWord_55521 prefixEnd_55521 4223549543464075189951 := by
  unfold tailWord_55521
  simp only [CollatzResearch.WordTrace]
  refine ⟨2025017231864374076990417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1350011487909582717993611 2025017231864374076990417)
  ·
    refine ⟨1518762923898280557742813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2025017231864374076990417 1518762923898280557742813)
    ·
      refine ⟨569536096461855209153555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1518762923898280557742813 569536096461855209153555)
      ·
        refine ⟨854304144692782813730333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 569536096461855209153555 854304144692782813730333)
        ·
          refine ⟨320364054259793555148875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 854304144692782813730333 320364054259793555148875)
          ·
            refine ⟨480546081389690332723313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320364054259793555148875 480546081389690332723313)
            ·
              refine ⟨360409561042267749542485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480546081389690332723313 360409561042267749542485)
              ·
                refine ⟨4223549543464075189951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 360409561042267749542485 4223549543464075189951)
                ·
                  rfl

theorem cell21_55521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 8].length) (baseStart_55521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_55521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_55521 prefixEnd_55521 := by exact prefixLift 55521
  have htrace : WordTrace (prefixWord ++ tailWord_55521) baseStart_55521 baseEnd_55521 := by
    simpa [prefixWord, tailWord_55521, baseEnd_55521] using wordTrace_append hprefix tailTrace_55521
  have hstable : (prefixWord ++ tailWord_55521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55521).length < 2 ^ (prefixWord ++ tailWord_55521).sum := by decide
  have hdescent : baseEnd_55521 < baseStart_55521 := by decide
  rcases family_descends (prefixWord ++ tailWord_55521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55538 : List Nat := [3, 2, 1, 3, 2, 2, 1, 7]
def baseStart_55538 : Nat := 118140960795 + 55538 * 2 ^ 59
def prefixEnd_55538 : Nat := 4983230072969 + 3 ^ 40 * 55538 * 2
def baseEnd_55538 : Nat := 4224842754001324595495

theorem tailTrace_55538 : CollatzResearch.WordTrace tailWord_55538 prefixEnd_55538 4224842754001324595495 := by
  unfold tailWord_55538
  simp only [CollatzResearch.WordTrace]
  refine ⟨506409318200696495089817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1350424848535190653572845 506409318200696495089817)
  ·
    refine ⟨379806988650522371317363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 506409318200696495089817 379806988650522371317363)
    ·
      refine ⟨569710482975783556976045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379806988650522371317363 569710482975783556976045)
      ·
        refine ⟨213641431115918833866017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 569710482975783556976045 213641431115918833866017)
        ·
          refine ⟨160231073336939125399513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213641431115918833866017 160231073336939125399513)
          ·
            refine ⟨120173305002704344049635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160231073336939125399513 120173305002704344049635)
            ·
              refine ⟨180259957504056516074453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120173305002704344049635 180259957504056516074453)
              ·
                refine ⟨4224842754001324595495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 180259957504056516074453 4224842754001324595495)
                ·
                  rfl

theorem cell21_55538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 7].length) (baseStart_55538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_55538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_55538 prefixEnd_55538 := by exact prefixLift 55538
  have htrace : WordTrace (prefixWord ++ tailWord_55538) baseStart_55538 baseEnd_55538 := by
    simpa [prefixWord, tailWord_55538, baseEnd_55538] using wordTrace_append hprefix tailTrace_55538
  have hstable : (prefixWord ++ tailWord_55538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55538).length < 2 ^ (prefixWord ++ tailWord_55538).sum := by decide
  have hdescent : baseEnd_55538 < baseStart_55538 := by decide
  rcases family_descends (prefixWord ++ tailWord_55538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55569 : List Nat := [1, 2, 2, 1, 1, 7, 1, 1, 5]
def baseStart_55569 : Nat := 118140960795 + 55569 * 2 ^ 59
def prefixEnd_55569 : Nat := 4983230072969 + 3 ^ 40 * 55569 * 2
def baseEnd_55569 : Nat := 12681602884354808769755

theorem tailTrace_55569 : CollatzResearch.WordTrace tailWord_55569 prefixEnd_55569 12681602884354808769755 := by
  unfold tailWord_55569
  simp only [CollatzResearch.WordTrace]
  refine ⟨2026767935690478274737761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1351178623793652183158507 2026767935690478274737761)
  ·
    refine ⟨1520075951767858706053321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2026767935690478274737761 1520075951767858706053321)
    ·
      refine ⟨1140056963825894029539991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1520075951767858706053321 1140056963825894029539991)
      ·
        refine ⟨1710085445738841044309987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1140056963825894029539991 1710085445738841044309987)
        ·
          refine ⟨2565128168608261566464981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1710085445738841044309987 2565128168608261566464981)
          ·
            refine ⟨60120191451756130464023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 2565128168608261566464981 60120191451756130464023)
            ·
              refine ⟨90180287177634195696035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60120191451756130464023 90180287177634195696035)
              ·
                refine ⟨135270430766451293544053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90180287177634195696035 135270430766451293544053)
                ·
                  refine ⟨12681602884354808769755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135270430766451293544053 12681602884354808769755)
                  ·
                    rfl

theorem cell21_55569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 5].length) (baseStart_55569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_55569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_55569 prefixEnd_55569 := by exact prefixLift 55569
  have htrace : WordTrace (prefixWord ++ tailWord_55569) baseStart_55569 baseEnd_55569 := by
    simpa [prefixWord, tailWord_55569, baseEnd_55569] using wordTrace_append hprefix tailTrace_55569
  have hstable : (prefixWord ++ tailWord_55569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55569).length < 2 ^ (prefixWord ++ tailWord_55569).sum := by decide
  have hdescent : baseEnd_55569 < baseStart_55569 := by decide
  rcases family_descends (prefixWord ++ tailWord_55569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55617 : List Nat := [1, 2, 5, 2, 2, 1, 2, 2, 4]
def baseStart_55617 : Nat := 118140960795 + 55617 * 2 ^ 59
def prefixEnd_55617 : Nat := 4983230072969 + 3 ^ 40 * 55617 * 2
def baseEnd_55617 : Nat := 12692557138317391969657

theorem tailTrace_55617 : CollatzResearch.WordTrace tailWord_55617 prefixEnd_55617 12692557138317391969657 := by
  unfold tailWord_55617
  simp only [CollatzResearch.WordTrace]
  refine ⟨2028518639516582472485105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1352345759677721648323403 2028518639516582472485105)
  ·
    refine ⟨1521388979637436854363829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2028518639516582472485105 1521388979637436854363829)
    ·
      refine ⟨142630216841009705096609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1521388979637436854363829 142630216841009705096609)
      ·
        refine ⟨106972662630757278822457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142630216841009705096609 106972662630757278822457)
        ·
          refine ⟨80229496973067959116843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106972662630757278822457 80229496973067959116843)
          ·
            refine ⟨120344245459601938675265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80229496973067959116843 120344245459601938675265)
            ·
              refine ⟨90258184094701454006449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120344245459601938675265 90258184094701454006449)
              ·
                refine ⟨67693638071026090504837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90258184094701454006449 67693638071026090504837)
                ·
                  refine ⟨12692557138317391969657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67693638071026090504837 12692557138317391969657)
                  ·
                    rfl

theorem cell21_55617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 4].length) (baseStart_55617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_55617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_55617 prefixEnd_55617 := by exact prefixLift 55617
  have htrace : WordTrace (prefixWord ++ tailWord_55617) baseStart_55617 baseEnd_55617 := by
    simpa [prefixWord, tailWord_55617, baseEnd_55617] using wordTrace_append hprefix tailTrace_55617
  have hstable : (prefixWord ++ tailWord_55617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55617).length < 2 ^ (prefixWord ++ tailWord_55617).sum := by decide
  have hdescent : baseEnd_55617 < baseStart_55617 := by decide
  rcases family_descends (prefixWord ++ tailWord_55617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55628 : List Nat := [2, 2, 1, 3, 2, 1, 2, 3, 5]
def baseStart_55628 : Nat := 118140960795 + 55628 * 2 ^ 59
def prefixEnd_55628 : Nat := 4983230072969 + 3 ^ 40 * 55628 * 2
def baseEnd_55628 : Nat := 12695067488183817286301

theorem tailTrace_55628 : CollatzResearch.WordTrace tailWord_55628 prefixEnd_55628 12695067488183817286301 := by
  unfold tailWord_55628
  simp only [CollatzResearch.WordTrace]
  refine ⟨1014459921238365675567769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1352613228317820900757025 1014459921238365675567769)
  ·
    refine ⟨760844940928774256675827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1014459921238365675567769 760844940928774256675827)
    ·
      refine ⟨1141267411393161385013741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 760844940928774256675827 1141267411393161385013741)
      ·
        refine ⟨427975279272435519380153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1141267411393161385013741 427975279272435519380153)
        ·
          refine ⟨320981459454326639535115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427975279272435519380153 320981459454326639535115)
          ·
            refine ⟨481472189181489959302673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320981459454326639535115 481472189181489959302673)
            ·
              refine ⟨361104141886117469477005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481472189181489959302673 361104141886117469477005)
              ·
                refine ⟨135414053207294051053877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 361104141886117469477005 135414053207294051053877)
                ·
                  refine ⟨12695067488183817286301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135414053207294051053877 12695067488183817286301)
                  ·
                    rfl

theorem cell21_55628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_55628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_55628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_55628 prefixEnd_55628 := by exact prefixLift 55628
  have htrace : WordTrace (prefixWord ++ tailWord_55628) baseStart_55628 baseEnd_55628 := by
    simpa [prefixWord, tailWord_55628, baseEnd_55628] using wordTrace_append hprefix tailTrace_55628
  have hstable : (prefixWord ++ tailWord_55628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55628).length < 2 ^ (prefixWord ++ tailWord_55628).sum := by decide
  have hdescent : baseEnd_55628 < baseStart_55628 := by decide
  rcases family_descends (prefixWord ++ tailWord_55628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55642 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 8]
def baseStart_55642 : Nat := 118140960795 + 55642 * 2 ^ 59
def prefixEnd_55642 : Nat := 4983230072969 + 3 ^ 40 * 55642 * 2
def baseEnd_55642 : Nat := 12698262478922904052939

theorem tailTrace_55642 : CollatzResearch.WordTrace tailWord_55642 prefixEnd_55642 12698262478922904052939 := by
  unfold tailWord_55642
  simp only [CollatzResearch.WordTrace]
  refine ⟨507357616106502935536295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1352953642950674494763453 507357616106502935536295)
  ·
    refine ⟨761036424159754403304443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 507357616106502935536295 761036424159754403304443)
    ·
      refine ⟨1141554636239631604956665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 761036424159754403304443 1141554636239631604956665)
      ·
        refine ⟨856165977179723703717499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1141554636239631604956665 856165977179723703717499)
        ·
          refine ⟨1284248965769585555576249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 856165977179723703717499 1284248965769585555576249)
          ·
            refine ⟨963186724327189166682187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1284248965769585555576249 963186724327189166682187)
            ·
              refine ⟨1444780086490783750023281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 963186724327189166682187 1444780086490783750023281)
              ·
                refine ⟨1083585064868087812517461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1444780086490783750023281 1083585064868087812517461)
                ·
                  refine ⟨12698262478922904052939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1083585064868087812517461 12698262478922904052939)
                  ·
                    rfl

theorem cell21_55642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_55642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_55642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_55642 prefixEnd_55642 := by exact prefixLift 55642
  have htrace : WordTrace (prefixWord ++ tailWord_55642) baseStart_55642 baseEnd_55642 := by
    simpa [prefixWord, tailWord_55642, baseEnd_55642] using wordTrace_append hprefix tailTrace_55642
  have hstable : (prefixWord ++ tailWord_55642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55642).length < 2 ^ (prefixWord ++ tailWord_55642).sum := by decide
  have hdescent : baseEnd_55642 < baseStart_55642 := by decide
  rcases family_descends (prefixWord ++ tailWord_55642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55752 : List Nat := [2, 1, 3, 1, 3, 2, 4, 1, 4]
def baseStart_55752 : Nat := 118140960795 + 55752 * 2 ^ 59
def prefixEnd_55752 : Nat := 4983230072969 + 3 ^ 40 * 55752 * 2
def baseEnd_55752 : Nat := 12723365977587157219381

theorem tailTrace_55752 : CollatzResearch.WordTrace tailWord_55752 prefixEnd_55752 12723365977587157219381 := by
  unfold tailWord_55752
  simp only [CollatzResearch.WordTrace]
  refine ⟨1016721247013750264324755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1355628329351667019099673 1016721247013750264324755)
  ·
    refine ⟨1525081870520625396487133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1016721247013750264324755 1525081870520625396487133)
    ·
      refine ⟨571905701445234523682675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1525081870520625396487133 571905701445234523682675)
      ·
        refine ⟨857858552167851785524013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571905701445234523682675 857858552167851785524013)
        ·
          refine ⟨321696957062944419571505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 857858552167851785524013 321696957062944419571505)
          ·
            refine ⟨241272717797208314678629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321696957062944419571505 241272717797208314678629)
            ·
              refine ⟨45238634586976559002243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 241272717797208314678629 45238634586976559002243)
              ·
                refine ⟨67857951880464838503365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45238634586976559002243 67857951880464838503365)
                ·
                  refine ⟨12723365977587157219381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67857951880464838503365 12723365977587157219381)
                  ·
                    rfl

theorem cell21_55752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 4].length) (baseStart_55752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_55752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_55752 prefixEnd_55752 := by exact prefixLift 55752
  have htrace : WordTrace (prefixWord ++ tailWord_55752) baseStart_55752 baseEnd_55752 := by
    simpa [prefixWord, tailWord_55752, baseEnd_55752] using wordTrace_append hprefix tailTrace_55752
  have hstable : (prefixWord ++ tailWord_55752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55752).length < 2 ^ (prefixWord ++ tailWord_55752).sum := by decide
  have hdescent : baseEnd_55752 < baseStart_55752 := by decide
  rcases family_descends (prefixWord ++ tailWord_55752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55766 : List Nat := [5, 2, 1, 1, 1, 1, 1, 9]
def baseStart_55766 : Nat := 118140960795 + 55766 * 2 ^ 59
def prefixEnd_55766 : Nat := 4983230072969 + 3 ^ 40 * 55766 * 2
def baseEnd_55766 : Nat := 4242186989442081328673

theorem tailTrace_55766 : CollatzResearch.WordTrace tailWord_55766 prefixEnd_55766 4242186989442081328673 := by
  unfold tailWord_55766
  simp only [CollatzResearch.WordTrace]
  refine ⟨127122069748548807478697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1355968743984520613106101 127122069748548807478697)
  ·
    refine ⟨95341552311411605609023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127122069748548807478697 95341552311411605609023)
    ·
      refine ⟨143012328467117408413535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95341552311411605609023 143012328467117408413535)
      ·
        refine ⟨214518492700676112620303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143012328467117408413535 214518492700676112620303)
        ·
          refine ⟨321777739051014168930455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214518492700676112620303 321777739051014168930455)
          ·
            refine ⟨482666608576521253395683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321777739051014168930455 482666608576521253395683)
            ·
              refine ⟨723999912864781880093525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482666608576521253395683 723999912864781880093525)
              ·
                refine ⟨4242186989442081328673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 723999912864781880093525 4242186989442081328673)
                ·
                  rfl

theorem cell21_55766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_55766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_55766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_55766 prefixEnd_55766 := by exact prefixLift 55766
  have htrace : WordTrace (prefixWord ++ tailWord_55766) baseStart_55766 baseEnd_55766 := by
    simpa [prefixWord, tailWord_55766, baseEnd_55766] using wordTrace_append hprefix tailTrace_55766
  have hstable : (prefixWord ++ tailWord_55766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55766).length < 2 ^ (prefixWord ++ tailWord_55766).sum := by decide
  have hdescent : baseEnd_55766 < baseStart_55766 := by decide
  rcases family_descends (prefixWord ++ tailWord_55766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55831 : List Nat := [1, 1, 3, 6, 1, 1, 2, 3, 3]
def baseStart_55831 : Nat := 118140960795 + 55831 * 2 ^ 59
def prefixEnd_55831 : Nat := 4983230072969 + 3 ^ 40 * 55831 * 2
def baseEnd_55831 : Nat := 12741394853900575402553

theorem tailTrace_55831 : CollatzResearch.WordTrace tailWord_55831 prefixEnd_55831 12741394853900575402553 := by
  unfold tailWord_55831
  simp only [CollatzResearch.WordTrace]
  refine ⟨2036323860741297020775347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1357549240494198013850231 2036323860741297020775347)
  ·
    refine ⟨3054485791111945531163021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2036323860741297020775347 3054485791111945531163021)
    ·
      refine ⟨1145432171666979574186133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3054485791111945531163021 1145432171666979574186133)
      ·
        refine ⟨53692133046889667539975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1145432171666979574186133 53692133046889667539975)
        ·
          refine ⟨80538199570334501309963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53692133046889667539975 80538199570334501309963)
          ·
            refine ⟨120807299355501751964945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80538199570334501309963 120807299355501751964945)
            ·
              refine ⟨90605474516626313973709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120807299355501751964945 90605474516626313973709)
              ·
                refine ⟨33977052943734867740141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90605474516626313973709 33977052943734867740141)
                ·
                  refine ⟨12741394853900575402553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33977052943734867740141 12741394853900575402553)
                  ·
                    rfl

theorem cell21_55831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3, 3].length) (baseStart_55831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_55831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_55831 prefixEnd_55831 := by exact prefixLift 55831
  have htrace : WordTrace (prefixWord ++ tailWord_55831) baseStart_55831 baseEnd_55831 := by
    simpa [prefixWord, tailWord_55831, baseEnd_55831] using wordTrace_append hprefix tailTrace_55831
  have hstable : (prefixWord ++ tailWord_55831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55831).length < 2 ^ (prefixWord ++ tailWord_55831).sum := by decide
  have hdescent : baseEnd_55831 < baseStart_55831 := by decide
  rcases family_descends (prefixWord ++ tailWord_55831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55839 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 9]
def baseStart_55839 : Nat := 118140960795 + 55839 * 2 ^ 59
def prefixEnd_55839 : Nat := 4983230072969 + 3 ^ 40 * 55839 * 2
def baseEnd_55839 : Nat := 12743220562894339269203

theorem tailTrace_55839 : CollatzResearch.WordTrace tailWord_55839 prefixEnd_55839 12743220562894339269203 := by
  unfold tailWord_55839
  simp only [CollatzResearch.WordTrace]
  refine ⟨2036615644712314387066571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1357743763141542924711047 2036615644712314387066571)
  ·
    refine ⟨3054923467068471580599857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2036615644712314387066571 3054923467068471580599857)
    ·
      refine ⟨2291192600301353685449893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3054923467068471580599857 2291192600301353685449893)
      ·
        refine ⟨429598612556503816021855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2291192600301353685449893 429598612556503816021855)
        ·
          refine ⟨644397918834755724032783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429598612556503816021855 644397918834755724032783)
          ·
            refine ⟨966596878252133586049175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644397918834755724032783 966596878252133586049175)
            ·
              refine ⟨1449895317378200379073763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 966596878252133586049175 1449895317378200379073763)
              ·
                refine ⟨2174842976067300568610645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1449895317378200379073763 2174842976067300568610645)
                ·
                  refine ⟨12743220562894339269203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2174842976067300568610645 12743220562894339269203)
                  ·
                    rfl

theorem cell21_55839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 9].length) (baseStart_55839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_55839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_55839 prefixEnd_55839 := by exact prefixLift 55839
  have htrace : WordTrace (prefixWord ++ tailWord_55839) baseStart_55839 baseEnd_55839 := by
    simpa [prefixWord, tailWord_55839, baseEnd_55839] using wordTrace_append hprefix tailTrace_55839
  have hstable : (prefixWord ++ tailWord_55839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55839).length < 2 ^ (prefixWord ++ tailWord_55839).sum := by decide
  have hdescent : baseEnd_55839 < baseStart_55839 := by decide
  rcases family_descends (prefixWord ++ tailWord_55839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55876 : List Nat := [2, 3, 5, 1, 1, 1, 1, 7]
def baseStart_55876 : Nat := 118140960795 + 55876 * 2 ^ 59
def prefixEnd_55876 : Nat := 4983230072969 + 3 ^ 40 * 55876 * 2
def baseEnd_55876 : Nat := 4250554822330165717487

theorem tailTrace_55876 : CollatzResearch.WordTrace tailWord_55876 prefixEnd_55876 4250554822330165717487 := by
  unfold tailWord_55876
  simp only [CollatzResearch.WordTrace]
  refine ⟨1018982572789134853081741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1358643430385513137442321 1018982572789134853081741)
  ·
    refine ⟨382118464795925569905653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1018982572789134853081741 382118464795925569905653)
    ·
      refine ⟨35823606074618022178655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 382118464795925569905653 35823606074618022178655)
      ·
        refine ⟨53735409111927033267983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35823606074618022178655 53735409111927033267983)
        ·
          refine ⟨80603113667890549901975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53735409111927033267983 80603113667890549901975)
          ·
            refine ⟨120904670501835824852963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80603113667890549901975 120904670501835824852963)
            ·
              refine ⟨181357005752753737279445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120904670501835824852963 181357005752753737279445)
              ·
                refine ⟨4250554822330165717487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 181357005752753737279445 4250554822330165717487)
                ·
                  rfl

theorem cell21_55876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 7].length) (baseStart_55876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_55876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_55876 prefixEnd_55876 := by exact prefixLift 55876
  have htrace : WordTrace (prefixWord ++ tailWord_55876) baseStart_55876 baseEnd_55876 := by
    simpa [prefixWord, tailWord_55876, baseEnd_55876] using wordTrace_append hprefix tailTrace_55876
  have hstable : (prefixWord ++ tailWord_55876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55876).length < 2 ^ (prefixWord ++ tailWord_55876).sum := by decide
  have hdescent : baseEnd_55876 < baseStart_55876 := by decide
  rcases family_descends (prefixWord ++ tailWord_55876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55915 : List Nat := [1, 1, 1, 1, 2, 2, 1, 7, 5]
def baseStart_55915 : Nat := 118140960795 + 55915 * 2 ^ 59
def prefixEnd_55915 : Nat := 4983230072969 + 3 ^ 40 * 55915 * 2
def baseEnd_55915 : Nat := 12760564798335096002381

theorem tailTrace_55915 : CollatzResearch.WordTrace tailWord_55915 prefixEnd_55915 12760564798335096002381 := by
  unfold tailWord_55915
  simp only [CollatzResearch.WordTrace]
  refine ⟨2039387592436979366833199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1359591728291319577888799 2039387592436979366833199)
  ·
    refine ⟨3059081388655469050249799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2039387592436979366833199 3059081388655469050249799)
    ·
      refine ⟨4588622082983203575374699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3059081388655469050249799 4588622082983203575374699)
      ·
        refine ⟨6882933124474805363062049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4588622082983203575374699 6882933124474805363062049)
        ·
          refine ⟨5162199843356104022296537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6882933124474805363062049 5162199843356104022296537)
          ·
            refine ⟨3871649882517078016722403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5162199843356104022296537 3871649882517078016722403)
            ·
              refine ⟨5807474823775617025083605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3871649882517078016722403 5807474823775617025083605)
              ·
                refine ⟨136112691182241024025397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5807474823775617025083605 136112691182241024025397)
                ·
                  refine ⟨12760564798335096002381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136112691182241024025397 12760564798335096002381)
                  ·
                    rfl

theorem cell21_55915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 5].length) (baseStart_55915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_55915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_55915 prefixEnd_55915 := by exact prefixLift 55915
  have htrace : WordTrace (prefixWord ++ tailWord_55915) baseStart_55915 baseEnd_55915 := by
    simpa [prefixWord, tailWord_55915, baseEnd_55915] using wordTrace_append hprefix tailTrace_55915
  have hstable : (prefixWord ++ tailWord_55915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55915).length < 2 ^ (prefixWord ++ tailWord_55915).sum := by decide
  have hdescent : baseEnd_55915 < baseStart_55915 := by decide
  rcases family_descends (prefixWord ++ tailWord_55915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55918 : List Nat := [4, 1, 2, 2, 2, 2, 2, 6]
def baseStart_55918 : Nat := 118140960795 + 55918 * 2 ^ 59
def prefixEnd_55918 : Nat := 4983230072969 + 3 ^ 40 * 55918 * 2
def baseEnd_55918 : Nat := 4253749813069252484125

theorem tailTrace_55918 : CollatzResearch.WordTrace tailWord_55918 prefixEnd_55918 4253749813069252484125 := by
  unfold tailWord_55918
  simp only [CollatzResearch.WordTrace]
  refine ⟨254937126428263859899051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1359664674284073919461605 254937126428263859899051)
  ·
    refine ⟨382405689642395789848577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254937126428263859899051 382405689642395789848577)
    ·
      refine ⟨286804267231796842386433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382405689642395789848577 286804267231796842386433)
      ·
        refine ⟨215103200423847631789825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286804267231796842386433 215103200423847631789825)
        ·
          refine ⟨161327400317885723842369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215103200423847631789825 161327400317885723842369)
          ·
            refine ⟨120995550238414292881777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161327400317885723842369 120995550238414292881777)
            ·
              refine ⟨90746662678810719661333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120995550238414292881777 90746662678810719661333)
              ·
                refine ⟨4253749813069252484125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90746662678810719661333 4253749813069252484125)
                ·
                  rfl

theorem cell21_55918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_55918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_55918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_55918 prefixEnd_55918 := by exact prefixLift 55918
  have htrace : WordTrace (prefixWord ++ tailWord_55918) baseStart_55918 baseEnd_55918 := by
    simpa [prefixWord, tailWord_55918, baseEnd_55918] using wordTrace_append hprefix tailTrace_55918
  have hstable : (prefixWord ++ tailWord_55918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55918).length < 2 ^ (prefixWord ++ tailWord_55918).sum := by decide
  have hdescent : baseEnd_55918 < baseStart_55918 := by decide
  rcases family_descends (prefixWord ++ tailWord_55918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55966 : List Nat := [4, 3, 1, 1, 1, 1, 3, 4, 3]
def baseStart_55966 : Nat := 118140960795 + 55966 * 2 ^ 59
def prefixEnd_55966 : Nat := 4983230072969 + 3 ^ 40 * 55966 * 2
def baseEnd_55966 : Nat := 12772203693170340652277

theorem tailTrace_55966 : CollatzResearch.WordTrace tailWord_55966 prefixEnd_55966 12772203693170340652277 := by
  unfold tailWord_55966
  simp only [CollatzResearch.WordTrace]
  refine ⟨255155964406526884617469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1360831810168143384626501 255155964406526884617469)
  ·
    refine ⟨95683486652447581731551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255155964406526884617469 95683486652447581731551)
    ·
      refine ⟨143525229978671372597327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95683486652447581731551 143525229978671372597327)
      ·
        refine ⟨215287844968007058895991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143525229978671372597327 215287844968007058895991)
        ·
          refine ⟨322931767452010588343987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215287844968007058895991 322931767452010588343987)
          ·
            refine ⟨484397651178015882515981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322931767452010588343987 484397651178015882515981)
            ·
              refine ⟨181649119191755955943493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 484397651178015882515981 181649119191755955943493)
              ·
                refine ⟨34059209848454241739405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181649119191755955943493 34059209848454241739405)
                ·
                  refine ⟨12772203693170340652277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34059209848454241739405 12772203693170340652277)
                  ·
                    rfl

theorem cell21_55966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_55966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_55966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_55966 prefixEnd_55966 := by exact prefixLift 55966
  have htrace : WordTrace (prefixWord ++ tailWord_55966) baseStart_55966 baseEnd_55966 := by
    simpa [prefixWord, tailWord_55966, baseEnd_55966] using wordTrace_append hprefix tailTrace_55966
  have hstable : (prefixWord ++ tailWord_55966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55966).length < 2 ^ (prefixWord ++ tailWord_55966).sum := by decide
  have hdescent : baseEnd_55966 < baseStart_55966 := by decide
  rcases family_descends (prefixWord ++ tailWord_55966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56129 : List Nat := [1, 2, 5, 3, 10]
def baseStart_56129 : Nat := 118140960795 + 56129 * 2 ^ 59
def prefixEnd_56129 : Nat := 4983230072969 + 3 ^ 40 * 56129 * 2
def baseEnd_56129 : Nat := 158140771776768881917

theorem tailTrace_56129 : CollatzResearch.WordTrace tailWord_56129 prefixEnd_56129 158140771776768881917 := by
  unfold tailWord_56129
  simp only [CollatzResearch.WordTrace]
  refine ⟨2047192813661693915123441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1364795209107795943415627 2047192813661693915123441)
  ·
    refine ⟨1535394610246270436342581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2047192813661693915123441 1535394610246270436342581)
    ·
      refine ⟨143943244710587853407117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1535394610246270436342581 143943244710587853407117)
      ·
        refine ⟨53978716766470445027669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143943244710587853407117 53978716766470445027669)
        ·
          refine ⟨158140771776768881917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 53978716766470445027669 158140771776768881917)
          ·
            rfl

theorem cell21_56129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 10].length) (baseStart_56129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_56129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_56129 prefixEnd_56129 := by exact prefixLift 56129
  have htrace : WordTrace (prefixWord ++ tailWord_56129) baseStart_56129 baseEnd_56129 := by
    simpa [prefixWord, tailWord_56129, baseEnd_56129] using wordTrace_append hprefix tailTrace_56129
  have hstable : (prefixWord ++ tailWord_56129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56129).length < 2 ^ (prefixWord ++ tailWord_56129).sum := by decide
  have hdescent : baseEnd_56129 < baseStart_56129 := by decide
  rcases family_descends (prefixWord ++ tailWord_56129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56177 : List Nat := [1, 2, 2, 2, 1, 5, 2, 3, 3]
def baseStart_56177 : Nat := 118140960795 + 56177 * 2 ^ 59
def prefixEnd_56177 : Nat := 4983230072969 + 3 ^ 40 * 56177 * 2
def baseEnd_56177 : Nat := 12820356767880862635179

theorem tailTrace_56177 : CollatzResearch.WordTrace tailWord_56177 prefixEnd_56177 12820356767880862635179 := by
  unfold tailWord_56177
  simp only [CollatzResearch.WordTrace]
  refine ⟨2048943517487798112870785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1365962344991865408580523 2048943517487798112870785)
  ·
    refine ⟨1536707638115848584653089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2048943517487798112870785 1536707638115848584653089)
    ·
      refine ⟨1152530728586886438489817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1536707638115848584653089 1152530728586886438489817)
      ·
        refine ⟨864398046440164828867363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1152530728586886438489817 864398046440164828867363)
        ·
          refine ⟨1296597069660247243301045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 864398046440164828867363 1296597069660247243301045)
          ·
            refine ⟨121555975280648179059473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1296597069660247243301045 121555975280648179059473)
            ·
              refine ⟨91166981460486134294605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121555975280648179059473 91166981460486134294605)
              ·
                refine ⟨34187618047682300360477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91166981460486134294605 34187618047682300360477)
                ·
                  refine ⟨12820356767880862635179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34187618047682300360477 12820356767880862635179)
                  ·
                    rfl

theorem cell21_56177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3, 3].length) (baseStart_56177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_56177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_56177 prefixEnd_56177 := by exact prefixLift 56177
  have htrace : WordTrace (prefixWord ++ tailWord_56177) baseStart_56177 baseEnd_56177 := by
    simpa [prefixWord, tailWord_56177, baseEnd_56177] using wordTrace_append hprefix tailTrace_56177
  have hstable : (prefixWord ++ tailWord_56177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56177).length < 2 ^ (prefixWord ++ tailWord_56177).sum := by decide
  have hdescent : baseEnd_56177 < baseStart_56177 := by decide
  rcases family_descends (prefixWord ++ tailWord_56177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56233 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 8]
def baseStart_56233 : Nat := 118140960795 + 56233 * 2 ^ 59
def prefixEnd_56233 : Nat := 4983230072969 + 3 ^ 40 * 56233 * 2
def baseEnd_56233 : Nat := 12833136730837209701731

theorem tailTrace_56233 : CollatzResearch.WordTrace tailWord_56233 prefixEnd_56233 12833136730837209701731 := by
  unfold tailWord_56233
  simp only [CollatzResearch.WordTrace]
  refine ⟨2050986005284919676909353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1367324003523279784606235 2050986005284919676909353)
  ·
    refine ⟨1538239503963689757682015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2050986005284919676909353 1538239503963689757682015)
    ·
      refine ⟨2307359255945534636523023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1538239503963689757682015 2307359255945534636523023)
      ·
        refine ⟨3461038883918301954784535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2307359255945534636523023 3461038883918301954784535)
        ·
          refine ⟨5191558325877452932176803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3461038883918301954784535 5191558325877452932176803)
          ·
            refine ⟨7787337488816179398265205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5191558325877452932176803 7787337488816179398265205)
            ·
              refine ⟨730062889576516818587363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7787337488816179398265205 730062889576516818587363)
              ·
                refine ⟨1095094334364775227881045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 730062889576516818587363 1095094334364775227881045)
                ·
                  refine ⟨12833136730837209701731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1095094334364775227881045 12833136730837209701731)
                  ·
                    rfl

theorem cell21_56233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 8].length) (baseStart_56233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_56233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_56233 prefixEnd_56233 := by exact prefixLift 56233
  have htrace : WordTrace (prefixWord ++ tailWord_56233) baseStart_56233 baseEnd_56233 := by
    simpa [prefixWord, tailWord_56233, baseEnd_56233] using wordTrace_append hprefix tailTrace_56233
  have hstable : (prefixWord ++ tailWord_56233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56233).length < 2 ^ (prefixWord ++ tailWord_56233).sum := by decide
  have hdescent : baseEnd_56233 < baseStart_56233 := by decide
  rcases family_descends (prefixWord ++ tailWord_56233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56250 : List Nat := [3, 1, 1, 1, 2, 1, 4, 4, 4]
def baseStart_56250 : Nat := 118140960795 + 56250 * 2 ^ 59
def prefixEnd_56250 : Nat := 4983230072969 + 3 ^ 40 * 56250 * 2
def baseEnd_56250 : Nat := 12837016362448957918363

theorem tailTrace_56250 : CollatzResearch.WordTrace tailWord_56250 prefixEnd_56250 12837016362448957918363 := by
  unfold tailWord_56250
  simp only [CollatzResearch.WordTrace]
  refine ⟨512901511555832895069551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1367737364148887720185469 512901511555832895069551)
  ·
    refine ⟨769352267333749342604327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 512901511555832895069551 769352267333749342604327)
    ·
      refine ⟨1154028401000624013906491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 769352267333749342604327 1154028401000624013906491)
      ·
        refine ⟨1731042601500936020859737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1154028401000624013906491 1731042601500936020859737)
        ·
          refine ⟨1298281951125702015644803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1731042601500936020859737 1298281951125702015644803)
          ·
            refine ⟨1947422926688553023467205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1298281951125702015644803 1947422926688553023467205)
            ·
              refine ⟨365141798754103691900101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1947422926688553023467205 365141798754103691900101)
              ·
                refine ⟨68464087266394442231269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 365141798754103691900101 68464087266394442231269)
                ·
                  refine ⟨12837016362448957918363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68464087266394442231269 12837016362448957918363)
                  ·
                    rfl

theorem cell21_56250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_56250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_56250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_56250 prefixEnd_56250 := by exact prefixLift 56250
  have htrace : WordTrace (prefixWord ++ tailWord_56250) baseStart_56250 baseEnd_56250 := by
    simpa [prefixWord, tailWord_56250, baseEnd_56250] using wordTrace_append hprefix tailTrace_56250
  have hstable : (prefixWord ++ tailWord_56250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56250).length < 2 ^ (prefixWord ++ tailWord_56250).sum := by decide
  have hdescent : baseEnd_56250 < baseStart_56250 := by decide
  rcases family_descends (prefixWord ++ tailWord_56250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56253 : List Nat := [1, 4, 1, 2, 4, 2, 1, 1, 5]
def baseStart_56253 : Nat := 118140960795 + 56253 * 2 ^ 59
def prefixEnd_56253 : Nat := 4983230072969 + 3 ^ 40 * 56253 * 2
def baseEnd_56253 : Nat := 12837701003321619368357

theorem tailTrace_56253 : CollatzResearch.WordTrace tailWord_56253 prefixEnd_56253 12837701003321619368357 := by
  unfold tailWord_56253
  simp only [CollatzResearch.WordTrace]
  refine ⟨2051715465212463092637413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1367810310141642061758275 2051715465212463092637413)
  ·
    refine ⟨384696649727336829869515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2051715465212463092637413 384696649727336829869515)
    ·
      refine ⟨577044974591005244804273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384696649727336829869515 577044974591005244804273)
      ·
        refine ⟨432783730943253933603205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577044974591005244804273 432783730943253933603205)
        ·
          refine ⟨81146949551860112550601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 432783730943253933603205 81146949551860112550601)
          ·
            refine ⟨60860212163895084412951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81146949551860112550601 60860212163895084412951)
            ·
              refine ⟨91290318245842626619427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60860212163895084412951 91290318245842626619427)
              ·
                refine ⟨136935477368763939929141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91290318245842626619427 136935477368763939929141)
                ·
                  refine ⟨12837701003321619368357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136935477368763939929141 12837701003321619368357)
                  ·
                    rfl

theorem cell21_56253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_56253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_56253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_56253 prefixEnd_56253 := by exact prefixLift 56253
  have htrace : WordTrace (prefixWord ++ tailWord_56253) baseStart_56253 baseEnd_56253 := by
    simpa [prefixWord, tailWord_56253, baseEnd_56253] using wordTrace_append hprefix tailTrace_56253
  have hstable : (prefixWord ++ tailWord_56253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56253).length < 2 ^ (prefixWord ++ tailWord_56253).sum := by decide
  have hdescent : baseEnd_56253 < baseStart_56253 := by decide
  rcases family_descends (prefixWord ++ tailWord_56253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56267 : List Nat := [1, 1, 1, 1, 3, 5, 4, 1, 4]
def baseStart_56267 : Nat := 118140960795 + 56267 * 2 ^ 59
def prefixEnd_56267 : Nat := 4983230072969 + 3 ^ 40 * 56267 * 2
def baseEnd_56267 : Nat := 12840895994060706134995

theorem tailTrace_56267 : CollatzResearch.WordTrace tailWord_56267 prefixEnd_56267 12840895994060706134995 := by
  unfold tailWord_56267
  simp only [CollatzResearch.WordTrace]
  refine ⟨2052226087161743483647055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1368150724774495655764703 2052226087161743483647055)
  ·
    refine ⟨3078339130742615225470583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2052226087161743483647055 3078339130742615225470583)
    ·
      refine ⟨4617508696113922838205875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3078339130742615225470583 4617508696113922838205875)
      ·
        refine ⟨6926263044170884257308813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4617508696113922838205875 6926263044170884257308813)
        ·
          refine ⟨2597348641564081596490805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6926263044170884257308813 2597348641564081596490805)
          ·
            refine ⟨243501435146632649671013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2597348641564081596490805 243501435146632649671013)
            ·
              refine ⟨45656519089993621813315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 243501435146632649671013 45656519089993621813315)
              ·
                refine ⟨68484778634990432719973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45656519089993621813315 68484778634990432719973)
                ·
                  refine ⟨12840895994060706134995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68484778634990432719973 12840895994060706134995)
                  ·
                    rfl

theorem cell21_56267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 4].length) (baseStart_56267 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_56267 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_56267 prefixEnd_56267 := by exact prefixLift 56267
  have htrace : WordTrace (prefixWord ++ tailWord_56267) baseStart_56267 baseEnd_56267 := by
    simpa [prefixWord, tailWord_56267, baseEnd_56267] using wordTrace_append hprefix tailTrace_56267
  have hstable : (prefixWord ++ tailWord_56267).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56267).length < 2 ^ (prefixWord ++ tailWord_56267).sum := by decide
  have hdescent : baseEnd_56267 < baseStart_56267 := by decide
  rcases family_descends (prefixWord ++ tailWord_56267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56402 : List Nat := [3, 2, 2, 1, 3, 1, 1, 2, 6]
def baseStart_56402 : Nat := 118140960795 + 56402 * 2 ^ 59
def prefixEnd_56402 : Nat := 4983230072969 + 3 ^ 40 * 56402 * 2
def baseEnd_56402 : Nat := 12871704833330471384719

theorem tailTrace_56402 : CollatzResearch.WordTrace tailWord_56402 prefixEnd_56402 12871704833330471384719 := by
  unfold tailWord_56402
  simp only [CollatzResearch.WordTrace]
  refine ⟨514287485418165384952865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1371433294448441026540973 514287485418165384952865)
  ·
    refine ⟨385715614063624038714649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 514287485418165384952865 385715614063624038714649)
    ·
      refine ⟨289286710547718029035987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385715614063624038714649 289286710547718029035987)
      ·
        refine ⟨433930065821577043553981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289286710547718029035987 433930065821577043553981)
        ·
          refine ⟨162723774683091391332743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 433930065821577043553981 162723774683091391332743)
          ·
            refine ⟨244085662024637086999115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162723774683091391332743 244085662024637086999115)
            ·
              refine ⟨366128493036955630498673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244085662024637086999115 366128493036955630498673)
              ·
                refine ⟨274596369777716722874005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366128493036955630498673 274596369777716722874005)
                ·
                  refine ⟨12871704833330471384719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 274596369777716722874005 12871704833330471384719)
                  ·
                    rfl

theorem cell21_56402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_56402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_56402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_56402 prefixEnd_56402 := by exact prefixLift 56402
  have htrace : WordTrace (prefixWord ++ tailWord_56402) baseStart_56402 baseEnd_56402 := by
    simpa [prefixWord, tailWord_56402, baseEnd_56402] using wordTrace_append hprefix tailTrace_56402
  have hstable : (prefixWord ++ tailWord_56402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56402).length < 2 ^ (prefixWord ++ tailWord_56402).sum := by decide
  have hdescent : baseEnd_56402 < baseStart_56402 := by decide
  rcases family_descends (prefixWord ++ tailWord_56402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56574 : List Nat := [4, 2, 2, 1, 1, 4, 1, 3, 3]
def baseStart_56574 : Nat := 118140960795 + 56574 * 2 ^ 59
def prefixEnd_56574 : Nat := 4983230072969 + 3 ^ 40 * 56574 * 2
def baseEnd_56574 : Nat := 12910957576696394517701

theorem tailTrace_56574 : CollatzResearch.WordTrace tailWord_56574 prefixEnd_56574 12910957576696394517701 := by
  unfold tailWord_56574
  simp only [CollatzResearch.WordTrace]
  refine ⟨257927912131191864384097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1375615531366356610048517 257927912131191864384097)
  ·
    refine ⟨193445934098393898288073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257927912131191864384097 193445934098393898288073)
    ·
      refine ⟨145084450573795423716055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193445934098393898288073 145084450573795423716055)
      ·
        refine ⟨217626675860693135574083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145084450573795423716055 217626675860693135574083)
        ·
          refine ⟨326440013791039703361125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217626675860693135574083 326440013791039703361125)
          ·
            refine ⟨61207502585819944380211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 326440013791039703361125 61207502585819944380211)
            ·
              refine ⟨91811253878729916570317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61207502585819944380211 91811253878729916570317)
              ·
                refine ⟨34429220204523718713869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91811253878729916570317 34429220204523718713869)
                ·
                  refine ⟨12910957576696394517701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34429220204523718713869 12910957576696394517701)
                  ·
                    rfl

theorem cell21_56574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_56574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_56574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_56574 prefixEnd_56574 := by exact prefixLift 56574
  have htrace : WordTrace (prefixWord ++ tailWord_56574) baseStart_56574 baseEnd_56574 := by
    simpa [prefixWord, tailWord_56574, baseEnd_56574] using wordTrace_append hprefix tailTrace_56574
  have hstable : (prefixWord ++ tailWord_56574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56574).length < 2 ^ (prefixWord ++ tailWord_56574).sum := by decide
  have hdescent : baseEnd_56574 < baseStart_56574 := by decide
  rcases family_descends (prefixWord ++ tailWord_56574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56661 : List Nat := [1, 3, 2, 2, 3, 3, 1, 6]
def baseStart_56661 : Nat := 118140960795 + 56661 * 2 ^ 59
def prefixEnd_56661 : Nat := 4983230072969 + 3 ^ 40 * 56661 * 2
def baseEnd_56661 : Nat := 4310270720667858855841

theorem tailTrace_56661 : CollatzResearch.WordTrace tailWord_56661 prefixEnd_56661 4310270720667858855841 := by
  unfold tailWord_56661
  simp only [CollatzResearch.WordTrace]
  refine ⟨2066596447734348773489837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1377730965156232515659891 2066596447734348773489837)
  ·
    refine ⟨774973667900380790058689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2066596447734348773489837 774973667900380790058689)
    ·
      refine ⟨581230250925285592544017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 774973667900380790058689 581230250925285592544017)
      ·
        refine ⟨435922688193964194408013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 581230250925285592544017 435922688193964194408013)
        ·
          refine ⟨163471008072736572903005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 435922688193964194408013 163471008072736572903005)
          ·
            refine ⟨61301628027276214838627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163471008072736572903005 61301628027276214838627)
            ·
              refine ⟨91952442040914322257941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61301628027276214838627 91952442040914322257941)
              ·
                refine ⟨4310270720667858855841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91952442040914322257941 4310270720667858855841)
                ·
                  rfl

theorem cell21_56661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 6].length) (baseStart_56661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_56661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_56661 prefixEnd_56661 := by exact prefixLift 56661
  have htrace : WordTrace (prefixWord ++ tailWord_56661) baseStart_56661 baseEnd_56661 := by
    simpa [prefixWord, tailWord_56661, baseEnd_56661] using wordTrace_append hprefix tailTrace_56661
  have hstable : (prefixWord ++ tailWord_56661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56661).length < 2 ^ (prefixWord ++ tailWord_56661).sum := by decide
  have hdescent : baseEnd_56661 < baseStart_56661 := by decide
  rcases family_descends (prefixWord ++ tailWord_56661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56675 : List Nat := [1, 1, 1, 5, 2, 3, 1, 2, 5]
def baseStart_56675 : Nat := 118140960795 + 56675 * 2 ^ 59
def prefixEnd_56675 : Nat := 4983230072969 + 3 ^ 40 * 56675 * 2
def baseEnd_56675 : Nat := 12934007152742663334161

theorem tailTrace_56675 : CollatzResearch.WordTrace tailWord_56675 prefixEnd_56675 12934007152742663334161 := by
  unfold tailWord_56675
  simp only [CollatzResearch.WordTrace]
  refine ⟨2067107069683629164499479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1378071379789086109666319 2067107069683629164499479)
  ·
    refine ⟨3100660604525443746749219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2067107069683629164499479 3100660604525443746749219)
    ·
      refine ⟨4650990906788165620123829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3100660604525443746749219 4650990906788165620123829)
      ·
        refine ⟨436030397511390526886609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4650990906788165620123829 436030397511390526886609)
        ·
          refine ⟨327022798133542895164957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436030397511390526886609 327022798133542895164957)
          ·
            refine ⟨122633549300078585686859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327022798133542895164957 122633549300078585686859)
            ·
              refine ⟨183950323950117878530289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122633549300078585686859 183950323950117878530289)
              ·
                refine ⟨137962742962588408897717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183950323950117878530289 137962742962588408897717)
                ·
                  refine ⟨12934007152742663334161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137962742962588408897717 12934007152742663334161)
                  ·
                    rfl

theorem cell21_56675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 5].length) (baseStart_56675 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_56675 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_56675 prefixEnd_56675 := by exact prefixLift 56675
  have htrace : WordTrace (prefixWord ++ tailWord_56675) baseStart_56675 baseEnd_56675 := by
    simpa [prefixWord, tailWord_56675, baseEnd_56675] using wordTrace_append hprefix tailTrace_56675
  have hstable : (prefixWord ++ tailWord_56675).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56675).length < 2 ^ (prefixWord ++ tailWord_56675).sum := by decide
  have hdescent : baseEnd_56675 < baseStart_56675 := by decide
  rcases family_descends (prefixWord ++ tailWord_56675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56765 : List Nat := [1, 4, 1, 2, 2, 1, 1, 3, 6]
def baseStart_56765 : Nat := 118140960795 + 56765 * 2 ^ 59
def prefixEnd_56765 : Nat := 4983230072969 + 3 ^ 40 * 56765 * 2
def baseEnd_56765 : Nat := 12954546378922506833977

theorem tailTrace_56765 : CollatzResearch.WordTrace tailWord_56765 prefixEnd_56765 12954546378922506833977 := by
  unfold tailWord_56765
  simp only [CollatzResearch.WordTrace]
  refine ⟨2070389639357574535275749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1380259759571716356850499 2070389639357574535275749)
  ·
    refine ⟨388198057379545225364203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2070389639357574535275749 388198057379545225364203)
    ·
      refine ⟨582297086069317838046305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388198057379545225364203 582297086069317838046305)
      ·
        refine ⟨436722814551988378534729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 582297086069317838046305 436722814551988378534729)
        ·
          refine ⟨327542110913991283901047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436722814551988378534729 327542110913991283901047)
          ·
            refine ⟨491313166370986925851571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327542110913991283901047 491313166370986925851571)
            ·
              refine ⟨736969749556480388777357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491313166370986925851571 736969749556480388777357)
              ·
                refine ⟨276363656083680145791509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 736969749556480388777357 276363656083680145791509)
                ·
                  refine ⟨12954546378922506833977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 276363656083680145791509 12954546378922506833977)
                  ·
                    rfl

theorem cell21_56765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_56765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_56765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_56765 prefixEnd_56765 := by exact prefixLift 56765
  have htrace : WordTrace (prefixWord ++ tailWord_56765) baseStart_56765 baseEnd_56765 := by
    simpa [prefixWord, tailWord_56765, baseEnd_56765] using wordTrace_append hprefix tailTrace_56765
  have hstable : (prefixWord ++ tailWord_56765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56765).length < 2 ^ (prefixWord ++ tailWord_56765).sum := by decide
  have hdescent : baseEnd_56765 < baseStart_56765 := by decide
  rcases family_descends (prefixWord ++ tailWord_56765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56779 : List Nat := [1, 1, 1, 1, 3, 3, 3, 8]
def baseStart_56779 : Nat := 118140960795 + 56779 * 2 ^ 59
def prefixEnd_56779 : Nat := 4983230072969 + 3 ^ 40 * 56779 * 2
def baseEnd_56779 : Nat := 4319247123220531200205

theorem tailTrace_56779 : CollatzResearch.WordTrace tailWord_56779 prefixEnd_56779 4319247123220531200205 := by
  unfold tailWord_56779
  simp only [CollatzResearch.WordTrace]
  refine ⟨2070900261306854926285391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1380600174204569950856927 2070900261306854926285391)
  ·
    refine ⟨3106350391960282389428087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2070900261306854926285391 3106350391960282389428087)
    ·
      refine ⟨4659525587940423584142131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3106350391960282389428087 4659525587940423584142131)
      ·
        refine ⟨6989288381910635376213197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4659525587940423584142131 6989288381910635376213197)
        ·
          refine ⟨2620983143216488266079949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6989288381910635376213197 2620983143216488266079949)
          ·
            refine ⟨982868678706183099779981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2620983143216488266079949 982868678706183099779981)
            ·
              refine ⟨368575754514818662417493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 982868678706183099779981 368575754514818662417493)
              ·
                refine ⟨4319247123220531200205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 368575754514818662417493 4319247123220531200205)
                ·
                  rfl

theorem cell21_56779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 8].length) (baseStart_56779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_56779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_56779 prefixEnd_56779 := by exact prefixLift 56779
  have htrace : WordTrace (prefixWord ++ tailWord_56779) baseStart_56779 baseEnd_56779 := by
    simpa [prefixWord, tailWord_56779, baseEnd_56779] using wordTrace_append hprefix tailTrace_56779
  have hstable : (prefixWord ++ tailWord_56779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56779).length < 2 ^ (prefixWord ++ tailWord_56779).sum := by decide
  have hdescent : baseEnd_56779 < baseStart_56779 := by decide
  rcases family_descends (prefixWord ++ tailWord_56779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56813 : List Nat := [1, 5, 1, 3, 3, 8]
def baseStart_56813 : Nat := 118140960795 + 56813 * 2 ^ 59
def prefixEnd_56813 : Nat := 4983230072969 + 3 ^ 40 * 56813 * 2
def baseEnd_56813 : Nat := 480203727143892223477

theorem tailTrace_56813 : CollatzResearch.WordTrace tailWord_56813 prefixEnd_56813 480203727143892223477 := by
  unfold tailWord_56813
  simp only [CollatzResearch.WordTrace]
  refine ⟨2072140343183678733023093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1381426895455785822015395 2072140343183678733023093)
  ·
    refine ⟨194263157173469881220915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2072140343183678733023093 194263157173469881220915)
    ·
      refine ⟨291394735760204821831373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194263157173469881220915 291394735760204821831373)
      ·
        refine ⟨109273025910076808186765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291394735760204821831373 109273025910076808186765)
        ·
          refine ⟨40977384716278803070037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109273025910076808186765 40977384716278803070037)
          ·
            refine ⟨480203727143892223477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 40977384716278803070037 480203727143892223477)
            ·
              rfl

theorem cell21_56813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 8].length) (baseStart_56813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_56813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_56813 prefixEnd_56813 := by exact prefixLift 56813
  have htrace : WordTrace (prefixWord ++ tailWord_56813) baseStart_56813 baseEnd_56813 := by
    simpa [prefixWord, tailWord_56813, baseEnd_56813] using wordTrace_append hprefix tailTrace_56813
  have hstable : (prefixWord ++ tailWord_56813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56813).length < 2 ^ (prefixWord ++ tailWord_56813).sum := by decide
  have hdescent : baseEnd_56813 < baseStart_56813 := by decide
  rcases family_descends (prefixWord ++ tailWord_56813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56827 : List Nat := [1, 1, 1, 1, 1, 3, 2, 8, 3]
def baseStart_56827 : Nat := 118140960795 + 56827 * 2 ^ 59
def prefixEnd_56827 : Nat := 4983230072969 + 3 ^ 40 * 56827 * 2
def baseEnd_56827 : Nat := 12968695623624176800517

theorem tailTrace_56827 : CollatzResearch.WordTrace tailWord_56827 prefixEnd_56827 12968695623624176800517 := by
  unfold tailWord_56827
  simp only [CollatzResearch.WordTrace]
  refine ⟨2072650965132959124032735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1381767310088639416021823 2072650965132959124032735)
  ·
    refine ⟨3108976447699438686049103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2072650965132959124032735 3108976447699438686049103)
    ·
      refine ⟨4663464671549158029073655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3108976447699438686049103 4663464671549158029073655)
      ·
        refine ⟨6995197007323737043610483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4663464671549158029073655 6995197007323737043610483)
        ·
          refine ⟨10492795510985605565415725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6995197007323737043610483 10492795510985605565415725)
          ·
            refine ⟨3934798316619602087030897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10492795510985605565415725 3934798316619602087030897)
            ·
              refine ⟨2951098737464701565273173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3934798316619602087030897 2951098737464701565273173)
              ·
                refine ⟨34583188329664471468045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2951098737464701565273173 34583188329664471468045)
                ·
                  refine ⟨12968695623624176800517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34583188329664471468045 12968695623624176800517)
                  ·
                    rfl

theorem cell21_56827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8, 3].length) (baseStart_56827 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_56827 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_56827 prefixEnd_56827 := by exact prefixLift 56827
  have htrace : WordTrace (prefixWord ++ tailWord_56827) baseStart_56827 baseEnd_56827 := by
    simpa [prefixWord, tailWord_56827, baseEnd_56827] using wordTrace_append hprefix tailTrace_56827
  have hstable : (prefixWord ++ tailWord_56827).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56827).length < 2 ^ (prefixWord ++ tailWord_56827).sum := by decide
  have hdescent : baseEnd_56827 < baseStart_56827 := by decide
  rcases family_descends (prefixWord ++ tailWord_56827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56841 : List Nat := [1, 2, 1, 1, 3, 1, 3, 5, 4]
def baseStart_56841 : Nat := 118140960795 + 56841 * 2 ^ 59
def prefixEnd_56841 : Nat := 4983230072969 + 3 ^ 40 * 56841 * 2
def baseEnd_56841 : Nat := 12971890614363263567155

theorem tailTrace_56841 : CollatzResearch.WordTrace tailWord_56841 prefixEnd_56841 12971890614363263567155 := by
  unfold tailWord_56841
  simp only [CollatzResearch.WordTrace]
  refine ⟨2073161587082239515042377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1382107724721493010028251 2073161587082239515042377)
  ·
    refine ⟨1554871190311679636281783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2073161587082239515042377 1554871190311679636281783)
    ·
      refine ⟨2332306785467519454422675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1554871190311679636281783 2332306785467519454422675)
      ·
        refine ⟨3498460178201279181634013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2332306785467519454422675 3498460178201279181634013)
        ·
          refine ⟨1311922566825479693112755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3498460178201279181634013 1311922566825479693112755)
          ·
            refine ⟨1967883850238219539669133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1311922566825479693112755 1967883850238219539669133)
            ·
              refine ⟨737956443839332327375925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1967883850238219539669133 737956443839332327375925)
              ·
                refine ⟨69183416609937405691493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 737956443839332327375925 69183416609937405691493)
                ·
                  refine ⟨12971890614363263567155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69183416609937405691493 12971890614363263567155)
                  ·
                    rfl

theorem cell21_56841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 4].length) (baseStart_56841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_56841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_56841 prefixEnd_56841 := by exact prefixLift 56841
  have htrace : WordTrace (prefixWord ++ tailWord_56841) baseStart_56841 baseEnd_56841 := by
    simpa [prefixWord, tailWord_56841, baseEnd_56841] using wordTrace_append hprefix tailTrace_56841
  have hstable : (prefixWord ++ tailWord_56841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56841).length < 2 ^ (prefixWord ++ tailWord_56841).sum := by decide
  have hdescent : baseEnd_56841 < baseStart_56841 := by decide
  rcases family_descends (prefixWord ++ tailWord_56841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56931 : List Nat := [1, 1, 1, 5, 1, 3, 9]
def baseStart_56931 : Nat := 118140960795 + 56931 * 2 ^ 59
def prefixEnd_56931 : Nat := 4983230072969 + 3 ^ 40 * 56931 * 2
def baseEnd_56931 : Nat := 1443603315615900785219

theorem tailTrace_56931 : CollatzResearch.WordTrace tailWord_56931 prefixEnd_56931 1443603315615900785219 := by
  unfold tailWord_56931
  simp only [CollatzResearch.WordTrace]
  refine ⟨2076444156756184885818647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1384296104504123257212431 2076444156756184885818647)
  ·
    refine ⟨3114666235134277328727971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2076444156756184885818647 3114666235134277328727971)
    ·
      refine ⟨4671999352701415993091957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3114666235134277328727971 4671999352701415993091957)
      ·
        refine ⟨437999939315757749352371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4671999352701415993091957 437999939315757749352371)
        ·
          refine ⟨656999908973636624028557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437999939315757749352371 656999908973636624028557)
          ·
            refine ⟨246374965865113734010709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 656999908973636624028557 246374965865113734010709)
            ·
              refine ⟨1443603315615900785219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 246374965865113734010709 1443603315615900785219)
              ·
                rfl

theorem cell21_56931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 9].length) (baseStart_56931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_56931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_56931 prefixEnd_56931 := by exact prefixLift 56931
  have htrace : WordTrace (prefixWord ++ tailWord_56931) baseStart_56931 baseEnd_56931 := by
    simpa [prefixWord, tailWord_56931, baseEnd_56931] using wordTrace_append hprefix tailTrace_56931
  have hstable : (prefixWord ++ tailWord_56931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56931).length < 2 ^ (prefixWord ++ tailWord_56931).sum := by decide
  have hdescent : baseEnd_56931 < baseStart_56931 := by decide
  rcases family_descends (prefixWord ++ tailWord_56931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56976 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 8]
def baseStart_56976 : Nat := 118140960795 + 56976 * 2 ^ 59
def prefixEnd_56976 : Nat := 4983230072969 + 3 ^ 40 * 56976 * 2
def baseEnd_56976 : Nat := 13002699453633028816879

theorem tailTrace_56976 : CollatzResearch.WordTrace tailWord_56976 prefixEnd_56976 13002699453633028816879 := by
  unfold tailWord_56976
  simp only [CollatzResearch.WordTrace]
  refine ⟨1039042720796578785603391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1385390294395438380804521 1039042720796578785603391)
  ·
    refine ⟨1558564081194868178405087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1039042720796578785603391 1558564081194868178405087)
    ·
      refine ⟨2337846121792302267607631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1558564081194868178405087 2337846121792302267607631)
      ·
        refine ⟨3506769182688453401411447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2337846121792302267607631 3506769182688453401411447)
        ·
          refine ⟨5260153774032680102117171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3506769182688453401411447 5260153774032680102117171)
          ·
            refine ⟨7890230661049020153175757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5260153774032680102117171 7890230661049020153175757)
            ·
              refine ⟨2958836497893382557440909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7890230661049020153175757 2958836497893382557440909)
              ·
                refine ⟨1109563686710018459040341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2958836497893382557440909 1109563686710018459040341)
                ·
                  refine ⟨13002699453633028816879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1109563686710018459040341 13002699453633028816879)
                  ·
                    rfl

theorem cell21_56976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 8].length) (baseStart_56976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_56976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_56976 prefixEnd_56976 := by exact prefixLift 56976
  have htrace : WordTrace (prefixWord ++ tailWord_56976) baseStart_56976 baseEnd_56976 := by
    simpa [prefixWord, tailWord_56976, baseEnd_56976] using wordTrace_append hprefix tailTrace_56976
  have hstable : (prefixWord ++ tailWord_56976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56976).length < 2 ^ (prefixWord ++ tailWord_56976).sum := by decide
  have hdescent : baseEnd_56976 < baseStart_56976 := by decide
  rcases family_descends (prefixWord ++ tailWord_56976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56996 : List Nat := [2, 3, 1, 2, 2, 3, 1, 4, 3]
def baseStart_56996 : Nat := 118140960795 + 56996 * 2 ^ 59
def prefixEnd_56996 : Nat := 4983230072969 + 3 ^ 40 * 56996 * 2
def baseEnd_56996 : Nat := 13007263726117438483505

theorem tailTrace_56996 : CollatzResearch.WordTrace tailWord_56996 prefixEnd_56996 13007263726117438483505 := by
  unfold tailWord_56996
  simp only [CollatzResearch.WordTrace]
  refine ⟨1039407450760350493467421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1385876601013800657956561 1039407450760350493467421)
  ·
    refine ⟨389777794035131435050283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1039407450760350493467421 389777794035131435050283)
    ·
      refine ⟨584666691052697152575425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389777794035131435050283 584666691052697152575425)
      ·
        refine ⟨438500018289522864431569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 584666691052697152575425 438500018289522864431569)
        ·
          refine ⟨328875013717142148323677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 438500018289522864431569 328875013717142148323677)
          ·
            refine ⟨123328130143928305621379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328875013717142148323677 123328130143928305621379)
            ·
              refine ⟨184992195215892458432069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123328130143928305621379 184992195215892458432069)
              ·
                refine ⟨34686036602979835956013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184992195215892458432069 34686036602979835956013)
                ·
                  refine ⟨13007263726117438483505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34686036602979835956013 13007263726117438483505)
                  ·
                    rfl

theorem cell21_56996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_56996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_56996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_56996 prefixEnd_56996 := by exact prefixLift 56996
  have htrace : WordTrace (prefixWord ++ tailWord_56996) baseStart_56996 baseEnd_56996 := by
    simpa [prefixWord, tailWord_56996, baseEnd_56996] using wordTrace_append hprefix tailTrace_56996
  have hstable : (prefixWord ++ tailWord_56996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56996).length < 2 ^ (prefixWord ++ tailWord_56996).sum := by decide
  have hdescent : baseEnd_56996 < baseStart_56996 := by decide
  rcases family_descends (prefixWord ++ tailWord_56996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57024 : List Nat := [2, 1, 1, 2, 4, 1, 5, 5]
def baseStart_57024 : Nat := 118140960795 + 57024 * 2 ^ 59
def prefixEnd_57024 : Nat := 4983230072969 + 3 ^ 40 * 57024 * 2
def baseEnd_57024 : Nat := 4337884569198537338927

theorem tailTrace_57024 : CollatzResearch.WordTrace tailWord_57024 prefixEnd_57024 4337884569198537338927 := by
  unfold tailWord_57024
  simp only [CollatzResearch.WordTrace]
  refine ⟨1039918072709630884477063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1386557430279507845969417 1039918072709630884477063)
  ·
    refine ⟨1559877109064446326715595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1039918072709630884477063 1559877109064446326715595)
    ·
      refine ⟨2339815663596669490073393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1559877109064446326715595 2339815663596669490073393)
      ·
        refine ⟨1754861747697502117555045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2339815663596669490073393 1754861747697502117555045)
        ·
          refine ⟨329036577693281647041571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1754861747697502117555045 329036577693281647041571)
          ·
            refine ⟨493554866539922470562357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329036577693281647041571 493554866539922470562357)
            ·
              refine ⟨46270768738117731615221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 493554866539922470562357 46270768738117731615221)
              ·
                refine ⟨4337884569198537338927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46270768738117731615221 4337884569198537338927)
                ·
                  rfl

theorem cell21_57024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 5].length) (baseStart_57024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_57024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_57024 prefixEnd_57024 := by exact prefixLift 57024
  have htrace : WordTrace (prefixWord ++ tailWord_57024) baseStart_57024 baseEnd_57024 := by
    simpa [prefixWord, tailWord_57024, baseEnd_57024] using wordTrace_append hprefix tailTrace_57024
  have hstable : (prefixWord ++ tailWord_57024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57024).length < 2 ^ (prefixWord ++ tailWord_57024).sum := by decide
  have hdescent : baseEnd_57024 < baseStart_57024 := by decide
  rcases family_descends (prefixWord ++ tailWord_57024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57030 : List Nat := [6, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_57030 : Nat := 118140960795 + 57030 * 2 ^ 59
def prefixEnd_57030 : Nat := 4983230072969 + 3 ^ 40 * 57030 * 2
def baseEnd_57030 : Nat := 13015022989340934916769

theorem tailTrace_57030 : CollatzResearch.WordTrace tailWord_57030 prefixEnd_57030 13015022989340934916769 := by
  unfold tailWord_57030
  simp only [CollatzResearch.WordTrace]
  refine ⟨65001718231172649802267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1386703322265016529115029 65001718231172649802267)
  ·
    refine ⟨97502577346758974703401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65001718231172649802267 97502577346758974703401)
    ·
      refine ⟨73126933010069231027551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97502577346758974703401 73126933010069231027551)
      ·
        refine ⟨109690399515103846541327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73126933010069231027551 109690399515103846541327)
        ·
          refine ⟨164535599272655769811991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109690399515103846541327 164535599272655769811991)
          ·
            refine ⟨246803398908983654717987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164535599272655769811991 246803398908983654717987)
            ·
              refine ⟨370205098363475482076981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246803398908983654717987 370205098363475482076981)
              ·
                refine ⟨34706727971575826444717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 370205098363475482076981 34706727971575826444717)
                ·
                  refine ⟨13015022989340934916769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34706727971575826444717 13015022989340934916769)
                  ·
                    rfl

theorem cell21_57030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_57030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_57030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_57030 prefixEnd_57030 := by exact prefixLift 57030
  have htrace : WordTrace (prefixWord ++ tailWord_57030) baseStart_57030 baseEnd_57030 := by
    simpa [prefixWord, tailWord_57030, baseEnd_57030] using wordTrace_append hprefix tailTrace_57030
  have hstable : (prefixWord ++ tailWord_57030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57030).length < 2 ^ (prefixWord ++ tailWord_57030).sum := by decide
  have hdescent : baseEnd_57030 < baseStart_57030 := by decide
  rcases family_descends (prefixWord ++ tailWord_57030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57038 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 7]
def baseStart_57038 : Nat := 118140960795 + 57038 * 2 ^ 59
def prefixEnd_57038 : Nat := 4983230072969 + 3 ^ 40 * 57038 * 2
def baseEnd_57038 : Nat := 13016848698334698783419

theorem tailTrace_57038 : CollatzResearch.WordTrace tailWord_57038 prefixEnd_57038 13016848698334698783419 := by
  unfold tailWord_57038
  simp only [CollatzResearch.WordTrace]
  refine ⟨260043345921067769995471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1386897844912361439975845 260043345921067769995471)
  ·
    refine ⟨390065018881601654993207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260043345921067769995471 390065018881601654993207)
    ·
      refine ⟨585097528322402482489811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390065018881601654993207 585097528322402482489811)
      ·
        refine ⟨877646292483603723734717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585097528322402482489811 877646292483603723734717)
        ·
          refine ⟨329117359681351396400519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 877646292483603723734717 329117359681351396400519)
          ·
            refine ⟨493676039522027094600779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329117359681351396400519 493676039522027094600779)
            ·
              refine ⟨740514059283040641901169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493676039522027094600779 740514059283040641901169)
              ·
                refine ⟨555385544462280481425877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 740514059283040641901169 555385544462280481425877)
                ·
                  refine ⟨13016848698334698783419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 555385544462280481425877 13016848698334698783419)
                  ·
                    rfl

theorem cell21_57038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_57038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_57038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_57038 prefixEnd_57038 := by exact prefixLift 57038
  have htrace : WordTrace (prefixWord ++ tailWord_57038) baseStart_57038 baseEnd_57038 := by
    simpa [prefixWord, tailWord_57038, baseEnd_57038] using wordTrace_append hprefix tailTrace_57038
  have hstable : (prefixWord ++ tailWord_57038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57038).length < 2 ^ (prefixWord ++ tailWord_57038).sum := by decide
  have hdescent : baseEnd_57038 < baseStart_57038 := by decide
  rcases family_descends (prefixWord ++ tailWord_57038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57055 : List Nat := [1, 1, 2, 3, 2, 2, 1, 6, 3]
def baseStart_57055 : Nat := 118140960795 + 57055 * 2 ^ 59
def prefixEnd_57055 : Nat := 4983230072969 + 3 ^ 40 * 57055 * 2
def baseEnd_57055 : Nat := 13020728329946447000051

theorem tailTrace_57055 : CollatzResearch.WordTrace tailWord_57055 prefixEnd_57055 13020728329946447000051 := by
  unfold tailWord_57055
  simp only [CollatzResearch.WordTrace]
  refine ⟨2080966808306954063332619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1387311205537969375555079 2080966808306954063332619)
  ·
    refine ⟨3121450212460431094998929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2080966808306954063332619 3121450212460431094998929)
    ·
      refine ⟨2341087659345323321249197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3121450212460431094998929 2341087659345323321249197)
      ·
        refine ⟨877907872254496245468449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2341087659345323321249197 877907872254496245468449)
        ·
          refine ⟨658430904190872184101337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 877907872254496245468449 658430904190872184101337)
          ·
            refine ⟨493823178143154138076003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 658430904190872184101337 493823178143154138076003)
            ·
              refine ⟨740734767214731207114005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493823178143154138076003 740734767214731207114005)
              ·
                refine ⟨34721942213190525333469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 740734767214731207114005 34721942213190525333469)
                ·
                  refine ⟨13020728329946447000051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34721942213190525333469 13020728329946447000051)
                  ·
                    rfl

theorem cell21_57055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6, 3].length) (baseStart_57055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_57055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_57055 prefixEnd_57055 := by exact prefixLift 57055
  have htrace : WordTrace (prefixWord ++ tailWord_57055) baseStart_57055 baseEnd_57055 := by
    simpa [prefixWord, tailWord_57055, baseEnd_57055] using wordTrace_append hprefix tailTrace_57055
  have hstable : (prefixWord ++ tailWord_57055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57055).length < 2 ^ (prefixWord ++ tailWord_57055).sum := by decide
  have hdescent : baseEnd_57055 < baseStart_57055 := by decide
  rcases family_descends (prefixWord ++ tailWord_57055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57106 : List Nat := [3, 2, 4, 1, 1, 2, 3, 2, 3]
def baseStart_57106 : Nat := 118140960795 + 57106 * 2 ^ 59
def prefixEnd_57106 : Nat := 4983230072969 + 3 ^ 40 * 57106 * 2
def baseEnd_57106 : Nat := 13032367224781691649947

theorem tailTrace_57106 : CollatzResearch.WordTrace tailWord_57106 prefixEnd_57106 13032367224781691649947 := by
  unfold tailWord_57106
  simp only [CollatzResearch.WordTrace]
  refine ⟨520706732780547443359793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1388551287414793182292781 520706732780547443359793)
  ·
    refine ⟨390530049585410582519845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 520706732780547443359793 390530049585410582519845)
    ·
      refine ⟨73224384297264484222471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 390530049585410582519845 73224384297264484222471)
      ·
        refine ⟨109836576445896726333707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73224384297264484222471 109836576445896726333707)
        ·
          refine ⟨164754864668845089500561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109836576445896726333707 164754864668845089500561)
          ·
            refine ⟨123566148501633817125421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164754864668845089500561 123566148501633817125421)
            ·
              refine ⟨46337305688112681422033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123566148501633817125421 46337305688112681422033)
              ·
                refine ⟨34752979266084511066525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46337305688112681422033 34752979266084511066525)
                ·
                  refine ⟨13032367224781691649947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34752979266084511066525 13032367224781691649947)
                  ·
                    rfl

theorem cell21_57106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_57106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_57106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_57106 prefixEnd_57106 := by exact prefixLift 57106
  have htrace : WordTrace (prefixWord ++ tailWord_57106) baseStart_57106 baseEnd_57106 := by
    simpa [prefixWord, tailWord_57106, baseEnd_57106] using wordTrace_append hprefix tailTrace_57106
  have hstable : (prefixWord ++ tailWord_57106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57106).length < 2 ^ (prefixWord ++ tailWord_57106).sum := by decide
  have hdescent : baseEnd_57106 < baseStart_57106 := by decide
  rcases family_descends (prefixWord ++ tailWord_57106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57165 : List Nat := [1, 6, 1, 2, 1, 2, 1, 4, 3]
def baseStart_57165 : Nat := 118140960795 + 57165 * 2 ^ 59
def prefixEnd_57165 : Nat := 4983230072969 + 3 ^ 40 * 57165 * 2
def baseEnd_57165 : Nat := 13045831828610700166493

theorem tailTrace_57165 : CollatzResearch.WordTrace tailWord_57165 prefixEnd_57165 13045831828610700166493 := by
  unfold tailWord_57165
  simp only [CollatzResearch.WordTrace]
  refine ⟨2084978837908442849836949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1389985891938961899891299 2084978837908442849836949)
  ·
    refine ⟨97733383026958258586107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2084978837908442849836949 97733383026958258586107)
    ·
      refine ⟨146600074540437387879161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97733383026958258586107 146600074540437387879161)
      ·
        refine ⟨109950055905328040909371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146600074540437387879161 109950055905328040909371)
        ·
          refine ⟨164925083857992061364057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109950055905328040909371 164925083857992061364057)
          ·
            refine ⟨123693812893494046023043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164925083857992061364057 123693812893494046023043)
            ·
              refine ⟨185540719340241069034565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123693812893494046023043 185540719340241069034565)
              ·
                refine ⟨34788884876295200443981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185540719340241069034565 34788884876295200443981)
                ·
                  refine ⟨13045831828610700166493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34788884876295200443981 13045831828610700166493)
                  ·
                    rfl

theorem cell21_57165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_57165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_57165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_57165 prefixEnd_57165 := by exact prefixLift 57165
  have htrace : WordTrace (prefixWord ++ tailWord_57165) baseStart_57165 baseEnd_57165 := by
    simpa [prefixWord, tailWord_57165, baseEnd_57165] using wordTrace_append hprefix tailTrace_57165
  have hstable : (prefixWord ++ tailWord_57165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57165).length < 2 ^ (prefixWord ++ tailWord_57165).sum := by decide
  have hdescent : baseEnd_57165 < baseStart_57165 := by decide
  rcases family_descends (prefixWord ++ tailWord_57165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57252 : List Nat := [2, 3, 1, 2, 1, 3, 4, 5]
def baseStart_57252 : Nat := 118140960795 + 57252 * 2 ^ 59
def prefixEnd_57252 : Nat := 4983230072969 + 3 ^ 40 * 57252 * 2
def baseEnd_57252 : Nat := 4355228804639294072105

theorem tailTrace_57252 : CollatzResearch.WordTrace tailWord_57252 prefixEnd_57252 4355228804639294072105 := by
  unfold tailWord_57252
  simp only [CollatzResearch.WordTrace]
  refine ⟨1044075994296628354127005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1392101325728837805502673 1044075994296628354127005)
  ·
    refine ⟨391528497861235632797627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1044075994296628354127005 391528497861235632797627)
    ·
      refine ⟨587292746791853449196441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391528497861235632797627 587292746791853449196441)
      ·
        refine ⟨440469560093890086897331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 587292746791853449196441 440469560093890086897331)
        ·
          refine ⟨660704340140835130345997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440469560093890086897331 660704340140835130345997)
          ·
            refine ⟨247764127552813173879749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 660704340140835130345997 247764127552813173879749)
            ·
              refine ⟨46455773916152470102453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247764127552813173879749 46455773916152470102453)
              ·
                refine ⟨4355228804639294072105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46455773916152470102453 4355228804639294072105)
                ·
                  rfl

theorem cell21_57252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 5].length) (baseStart_57252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_57252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_57252 prefixEnd_57252 := by exact prefixLift 57252
  have htrace : WordTrace (prefixWord ++ tailWord_57252) baseStart_57252 baseEnd_57252 := by
    simpa [prefixWord, tailWord_57252, baseEnd_57252] using wordTrace_append hprefix tailTrace_57252
  have hstable : (prefixWord ++ tailWord_57252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57252).length < 2 ^ (prefixWord ++ tailWord_57252).sum := by decide
  have hdescent : baseEnd_57252 < baseStart_57252 := by decide
  rcases family_descends (prefixWord ++ tailWord_57252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57280 : List Nat := [2, 1, 1, 2, 3, 2, 1, 3, 6]
def baseStart_57280 : Nat := 118140960795 + 57280 * 2 ^ 59
def prefixEnd_57280 : Nat := 4983230072969 + 3 ^ 40 * 57280 * 2
def baseEnd_57280 : Nat := 13072076395396055749591

theorem tailTrace_57280 : CollatzResearch.WordTrace tailWord_57280 prefixEnd_57280 13072076395396055749591 := by
  unfold tailWord_57280
  simp only [CollatzResearch.WordTrace]
  refine ⟨1044586616245908745136647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1392782154994544993515529 1044586616245908745136647)
  ·
    refine ⟨1566879924368863117704971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1044586616245908745136647 1566879924368863117704971)
    ·
      refine ⟨2350319886553294676557457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1566879924368863117704971 2350319886553294676557457)
      ·
        refine ⟨1762739914914971007418093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2350319886553294676557457 1762739914914971007418093)
        ·
          refine ⟨661027468093114127781785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1762739914914971007418093 661027468093114127781785)
          ·
            refine ⟨495770601069835595836339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 661027468093114127781785 495770601069835595836339)
            ·
              refine ⟨743655901604753393754509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495770601069835595836339 743655901604753393754509)
              ·
                refine ⟨278870963101782522657941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 743655901604753393754509 278870963101782522657941)
                ·
                  refine ⟨13072076395396055749591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 278870963101782522657941 13072076395396055749591)
                  ·
                    rfl

theorem cell21_57280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 6].length) (baseStart_57280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_57280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_57280 prefixEnd_57280 := by exact prefixLift 57280
  have htrace : WordTrace (prefixWord ++ tailWord_57280) baseStart_57280 baseEnd_57280 := by
    simpa [prefixWord, tailWord_57280, baseEnd_57280] using wordTrace_append hprefix tailTrace_57280
  have hstable : (prefixWord ++ tailWord_57280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57280).length < 2 ^ (prefixWord ++ tailWord_57280).sum := by decide
  have hdescent : baseEnd_57280 < baseStart_57280 := by decide
  rcases family_descends (prefixWord ++ tailWord_57280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57311 : List Nat := [1, 1, 2, 3, 4, 1, 2, 7]
def baseStart_57311 : Nat := 118140960795 + 57311 * 2 ^ 59
def prefixEnd_57311 : Nat := 4983230072969 + 3 ^ 40 * 57311 * 2
def baseEnd_57311 : Nat := 4359717005915630244287

theorem tailTrace_57311 : CollatzResearch.WordTrace tailWord_57311 prefixEnd_57311 4359717005915630244287 := by
  unfold tailWord_57311
  simp only [CollatzResearch.WordTrace]
  refine ⟨2090303895379509784651787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1393535930253006523101191 2090303895379509784651787)
  ·
    refine ⟨3135455843069264676977681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2090303895379509784651787 3135455843069264676977681)
    ·
      refine ⟨2351591882301948507733261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3135455843069264676977681 2351591882301948507733261)
      ·
        refine ⟨881846955863230690399973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2351591882301948507733261 881846955863230690399973)
        ·
          refine ⟨165346304224355754449995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 881846955863230690399973 165346304224355754449995)
          ·
            refine ⟨248019456336533631674993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165346304224355754449995 248019456336533631674993)
            ·
              refine ⟨186014592252400223756245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248019456336533631674993 186014592252400223756245)
              ·
                refine ⟨4359717005915630244287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 186014592252400223756245 4359717005915630244287)
                ·
                  rfl

theorem cell21_57311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 7].length) (baseStart_57311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_57311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_57311 prefixEnd_57311 := by exact prefixLift 57311
  have htrace : WordTrace (prefixWord ++ tailWord_57311) baseStart_57311 baseEnd_57311 := by
    simpa [prefixWord, tailWord_57311, baseEnd_57311] using wordTrace_append hprefix tailTrace_57311
  have hstable : (prefixWord ++ tailWord_57311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57311).length < 2 ^ (prefixWord ++ tailWord_57311).sum := by decide
  have hdescent : baseEnd_57311 < baseStart_57311 := by decide
  rcases family_descends (prefixWord ++ tailWord_57311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57334 : List Nat := [5, 1, 1, 1, 4, 2, 2, 2, 3]
def baseStart_57334 : Nat := 118140960795 + 57334 * 2 ^ 59
def prefixEnd_57334 : Nat := 4983230072969 + 3 ^ 40 * 57334 * 2
def baseEnd_57334 : Nat := 13084399931103961849481

theorem tailTrace_57334 : CollatzResearch.WordTrace tailWord_57334 prefixEnd_57334 13084399931103961849481 := by
  unfold tailWord_57334
  simp only [CollatzResearch.WordTrace]
  refine ⟨130696423393511544546191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1394095182864123141826037 130696423393511544546191)
  ·
    refine ⟨196044635090267316819287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130696423393511544546191 196044635090267316819287)
    ·
      refine ⟨294066952635400975228931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196044635090267316819287 294066952635400975228931)
      ·
        refine ⟨441100428953101462843397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294066952635400975228931 441100428953101462843397)
        ·
          refine ⟨82706330428706524283137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 441100428953101462843397 82706330428706524283137)
          ·
            refine ⟨62029747821529893212353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82706330428706524283137 62029747821529893212353)
            ·
              refine ⟨46522310866147419909265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62029747821529893212353 46522310866147419909265)
              ·
                refine ⟨34891733149610564931949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46522310866147419909265 34891733149610564931949)
                ·
                  refine ⟨13084399931103961849481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34891733149610564931949 13084399931103961849481)
                  ·
                    rfl

theorem cell21_57334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_57334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_57334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_57334 prefixEnd_57334 := by exact prefixLift 57334
  have htrace : WordTrace (prefixWord ++ tailWord_57334) baseStart_57334 baseEnd_57334 := by
    simpa [prefixWord, tailWord_57334, baseEnd_57334] using wordTrace_append hprefix tailTrace_57334
  have hstable : (prefixWord ++ tailWord_57334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57334).length < 2 ^ (prefixWord ++ tailWord_57334).sum := by decide
  have hdescent : baseEnd_57334 < baseStart_57334 := by decide
  rcases family_descends (prefixWord ++ tailWord_57334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57390 : List Nat := [4, 1, 3, 1, 1, 2, 3, 2, 4]
def baseStart_57390 : Nat := 118140960795 + 57390 * 2 ^ 59
def prefixEnd_57390 : Nat := 4983230072969 + 3 ^ 40 * 57390 * 2
def baseEnd_57390 : Nat := 13097179894060308916033

theorem tailTrace_57390 : CollatzResearch.WordTrace tailWord_57390 prefixEnd_57390 13097179894060308916033 := by
  unfold tailWord_57390
  simp only [CollatzResearch.WordTrace]
  refine ⟨261648157761663284597203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1395456841395537517851749 261648157761663284597203)
  ·
    refine ⟨392472236642494926895805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261648157761663284597203 392472236642494926895805)
    ·
      refine ⟨147177088740935597585927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 392472236642494926895805 147177088740935597585927)
      ·
        refine ⟨220765633111403396378891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147177088740935597585927 220765633111403396378891)
        ·
          refine ⟨331148449667105094568337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220765633111403396378891 331148449667105094568337)
          ·
            refine ⟨248361337250328820926253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331148449667105094568337 248361337250328820926253)
            ·
              refine ⟨93135501468873307847345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248361337250328820926253 93135501468873307847345)
              ·
                refine ⟨69851626101654980885509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93135501468873307847345 69851626101654980885509)
                ·
                  refine ⟨13097179894060308916033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69851626101654980885509 13097179894060308916033)
                  ·
                    rfl

theorem cell21_57390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_57390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_57390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_57390 prefixEnd_57390 := by exact prefixLift 57390
  have htrace : WordTrace (prefixWord ++ tailWord_57390) baseStart_57390 baseEnd_57390 := by
    simpa [prefixWord, tailWord_57390, baseEnd_57390] using wordTrace_append hprefix tailTrace_57390
  have hstable : (prefixWord ++ tailWord_57390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57390).length < 2 ^ (prefixWord ++ tailWord_57390).sum := by decide
  have hdescent : baseEnd_57390 < baseStart_57390 := by decide
  rcases family_descends (prefixWord ++ tailWord_57390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57432 : List Nat := [2, 1, 2, 2, 1, 4, 1, 2, 6]
def baseStart_57432 : Nat := 118140960795 + 57432 * 2 ^ 59
def prefixEnd_57432 : Nat := 4983230072969 + 3 ^ 40 * 57432 * 2
def baseEnd_57432 : Nat := 13106764866277569215947

theorem tailTrace_57432 : CollatzResearch.WordTrace tailWord_57432 prefixEnd_57432 13106764866277569215947 := by
  unfold tailWord_57432
  simp only [CollatzResearch.WordTrace]
  refine ⟨1047358563970573724903275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1396478085294098299871033 1047358563970573724903275)
  ·
    refine ⟨1571037845955860587354913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1047358563970573724903275 1571037845955860587354913)
    ·
      refine ⟨1178278384466895440516185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1571037845955860587354913 1178278384466895440516185)
      ·
        refine ⟨883708788350171580387139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1178278384466895440516185 883708788350171580387139)
        ·
          refine ⟨1325563182525257370580709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 883708788350171580387139 1325563182525257370580709)
          ·
            refine ⟨248543096723485756983883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1325563182525257370580709 248543096723485756983883)
            ·
              refine ⟨372814645085228635475825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248543096723485756983883 372814645085228635475825)
              ·
                refine ⟨279610983813921476606869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372814645085228635475825 279610983813921476606869)
                ·
                  refine ⟨13106764866277569215947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 279610983813921476606869 13106764866277569215947)
                  ·
                    rfl

theorem cell21_57432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 6].length) (baseStart_57432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_57432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_57432 prefixEnd_57432 := by exact prefixLift 57432
  have htrace : WordTrace (prefixWord ++ tailWord_57432) baseStart_57432 baseEnd_57432 := by
    simpa [prefixWord, tailWord_57432, baseEnd_57432] using wordTrace_append hprefix tailTrace_57432
  have hstable : (prefixWord ++ tailWord_57432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57432).length < 2 ^ (prefixWord ++ tailWord_57432).sum := by decide
  have hdescent : baseEnd_57432 < baseStart_57432 := by decide
  rcases family_descends (prefixWord ++ tailWord_57432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57438 : List Nat := [4, 4, 1, 1, 2, 2, 7]
def baseStart_57438 : Nat := 118140960795 + 57438 * 2 ^ 59
def prefixEnd_57438 : Nat := 4983230072969 + 3 ^ 40 * 57438 * 2
def baseEnd_57438 : Nat := 1456459349780321346215

theorem tailTrace_57438 : CollatzResearch.WordTrace tailWord_57438 prefixEnd_57438 1456459349780321346215 := by
  unfold tailWord_57438
  simp only [CollatzResearch.WordTrace]
  refine ⟨261866995739926309315621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1396623977279606983016645 261866995739926309315621)
  ·
    refine ⟨49100061701236182996679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261866995739926309315621 49100061701236182996679)
    ·
      refine ⟨73650092551854274495019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49100061701236182996679 73650092551854274495019)
      ·
        refine ⟨110475138827781411742529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73650092551854274495019 110475138827781411742529)
        ·
          refine ⟨82856354120836058806897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110475138827781411742529 82856354120836058806897)
          ·
            refine ⟨62142265590627044105173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82856354120836058806897 62142265590627044105173)
            ·
              refine ⟨1456459349780321346215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 62142265590627044105173 1456459349780321346215)
              ·
                rfl

theorem cell21_57438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 7].length) (baseStart_57438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_57438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_57438 prefixEnd_57438 := by exact prefixLift 57438
  have htrace : WordTrace (prefixWord ++ tailWord_57438) baseStart_57438 baseEnd_57438 := by
    simpa [prefixWord, tailWord_57438, baseEnd_57438] using wordTrace_append hprefix tailTrace_57438
  have hstable : (prefixWord ++ tailWord_57438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57438).length < 2 ^ (prefixWord ++ tailWord_57438).sum := by decide
  have hdescent : baseEnd_57438 < baseStart_57438 := by decide
  rcases family_descends (prefixWord ++ tailWord_57438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57452 : List Nat := [2, 2, 1, 1, 3, 4, 3, 2, 3]
def baseStart_57452 : Nat := 118140960795 + 57452 * 2 ^ 59
def prefixEnd_57452 : Nat := 4983230072969 + 3 ^ 40 * 57452 * 2
def baseEnd_57452 : Nat := 13111329138761978882573

theorem tailTrace_57452 : CollatzResearch.WordTrace tailWord_57452 prefixEnd_57452 13111329138761978882573 := by
  unfold tailWord_57452
  simp only [CollatzResearch.WordTrace]
  refine ⟨1047723293934345432767305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1396964391912460577023073 1047723293934345432767305)
  ·
    refine ⟨785792470450759074575479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1047723293934345432767305 785792470450759074575479)
    ·
      refine ⟨1178688705676138611863219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 785792470450759074575479 1178688705676138611863219)
      ·
        refine ⟨1768033058514207917794829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1178688705676138611863219 1768033058514207917794829)
        ·
          refine ⟨663012396942827969173061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1768033058514207917794829 663012396942827969173061)
          ·
            refine ⟨124314824426780244219949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 663012396942827969173061 124314824426780244219949)
            ·
              refine ⟨46618059160042591582481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124314824426780244219949 46618059160042591582481)
              ·
                refine ⟨34963544370031943686861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46618059160042591582481 34963544370031943686861)
                ·
                  refine ⟨13111329138761978882573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34963544370031943686861 13111329138761978882573)
                  ·
                    rfl

theorem cell21_57452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2, 3].length) (baseStart_57452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_57452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_57452 prefixEnd_57452 := by exact prefixLift 57452
  have htrace : WordTrace (prefixWord ++ tailWord_57452) baseStart_57452 baseEnd_57452 := by
    simpa [prefixWord, tailWord_57452, baseEnd_57452] using wordTrace_append hprefix tailTrace_57452
  have hstable : (prefixWord ++ tailWord_57452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57452).length < 2 ^ (prefixWord ++ tailWord_57452).sum := by decide
  have hdescent : baseEnd_57452 < baseStart_57452 := by decide
  rcases family_descends (prefixWord ++ tailWord_57452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57463 : List Nat := [1, 1, 3, 1, 1, 6, 2, 6]
def baseStart_57463 : Nat := 118140960795 + 57463 * 2 ^ 59
def prefixEnd_57463 : Nat := 4983230072969 + 3 ^ 40 * 57463 * 2
def baseEnd_57463 : Nat := 4371279829542801399739

theorem tailTrace_57463 : CollatzResearch.WordTrace tailWord_57463 prefixEnd_57463 4371279829542801399739 := by
  unfold tailWord_57463
  simp only [CollatzResearch.WordTrace]
  refine ⟨2095847790828839744185043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1397231860552559829456695 2095847790828839744185043)
  ·
    refine ⟨3143771686243259616277565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2095847790828839744185043 3143771686243259616277565)
    ·
      refine ⟨1178914382341222356104087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3143771686243259616277565 1178914382341222356104087)
      ·
        refine ⟨1768371573511833534156131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1178914382341222356104087 1768371573511833534156131)
        ·
          refine ⟨2652557360267750301234197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1768371573511833534156131 2652557360267750301234197)
          ·
            refine ⟨124338626262550795370353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2652557360267750301234197 124338626262550795370353)
            ·
              refine ⟨93253969696913096527765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124338626262550795370353 93253969696913096527765)
              ·
                refine ⟨4371279829542801399739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93253969696913096527765 4371279829542801399739)
                ·
                  rfl

theorem cell21_57463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 6].length) (baseStart_57463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_57463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_57463 prefixEnd_57463 := by exact prefixLift 57463
  have htrace : WordTrace (prefixWord ++ tailWord_57463) baseStart_57463 baseEnd_57463 := by
    simpa [prefixWord, tailWord_57463, baseEnd_57463] using wordTrace_append hprefix tailTrace_57463
  have hstable : (prefixWord ++ tailWord_57463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57463).length < 2 ^ (prefixWord ++ tailWord_57463).sum := by decide
  have hdescent : baseEnd_57463 < baseStart_57463 := by decide
  rcases family_descends (prefixWord ++ tailWord_57463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57514 : List Nat := [3, 1, 5, 1, 3, 1, 1, 6]
def baseStart_57514 : Nat := 118140960795 + 57514 * 2 ^ 59
def prefixEnd_57514 : Nat := 4983230072969 + 3 ^ 40 * 57514 * 2
def baseEnd_57514 : Nat := 4375159461154549616371

theorem tailTrace_57514 : CollatzResearch.WordTrace tailWord_57514 prefixEnd_57514 4375159461154549616371 := by
  unfold tailWord_57514
  simp only [CollatzResearch.WordTrace]
  refine ⟨524426978411018863572899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1398471942429383636194397 524426978411018863572899)
  ·
    refine ⟨786640467616528295359349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 524426978411018863572899 786640467616528295359349)
    ·
      refine ⟨73747543839049527689939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 786640467616528295359349 73747543839049527689939)
      ·
        refine ⟨110621315758574291534909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73747543839049527689939 110621315758574291534909)
        ·
          refine ⟨41482993409465359325591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110621315758574291534909 41482993409465359325591)
          ·
            refine ⟨62224490114198038988387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41482993409465359325591 62224490114198038988387)
            ·
              refine ⟨93336735171297058482581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62224490114198038988387 93336735171297058482581)
              ·
                refine ⟨4375159461154549616371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93336735171297058482581 4375159461154549616371)
                ·
                  rfl

theorem cell21_57514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 6].length) (baseStart_57514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_57514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_57514 prefixEnd_57514 := by exact prefixLift 57514
  have htrace : WordTrace (prefixWord ++ tailWord_57514) baseStart_57514 baseEnd_57514 := by
    simpa [prefixWord, tailWord_57514, baseEnd_57514] using wordTrace_append hprefix tailTrace_57514
  have hstable : (prefixWord ++ tailWord_57514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57514).length < 2 ^ (prefixWord ++ tailWord_57514).sum := by decide
  have hdescent : baseEnd_57514 < baseStart_57514 := by decide
  rcases family_descends (prefixWord ++ tailWord_57514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57584 : List Nat := [2, 1, 1, 1, 3, 1, 1, 7, 4]
def baseStart_57584 : Nat := 118140960795 + 57584 * 2 ^ 59
def prefixEnd_57584 : Nat := 4983230072969 + 3 ^ 40 * 57584 * 2
def baseEnd_57584 : Nat := 13141453337159082682303

theorem tailTrace_57584 : CollatzResearch.WordTrace tailWord_57584 prefixEnd_57584 13141453337159082682303 := by
  unfold tailWord_57584
  simp only [CollatzResearch.WordTrace]
  refine ⟨1050130511695238704669903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1400174015593651606226537 1050130511695238704669903)
  ·
    refine ⟨1575195767542858057004855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1050130511695238704669903 1575195767542858057004855)
    ·
      refine ⟨2362793651314287085507283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1575195767542858057004855 2362793651314287085507283)
      ·
        refine ⟨3544190476971430628260925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2362793651314287085507283 3544190476971430628260925)
        ·
          refine ⟨1329071428864286485597847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3544190476971430628260925 1329071428864286485597847)
          ·
            refine ⟨1993607143296429728396771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1329071428864286485597847 1993607143296429728396771)
            ·
              refine ⟨2990410714944644592595157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1993607143296429728396771 2990410714944644592595157)
              ·
                refine ⟨70087751131515107638949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2990410714944644592595157 70087751131515107638949)
                ·
                  refine ⟨13141453337159082682303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70087751131515107638949 13141453337159082682303)
                  ·
                    rfl

theorem cell21_57584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 4].length) (baseStart_57584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_57584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_57584 prefixEnd_57584 := by exact prefixLift 57584
  have htrace : WordTrace (prefixWord ++ tailWord_57584) baseStart_57584 baseEnd_57584 := by
    simpa [prefixWord, tailWord_57584, baseEnd_57584] using wordTrace_append hprefix tailTrace_57584
  have hstable : (prefixWord ++ tailWord_57584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57584).length < 2 ^ (prefixWord ++ tailWord_57584).sum := by decide
  have hdescent : baseEnd_57584 < baseStart_57584 := by decide
  rcases family_descends (prefixWord ++ tailWord_57584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57680 : List Nat := [2, 1, 1, 1, 1, 8, 2, 2, 3]
def baseStart_57680 : Nat := 118140960795 + 57680 * 2 ^ 59
def prefixEnd_57680 : Nat := 4983230072969 + 3 ^ 40 * 57680 * 2
def baseEnd_57680 : Nat := 13163361845084249082107

theorem tailTrace_57680 : CollatzResearch.WordTrace tailWord_57680 prefixEnd_57680 13163361845084249082107 := by
  unfold tailWord_57680
  simp only [CollatzResearch.WordTrace]
  refine ⟨1051881215521342902417247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1402508287361790536556329 1051881215521342902417247)
  ·
    refine ⟨1577821823282014353625871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1051881215521342902417247 1577821823282014353625871)
    ·
      refine ⟨2366732734923021530438807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1577821823282014353625871 2366732734923021530438807)
      ·
        refine ⟨3550099102384532295658211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2366732734923021530438807 3550099102384532295658211)
        ·
          refine ⟨5325148653576798443487317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3550099102384532295658211 5325148653576798443487317)
          ·
            refine ⟨62404085784103106759617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 5325148653576798443487317 62404085784103106759617)
            ·
              refine ⟨46803064338077330069713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62404085784103106759617 46803064338077330069713)
              ·
                refine ⟨35102298253557997552285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46803064338077330069713 35102298253557997552285)
                ·
                  refine ⟨13163361845084249082107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35102298253557997552285 13163361845084249082107)
                  ·
                    rfl

theorem cell21_57680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2, 3].length) (baseStart_57680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_57680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_57680 prefixEnd_57680 := by exact prefixLift 57680
  have htrace : WordTrace (prefixWord ++ tailWord_57680) baseStart_57680 baseEnd_57680 := by
    simpa [prefixWord, tailWord_57680, baseEnd_57680] using wordTrace_append hprefix tailTrace_57680
  have hstable : (prefixWord ++ tailWord_57680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57680).length < 2 ^ (prefixWord ++ tailWord_57680).sum := by decide
  have hdescent : baseEnd_57680 < baseStart_57680 := by decide
  rcases family_descends (prefixWord ++ tailWord_57680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57705 : List Nat := [1, 2, 1, 1, 1, 3, 5, 2, 5]
def baseStart_57705 : Nat := 118140960795 + 57705 * 2 ^ 59
def prefixEnd_57705 : Nat := 4983230072969 + 3 ^ 40 * 57705 * 2
def baseEnd_57705 : Nat := 13169067185689761165389

theorem tailTrace_57705 : CollatzResearch.WordTrace tailWord_57705 prefixEnd_57705 13169067185689761165389 := by
  unfold tailWord_57705
  simp only [CollatzResearch.WordTrace]
  refine ⟨2104674255952115074494569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1403116170634743382996379 2104674255952115074494569)
  ·
    refine ⟨1578505691964086305870927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2104674255952115074494569 1578505691964086305870927)
    ·
      refine ⟨2367758537946129458806391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1578505691964086305870927 2367758537946129458806391)
      ·
        refine ⟨3551637806919194188209587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2367758537946129458806391 3551637806919194188209587)
        ·
          refine ⟨5327456710378791282314381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3551637806919194188209587 5327456710378791282314381)
          ·
            refine ⟨1997796266392046730867893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5327456710378791282314381 1997796266392046730867893)
            ·
              refine ⟨187293399974254381018865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1997796266392046730867893 187293399974254381018865)
              ·
                refine ⟨140470049980690785764149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187293399974254381018865 140470049980690785764149)
                ·
                  refine ⟨13169067185689761165389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140470049980690785764149 13169067185689761165389)
                  ·
                    rfl

theorem cell21_57705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 5].length) (baseStart_57705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_57705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_57705 prefixEnd_57705 := by exact prefixLift 57705
  have htrace : WordTrace (prefixWord ++ tailWord_57705) baseStart_57705 baseEnd_57705 := by
    simpa [prefixWord, tailWord_57705, baseEnd_57705] using wordTrace_append hprefix tailTrace_57705
  have hstable : (prefixWord ++ tailWord_57705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57705).length < 2 ^ (prefixWord ++ tailWord_57705).sum := by decide
  have hdescent : baseEnd_57705 < baseStart_57705 := by decide
  rcases family_descends (prefixWord ++ tailWord_57705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57708 : List Nat := [2, 2, 1, 1, 6, 1, 3, 5]
def baseStart_57708 : Nat := 118140960795 + 57708 * 2 ^ 59
def prefixEnd_57708 : Nat := 4983230072969 + 3 ^ 40 * 57708 * 2
def baseEnd_57708 : Nat := 4389917275520807538461

theorem tailTrace_57708 : CollatzResearch.WordTrace tailWord_57708 prefixEnd_57708 4389917275520807538461 := by
  unfold tailWord_57708
  simp only [CollatzResearch.WordTrace]
  refine ⟨1052391837470623293426889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1403189116627497724569185 1052391837470623293426889)
  ·
    refine ⟨789293878102967470070167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1052391837470623293426889 789293878102967470070167)
    ·
      refine ⟨1183940817154451205105251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 789293878102967470070167 1183940817154451205105251)
      ·
        refine ⟨1775911225731676807657877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1183940817154451205105251 1775911225731676807657877)
        ·
          refine ⟨83245838706172350358963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1775911225731676807657877 83245838706172350358963)
          ·
            refine ⟨124868758059258525538445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83245838706172350358963 124868758059258525538445)
            ·
              refine ⟨46825784272221947076917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124868758059258525538445 46825784272221947076917)
              ·
                refine ⟨4389917275520807538461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46825784272221947076917 4389917275520807538461)
                ·
                  rfl

theorem cell21_57708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 5].length) (baseStart_57708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_57708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_57708 prefixEnd_57708 := by exact prefixLift 57708
  have htrace : WordTrace (prefixWord ++ tailWord_57708) baseStart_57708 baseEnd_57708 := by
    simpa [prefixWord, tailWord_57708, baseEnd_57708] using wordTrace_append hprefix tailTrace_57708
  have hstable : (prefixWord ++ tailWord_57708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57708).length < 2 ^ (prefixWord ++ tailWord_57708).sum := by decide
  have hdescent : baseEnd_57708 < baseStart_57708 := by decide
  rcases family_descends (prefixWord ++ tailWord_57708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57736 : List Nat := [2, 1, 3, 3, 1, 1, 3, 1, 6]
def baseStart_57736 : Nat := 118140960795 + 57736 * 2 ^ 59
def prefixEnd_57736 : Nat := 4983230072969 + 3 ^ 40 * 57736 * 2
def baseEnd_57736 : Nat := 13176141808040596148659

theorem tailTrace_57736 : CollatzResearch.WordTrace tailWord_57736 prefixEnd_57736 13176141808040596148659 := by
  unfold tailWord_57736
  simp only [CollatzResearch.WordTrace]
  refine ⟨1052902459419903684436531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1403869945893204912582041 1052902459419903684436531)
  ·
    refine ⟨1579353689129855526654797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1052902459419903684436531 1579353689129855526654797)
    ·
      refine ⟨592257633423695822495549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1579353689129855526654797 592257633423695822495549)
      ·
        refine ⟨222096612533885933435831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 592257633423695822495549 222096612533885933435831)
        ·
          refine ⟨333144918800828900153747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222096612533885933435831 333144918800828900153747)
          ·
            refine ⟨499717378201243350230621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333144918800828900153747 499717378201243350230621)
            ·
              refine ⟨187394016825466256336483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 499717378201243350230621 187394016825466256336483)
              ·
                refine ⟨281091025238199384504725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187394016825466256336483 281091025238199384504725)
                ·
                  refine ⟨13176141808040596148659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 281091025238199384504725 13176141808040596148659)
                  ·
                    rfl

theorem cell21_57736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 6].length) (baseStart_57736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_57736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_57736 prefixEnd_57736 := by exact prefixLift 57736
  have htrace : WordTrace (prefixWord ++ tailWord_57736) baseStart_57736 baseEnd_57736 := by
    simpa [prefixWord, tailWord_57736, baseEnd_57736] using wordTrace_append hprefix tailTrace_57736
  have hstable : (prefixWord ++ tailWord_57736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57736).length < 2 ^ (prefixWord ++ tailWord_57736).sum := by decide
  have hdescent : baseEnd_57736 < baseStart_57736 := by decide
  rcases family_descends (prefixWord ++ tailWord_57736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57753 : List Nat := [1, 2, 1, 2, 1, 4, 5, 1, 4]
def baseStart_57753 : Nat := 118140960795 + 57753 * 2 ^ 59
def prefixEnd_57753 : Nat := 4983230072969 + 3 ^ 40 * 57753 * 2
def baseEnd_57753 : Nat := 13180021439652344365291

theorem tailTrace_57753 : CollatzResearch.WordTrace tailWord_57753 prefixEnd_57753 13180021439652344365291 := by
  unfold tailWord_57753
  simp only [CollatzResearch.WordTrace]
  refine ⟨2106424959778219272241913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1404283306518812848161275 2106424959778219272241913)
  ·
    refine ⟨1579818719833664454181435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2106424959778219272241913 1579818719833664454181435)
    ·
      refine ⟨2369728079750496681272153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1579818719833664454181435 2369728079750496681272153)
      ·
        refine ⟨1777296059812872510954115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2369728079750496681272153 1777296059812872510954115)
        ·
          refine ⟨2665944089719308766431173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1777296059812872510954115 2665944089719308766431173)
          ·
            refine ⟨499864516822370393705845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2665944089719308766431173 499864516822370393705845)
            ·
              refine ⟨46862298452097224409923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 499864516822370393705845 46862298452097224409923)
              ·
                refine ⟨70293447678145836614885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46862298452097224409923 70293447678145836614885)
                ·
                  refine ⟨13180021439652344365291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70293447678145836614885 13180021439652344365291)
                  ·
                    rfl

theorem cell21_57753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 4].length) (baseStart_57753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_57753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_57753 prefixEnd_57753 := by exact prefixLift 57753
  have htrace : WordTrace (prefixWord ++ tailWord_57753) baseStart_57753 baseEnd_57753 := by
    simpa [prefixWord, tailWord_57753, baseEnd_57753] using wordTrace_append hprefix tailTrace_57753
  have hstable : (prefixWord ++ tailWord_57753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57753).length < 2 ^ (prefixWord ++ tailWord_57753).sum := by decide
  have hdescent : baseEnd_57753 < baseStart_57753 := by decide
  rcases family_descends (prefixWord ++ tailWord_57753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57767 : List Nat := [1, 1, 6, 1, 1, 3, 1, 7]
def baseStart_57767 : Nat := 118140960795 + 57767 * 2 ^ 59
def prefixEnd_57767 : Nat := 4983230072969 + 3 ^ 40 * 57767 * 2
def baseEnd_57767 : Nat := 4394405476797143710643

theorem tailTrace_57767 : CollatzResearch.WordTrace tailWord_57767 prefixEnd_57767 4394405476797143710643 := by
  unfold tailWord_57767
  simp only [CollatzResearch.WordTrace]
  refine ⟨2106935581727499663251555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1404623721151666442167703 2106935581727499663251555)
  ·
    refine ⟨3160403372591249494877333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2106935581727499663251555 3160403372591249494877333)
    ·
      refine ⟨148143908090214820072375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3160403372591249494877333 148143908090214820072375)
      ·
        refine ⟨222215862135322230108563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148143908090214820072375 222215862135322230108563)
        ·
          refine ⟨333323793202983345162845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222215862135322230108563 333323793202983345162845)
          ·
            refine ⟨124996422451118754436067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 333323793202983345162845 124996422451118754436067)
            ·
              refine ⟨187494633676678131654101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124996422451118754436067 187494633676678131654101)
              ·
                refine ⟨4394405476797143710643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 187494633676678131654101 4394405476797143710643)
                ·
                  rfl

theorem cell21_57767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 7].length) (baseStart_57767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_57767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_57767 prefixEnd_57767 := by exact prefixLift 57767
  have htrace : WordTrace (prefixWord ++ tailWord_57767) baseStart_57767 baseEnd_57767 := by
    simpa [prefixWord, tailWord_57767, baseEnd_57767] using wordTrace_append hprefix tailTrace_57767
  have hstable : (prefixWord ++ tailWord_57767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57767).length < 2 ^ (prefixWord ++ tailWord_57767).sum := by decide
  have hdescent : baseEnd_57767 < baseStart_57767 := by decide
  rcases family_descends (prefixWord ++ tailWord_57767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57773 : List Nat := [1, 5, 2, 2, 2, 2, 1, 3, 3]
def baseStart_57773 : Nat := 118140960795 + 57773 * 2 ^ 59
def prefixEnd_57773 : Nat := 4983230072969 + 3 ^ 40 * 57773 * 2
def baseEnd_57773 : Nat := 13184585712136754031917

theorem tailTrace_57773 : CollatzResearch.WordTrace tailWord_57773 prefixEnd_57773 13184585712136754031917 := by
  unfold tailWord_57773
  simp only [CollatzResearch.WordTrace]
  refine ⟨2107154419705762687969973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1404769613137175125313315 2107154419705762687969973)
  ·
    refine ⟨197545726847415251997185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2107154419705762687969973 197545726847415251997185)
    ·
      refine ⟨148159295135561438997889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197545726847415251997185 148159295135561438997889)
      ·
        refine ⟨111119471351671079248417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148159295135561438997889 111119471351671079248417)
        ·
          refine ⟨83339603513753309436313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111119471351671079248417 83339603513753309436313)
          ·
            refine ⟨62504702635314982077235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83339603513753309436313 62504702635314982077235)
            ·
              refine ⟨93757053952972473115853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62504702635314982077235 93757053952972473115853)
              ·
                refine ⟨35158895232364677418445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93757053952972473115853 35158895232364677418445)
                ·
                  refine ⟨13184585712136754031917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35158895232364677418445 13184585712136754031917)
                  ·
                    rfl

theorem cell21_57773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_57773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_57773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_57773 prefixEnd_57773 := by exact prefixLift 57773
  have htrace : WordTrace (prefixWord ++ tailWord_57773) baseStart_57773 baseEnd_57773 := by
    simpa [prefixWord, tailWord_57773, baseEnd_57773] using wordTrace_append hprefix tailTrace_57773
  have hstable : (prefixWord ++ tailWord_57773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57773).length < 2 ^ (prefixWord ++ tailWord_57773).sum := by decide
  have hdescent : baseEnd_57773 < baseStart_57773 := by decide
  rcases family_descends (prefixWord ++ tailWord_57773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57860 : List Nat := [2, 3, 2, 3, 1, 3, 1, 6]
def baseStart_57860 : Nat := 118140960795 + 57860 * 2 ^ 59
def prefixEnd_57860 : Nat := 4983230072969 + 3 ^ 40 * 57860 * 2
def baseEnd_57860 : Nat := 4401480099147978693913

theorem tailTrace_57860 : CollatzResearch.WordTrace tailWord_57860 prefixEnd_57860 4401480099147978693913 := by
  unfold tailWord_57860
  simp only [CollatzResearch.WordTrace]
  refine ⟨1055163785195288273193517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1406885046927051030924689 1055163785195288273193517)
  ·
    refine ⟨395686419448233102447569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1055163785195288273193517 395686419448233102447569)
    ·
      refine ⟨296764814586174826835677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395686419448233102447569 296764814586174826835677)
      ·
        refine ⟨111286805469815560063379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296764814586174826835677 111286805469815560063379)
        ·
          refine ⟨166930208204723340095069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111286805469815560063379 166930208204723340095069)
          ·
            refine ⟨62598828076771252535651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166930208204723340095069 62598828076771252535651)
            ·
              refine ⟨93898242115156878803477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62598828076771252535651 93898242115156878803477)
              ·
                refine ⟨4401480099147978693913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93898242115156878803477 4401480099147978693913)
                ·
                  rfl

theorem cell21_57860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 6].length) (baseStart_57860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_57860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_57860 prefixEnd_57860 := by exact prefixLift 57860
  have htrace : WordTrace (prefixWord ++ tailWord_57860) baseStart_57860 baseEnd_57860 := by
    simpa [prefixWord, tailWord_57860, baseEnd_57860] using wordTrace_append hprefix tailTrace_57860
  have hstable : (prefixWord ++ tailWord_57860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57860).length < 2 ^ (prefixWord ++ tailWord_57860).sum := by decide
  have hdescent : baseEnd_57860 < baseStart_57860 := by decide
  rcases family_descends (prefixWord ++ tailWord_57860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57891 : List Nat := [1, 1, 1, 4, 4, 2, 2, 3, 3]
def baseStart_57891 : Nat := 118140960795 + 57891 * 2 ^ 59
def prefixEnd_57891 : Nat := 4983230072969 + 3 ^ 40 * 57891 * 2
def baseEnd_57891 : Nat := 13211514919794771065009

theorem tailTrace_57891 : CollatzResearch.WordTrace tailWord_57891 prefixEnd_57891 13211514919794771065009 := by
  unfold tailWord_57891
  simp only [CollatzResearch.WordTrace]
  refine ⟨2111458233278268840765527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1407638822185512560510351 2111458233278268840765527)
  ·
    refine ⟨3167187349917403261148291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2111458233278268840765527 3167187349917403261148291)
    ·
      refine ⟨4750781024876104891722437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3167187349917403261148291 4750781024876104891722437)
      ·
        refine ⟨890771442164269667197957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4750781024876104891722437 890771442164269667197957)
        ·
          refine ⟨167019645405800562599617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 890771442164269667197957 167019645405800562599617)
          ·
            refine ⟨125264734054350421949713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167019645405800562599617 125264734054350421949713)
            ·
              refine ⟨93948550540762816462285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125264734054350421949713 93948550540762816462285)
              ·
                refine ⟨35230706452786056173357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93948550540762816462285 35230706452786056173357)
                ·
                  refine ⟨13211514919794771065009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35230706452786056173357 13211514919794771065009)
                  ·
                    rfl

theorem cell21_57891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3, 3].length) (baseStart_57891 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_57891 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_57891 prefixEnd_57891 := by exact prefixLift 57891
  have htrace : WordTrace (prefixWord ++ tailWord_57891) baseStart_57891 baseEnd_57891 := by
    simpa [prefixWord, tailWord_57891, baseEnd_57891] using wordTrace_append hprefix tailTrace_57891
  have hstable : (prefixWord ++ tailWord_57891).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57891).length < 2 ^ (prefixWord ++ tailWord_57891).sum := by decide
  have hdescent : baseEnd_57891 < baseStart_57891 := by decide
  rcases family_descends (prefixWord ++ tailWord_57891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57908 : List Nat := [2, 5, 1, 3, 1, 1, 2, 1, 5]
def baseStart_57908 : Nat := 118140960795 + 57908 * 2 ^ 59
def prefixEnd_57908 : Nat := 4983230072969 + 3 ^ 40 * 57908 * 2
def baseEnd_57908 : Nat := 13215394551406519281641

theorem tailTrace_57908 : CollatzResearch.WordTrace tailWord_57908 prefixEnd_57908 13215394551406519281641 := by
  unfold tailWord_57908
  simp only [CollatzResearch.WordTrace]
  refine ⟨1056039137108340372067189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1408052182811120496089585 1056039137108340372067189)
  ·
    refine ⟨99003669103906909881299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1056039137108340372067189 99003669103906909881299)
    ·
      refine ⟨148505503655860364821949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99003669103906909881299 148505503655860364821949)
      ·
        refine ⟨55689563870947636808231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148505503655860364821949 55689563870947636808231)
        ·
          refine ⟨83534345806421455212347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55689563870947636808231 83534345806421455212347)
          ·
            refine ⟨125301518709632182818521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83534345806421455212347 125301518709632182818521)
            ·
              refine ⟨93976139032224137113891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125301518709632182818521 93976139032224137113891)
              ·
                refine ⟨140964208548336205670837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93976139032224137113891 140964208548336205670837)
                ·
                  refine ⟨13215394551406519281641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140964208548336205670837 13215394551406519281641)
                  ·
                    rfl

theorem cell21_57908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_57908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_57908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_57908 prefixEnd_57908 := by exact prefixLift 57908
  have htrace : WordTrace (prefixWord ++ tailWord_57908) baseStart_57908 baseEnd_57908 := by
    simpa [prefixWord, tailWord_57908, baseEnd_57908] using wordTrace_append hprefix tailTrace_57908
  have hstable : (prefixWord ++ tailWord_57908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57908).length < 2 ^ (prefixWord ++ tailWord_57908).sum := by decide
  have hdescent : baseEnd_57908 < baseStart_57908 := by decide
  rcases family_descends (prefixWord ++ tailWord_57908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57981 : List Nat := [1, 4, 1, 1, 5, 1, 1, 3, 4]
def baseStart_57981 : Nat := 118140960795 + 57981 * 2 ^ 59
def prefixEnd_57981 : Nat := 4983230072969 + 3 ^ 40 * 57981 * 2
def baseEnd_57981 : Nat := 13232054145974614564825

theorem tailTrace_57981 : CollatzResearch.WordTrace tailWord_57981 prefixEnd_57981 13232054145974614564825 := by
  unfold tailWord_57981
  simp only [CollatzResearch.WordTrace]
  refine ⟨2114740802952214211541797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1409827201968142807694531 2114740802952214211541797)
  ·
    refine ⟨396513900553540164664087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2114740802952214211541797 396513900553540164664087)
    ·
      refine ⟨594770850830310246996131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396513900553540164664087 594770850830310246996131)
      ·
        refine ⟨892156276245465370494197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594770850830310246996131 892156276245465370494197)
        ·
          refine ⟨83639650898012378483831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 892156276245465370494197 83639650898012378483831)
          ·
            refine ⟨125459476347018567725747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83639650898012378483831 125459476347018567725747)
            ·
              refine ⟨188189214520527851588621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125459476347018567725747 188189214520527851588621)
              ·
                refine ⟨70570955445197944345733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188189214520527851588621 70570955445197944345733)
                ·
                  refine ⟨13232054145974614564825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70570955445197944345733 13232054145974614564825)
                  ·
                    rfl

theorem cell21_57981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_57981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_57981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_57981 prefixEnd_57981 := by exact prefixLift 57981
  have htrace : WordTrace (prefixWord ++ tailWord_57981) baseStart_57981 baseEnd_57981 := by
    simpa [prefixWord, tailWord_57981, baseEnd_57981] using wordTrace_append hprefix tailTrace_57981
  have hstable : (prefixWord ++ tailWord_57981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57981).length < 2 ^ (prefixWord ++ tailWord_57981).sum := by decide
  have hdescent : baseEnd_57981 < baseStart_57981 := by decide
  rcases family_descends (prefixWord ++ tailWord_57981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58085 : List Nat := [1, 3, 1, 4, 1, 2, 1, 3, 5]
def baseStart_58085 : Nat := 118140960795 + 58085 * 2 ^ 59
def prefixEnd_58085 : Nat := 4983230072969 + 3 ^ 40 * 58085 * 2
def baseEnd_58085 : Nat := 13255788362893544831279

theorem tailTrace_58085 : CollatzResearch.WordTrace tailWord_58085 prefixEnd_58085 13255788362893544831279 := by
  unfold tailWord_58085
  simp only [CollatzResearch.WordTrace]
  refine ⟨2118533994575439973327709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1412355996383626648885139 2118533994575439973327709)
  ·
    refine ⟨794450247965789989997891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2118533994575439973327709 794450247965789989997891)
    ·
      refine ⟨1191675371948684984996837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 794450247965789989997891 1191675371948684984996837)
      ·
        refine ⟨223439132240378434686907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1191675371948684984996837 223439132240378434686907)
        ·
          refine ⟨335158698360567652030361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223439132240378434686907 335158698360567652030361)
          ·
            refine ⟨251369023770425739022771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335158698360567652030361 251369023770425739022771)
            ·
              refine ⟨377053535655638608534157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251369023770425739022771 377053535655638608534157)
              ·
                refine ⟨141395075870864478200309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 377053535655638608534157 141395075870864478200309)
                ·
                  refine ⟨13255788362893544831279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141395075870864478200309 13255788362893544831279)
                  ·
                    rfl

theorem cell21_58085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_58085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_58085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_58085 prefixEnd_58085 := by exact prefixLift 58085
  have htrace : WordTrace (prefixWord ++ tailWord_58085) baseStart_58085 baseEnd_58085 := by
    simpa [prefixWord, tailWord_58085, baseEnd_58085] using wordTrace_append hprefix tailTrace_58085
  have hstable : (prefixWord ++ tailWord_58085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58085).length < 2 ^ (prefixWord ++ tailWord_58085).sum := by decide
  have hdescent : baseEnd_58085 < baseStart_58085 := by decide
  rcases family_descends (prefixWord ++ tailWord_58085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58119 : List Nat := [1, 1, 4, 4, 1, 1, 3, 3, 3]
def baseStart_58119 : Nat := 118140960795 + 58119 * 2 ^ 59
def prefixEnd_58119 : Nat := 4983230072969 + 3 ^ 40 * 58119 * 2
def baseEnd_58119 : Nat := 13263547626117041264543

theorem tailTrace_58119 : CollatzResearch.WordTrace tailWord_58119 prefixEnd_58119 13263547626117041264543 := by
  unfold tailWord_58119
  simp only [CollatzResearch.WordTrace]
  refine ⟨2119774076452263780065411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1413182717634842520043607 2119774076452263780065411)
  ·
    refine ⟨3179661114678395670098117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2119774076452263780065411 3179661114678395670098117)
    ·
      refine ⟨596186459002199188143397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3179661114678395670098117 596186459002199188143397)
      ·
        refine ⟨111784961062912347776887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 596186459002199188143397 111784961062912347776887)
        ·
          refine ⟨167677441594368521665331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111784961062912347776887 167677441594368521665331)
          ·
            refine ⟨251516162391552782497997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167677441594368521665331 251516162391552782497997)
            ·
              refine ⟨94318560896832293436749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251516162391552782497997 94318560896832293436749)
              ·
                refine ⟨35369460336312110038781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94318560896832293436749 35369460336312110038781)
                ·
                  refine ⟨13263547626117041264543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35369460336312110038781 13263547626117041264543)
                  ·
                    rfl

theorem cell21_58119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3, 3].length) (baseStart_58119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_58119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_58119 prefixEnd_58119 := by exact prefixLift 58119
  have htrace : WordTrace (prefixWord ++ tailWord_58119) baseStart_58119 baseEnd_58119 := by
    simpa [prefixWord, tailWord_58119, baseEnd_58119] using wordTrace_append hprefix tailTrace_58119
  have hstable : (prefixWord ++ tailWord_58119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58119).length < 2 ^ (prefixWord ++ tailWord_58119).sum := by decide
  have hdescent : baseEnd_58119 < baseStart_58119 := by decide
  rcases family_descends (prefixWord ++ tailWord_58119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58265 : List Nat := [1, 2, 1, 2, 1, 3, 1, 10]
def baseStart_58265 : Nat := 118140960795 + 58265 * 2 ^ 59
def prefixEnd_58265 : Nat := 4983230072969 + 3 ^ 40 * 58265 * 2
def baseEnd_58265 : Nat := 4432288938417743943637

theorem tailTrace_58265 : CollatzResearch.WordTrace tailWord_58265 prefixEnd_58265 4432288938417743943637 := by
  unfold tailWord_58265
  simp only [CollatzResearch.WordTrace]
  refine ⟨2125099133923330714880249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1416732755948887143253499 2125099133923330714880249)
  ·
    refine ⟨1593824350442498036160187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2125099133923330714880249 1593824350442498036160187)
    ·
      refine ⟨2390736525663747054240281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1593824350442498036160187 2390736525663747054240281)
      ·
        refine ⟨1793052394247810290680211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2390736525663747054240281 1793052394247810290680211)
        ·
          refine ⟨2689578591371715436020317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1793052394247810290680211 2689578591371715436020317)
          ·
            refine ⟨1008591971764393288507619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2689578591371715436020317 1008591971764393288507619)
            ·
              refine ⟨1512887957646589932761429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1008591971764393288507619 1512887957646589932761429)
              ·
                refine ⟨4432288938417743943637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1512887957646589932761429 4432288938417743943637)
                ·
                  rfl

theorem cell21_58265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 10].length) (baseStart_58265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_58265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_58265 prefixEnd_58265 := by exact prefixLift 58265
  have htrace : WordTrace (prefixWord ++ tailWord_58265) baseStart_58265 baseEnd_58265 := by
    simpa [prefixWord, tailWord_58265, baseEnd_58265] using wordTrace_append hprefix tailTrace_58265
  have hstable : (prefixWord ++ tailWord_58265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58265).length < 2 ^ (prefixWord ++ tailWord_58265).sum := by decide
  have hdescent : baseEnd_58265 < baseStart_58265 := by decide
  rcases family_descends (prefixWord ++ tailWord_58265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58356 : List Nat := [2, 6, 2, 1, 2, 1, 2, 2, 3]
def baseStart_58356 : Nat := 118140960795 + 58356 * 2 ^ 59
def prefixEnd_58356 : Nat := 4983230072969 + 3 ^ 40 * 58356 * 2
def baseEnd_58356 : Nat := 13317634255057295814059

theorem tailTrace_58356 : CollatzResearch.WordTrace tailWord_58356 prefixEnd_58356 13317634255057295814059 := by
  unfold tailWord_58356
  simp only [CollatzResearch.WordTrace]
  refine ⟨1064209088296826628221461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1418945451062435504295281 1064209088296826628221461)
  ·
    refine ⟨49884801013913748197881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1064209088296826628221461 49884801013913748197881)
    ·
      refine ⟨37413600760435311148411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49884801013913748197881 37413600760435311148411)
      ·
        refine ⟨56120401140652966722617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37413600760435311148411 56120401140652966722617)
        ·
          refine ⟨42090300855489725041963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56120401140652966722617 42090300855489725041963)
          ·
            refine ⟨63135451283234587562945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42090300855489725041963 63135451283234587562945)
            ·
              refine ⟨47351588462425940672209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63135451283234587562945 47351588462425940672209)
              ·
                refine ⟨35513691346819455504157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47351588462425940672209 35513691346819455504157)
                ·
                  refine ⟨13317634255057295814059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35513691346819455504157 13317634255057295814059)
                  ·
                    rfl

theorem cell21_58356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_58356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_58356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_58356 prefixEnd_58356 := by exact prefixLift 58356
  have htrace : WordTrace (prefixWord ++ tailWord_58356) baseStart_58356 baseEnd_58356 := by
    simpa [prefixWord, tailWord_58356, baseEnd_58356] using wordTrace_append hprefix tailTrace_58356
  have hstable : (prefixWord ++ tailWord_58356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58356).length < 2 ^ (prefixWord ++ tailWord_58356).sum := by decide
  have hdescent : baseEnd_58356 < baseStart_58356 := by decide
  rcases family_descends (prefixWord ++ tailWord_58356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58358 : List Nat := [5, 1, 1, 1, 3, 10]
def baseStart_58358 : Nat := 118140960795 + 58358 * 2 ^ 59
def prefixEnd_58358 : Nat := 4983230072969 + 3 ^ 40 * 58358 * 2
def baseEnd_58358 : Nat := 493262617863175436323

theorem tailTrace_58358 : CollatzResearch.WordTrace tailWord_58358 prefixEnd_58358 493262617863175436323 := by
  unfold tailWord_58358
  simp only [CollatzResearch.WordTrace]
  refine ⟨133030695161650474875983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1418994081724271732010485 133030695161650474875983)
  ·
    refine ⟨199546042742475712313975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133030695161650474875983 199546042742475712313975)
    ·
      refine ⟨299319064113713568470963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199546042742475712313975 299319064113713568470963)
      ·
        refine ⟨448978596170570352706445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299319064113713568470963 448978596170570352706445)
        ·
          refine ⟨168366973563963882264917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 448978596170570352706445 168366973563963882264917)
          ·
            refine ⟨493262617863175436323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 168366973563963882264917 493262617863175436323)
            ·
              rfl

theorem cell21_58358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 10].length) (baseStart_58358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_58358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_58358 prefixEnd_58358 := by exact prefixLift 58358
  have htrace : WordTrace (prefixWord ++ tailWord_58358) baseStart_58358 baseEnd_58358 := by
    simpa [prefixWord, tailWord_58358, baseEnd_58358] using wordTrace_append hprefix tailTrace_58358
  have hstable : (prefixWord ++ tailWord_58358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58358).length < 2 ^ (prefixWord ++ tailWord_58358).sum := by decide
  have hdescent : baseEnd_58358 < baseStart_58358 := by decide
  rcases family_descends (prefixWord ++ tailWord_58358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58389 : List Nat := [1, 3, 2, 1, 4, 2, 1, 2, 5]
def baseStart_58389 : Nat := 118140960795 + 58389 * 2 ^ 59
def prefixEnd_58389 : Nat := 4983230072969 + 3 ^ 40 * 58389 * 2
def baseEnd_58389 : Nat := 13325165304656571763991

theorem tailTrace_58389 : CollatzResearch.WordTrace tailWord_58389 prefixEnd_58389 13325165304656571763991 := by
  unfold tailWord_58389
  simp only [CollatzResearch.WordTrace]
  refine ⟨2129621785474099892394221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1419747856982733261596147 2129621785474099892394221)
  ·
    refine ⟨798608169552787459647833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2129621785474099892394221 798608169552787459647833)
    ·
      refine ⟨598956127164590594735875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 798608169552787459647833 598956127164590594735875)
      ·
        refine ⟨898434190746885892103813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598956127164590594735875 898434190746885892103813)
        ·
          refine ⟨168456410765041104769465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 898434190746885892103813 168456410765041104769465)
          ·
            refine ⟨126342308073780828577099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168456410765041104769465 126342308073780828577099)
            ·
              refine ⟨189513462110671242865649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126342308073780828577099 189513462110671242865649)
              ·
                refine ⟨142135096583003432149237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189513462110671242865649 142135096583003432149237)
                ·
                  refine ⟨13325165304656571763991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142135096583003432149237 13325165304656571763991)
                  ·
                    rfl

theorem cell21_58389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_58389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_58389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_58389 prefixEnd_58389 := by exact prefixLift 58389
  have htrace : WordTrace (prefixWord ++ tailWord_58389) baseStart_58389 baseEnd_58389 := by
    simpa [prefixWord, tailWord_58389, baseEnd_58389] using wordTrace_append hprefix tailTrace_58389
  have hstable : (prefixWord ++ tailWord_58389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58389).length < 2 ^ (prefixWord ++ tailWord_58389).sum := by decide
  have hdescent : baseEnd_58389 < baseStart_58389 := by decide
  rcases family_descends (prefixWord ++ tailWord_58389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58417 : List Nat := [1, 2, 2, 3, 1, 2, 10]
def baseStart_58417 : Nat := 118140960795 + 58417 * 2 ^ 59
def prefixEnd_58417 : Nat := 4983230072969 + 3 ^ 40 * 58417 * 2
def baseEnd_58417 : Nat := 1481283920681638366363

theorem tailTrace_58417 : CollatzResearch.WordTrace tailWord_58417 prefixEnd_58417 1481283920681638366363 := by
  unfold tailWord_58417
  simp only [CollatzResearch.WordTrace]
  refine ⟨2130643029372660674413505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1420428686248440449609003 2130643029372660674413505)
  ·
    refine ⟨1597982272029495505810129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2130643029372660674413505 1597982272029495505810129)
    ·
      refine ⟨1198486704022121629357597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1597982272029495505810129 1198486704022121629357597)
      ·
        refine ⟨449432514008295611009099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1198486704022121629357597 449432514008295611009099)
        ·
          refine ⟨674148771012443416513649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449432514008295611009099 674148771012443416513649)
          ·
            refine ⟨505611578259332562385237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 674148771012443416513649 505611578259332562385237)
            ·
              refine ⟨1481283920681638366363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 505611578259332562385237 1481283920681638366363)
              ·
                rfl

theorem cell21_58417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 10].length) (baseStart_58417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_58417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_58417 prefixEnd_58417 := by exact prefixLift 58417
  have htrace : WordTrace (prefixWord ++ tailWord_58417) baseStart_58417 baseEnd_58417 := by
    simpa [prefixWord, tailWord_58417, baseEnd_58417] using wordTrace_append hprefix tailTrace_58417
  have hstable : (prefixWord ++ tailWord_58417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58417).length < 2 ^ (prefixWord ++ tailWord_58417).sum := by decide
  have hdescent : baseEnd_58417 < baseStart_58417 := by decide
  rcases family_descends (prefixWord ++ tailWord_58417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58479 : List Nat := [1, 1, 2, 1, 3, 3, 2, 4, 4]
def baseStart_58479 : Nat := 118140960795 + 58479 * 2 ^ 59
def prefixEnd_58479 : Nat := 4983230072969 + 3 ^ 40 * 58479 * 2
def baseEnd_58479 : Nat := 13345704530836415263807

theorem tailTrace_58479 : CollatzResearch.WordTrace tailWord_58479 prefixEnd_58479 13345704530836415263807 := by
  unfold tailWord_58479
  simp only [CollatzResearch.WordTrace]
  refine ⟨2132904355148045263170491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1421936236765363508780327 2132904355148045263170491)
  ·
    refine ⟨3199356532722067894755737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2132904355148045263170491 3199356532722067894755737)
    ·
      refine ⟨2399517399541550921066803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3199356532722067894755737 2399517399541550921066803)
      ·
        refine ⟨3599276099312326381600205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2399517399541550921066803 3599276099312326381600205)
        ·
          refine ⟨1349728537242122393100077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3599276099312326381600205 1349728537242122393100077)
          ·
            refine ⟨506148201465795897412529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1349728537242122393100077 506148201465795897412529)
            ·
              refine ⟨379611151099346923059397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 506148201465795897412529 379611151099346923059397)
              ·
                refine ⟨71177090831127548073637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 379611151099346923059397 71177090831127548073637)
                ·
                  refine ⟨13345704530836415263807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71177090831127548073637 13345704530836415263807)
                  ·
                    rfl

theorem cell21_58479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 4].length) (baseStart_58479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_58479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_58479 prefixEnd_58479 := by exact prefixLift 58479
  have htrace : WordTrace (prefixWord ++ tailWord_58479) baseStart_58479 baseEnd_58479 := by
    simpa [prefixWord, tailWord_58479, baseEnd_58479] using wordTrace_append hprefix tailTrace_58479
  have hstable : (prefixWord ++ tailWord_58479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58479).length < 2 ^ (prefixWord ++ tailWord_58479).sum := by decide
  have hdescent : baseEnd_58479 < baseStart_58479 := by decide
  rcases family_descends (prefixWord ++ tailWord_58479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58496 : List Nat := [2, 1, 1, 2, 1, 3, 6, 1, 4]
def baseStart_58496 : Nat := 118140960795 + 58496 * 2 ^ 59
def prefixEnd_58496 : Nat := 4983230072969 + 3 ^ 40 * 58496 * 2
def baseEnd_58496 : Nat := 13349584162448163480439

theorem tailTrace_58496 : CollatzResearch.WordTrace tailWord_58496 prefixEnd_58496 13349584162448163480439 := by
  unfold tailWord_58496
  simp only [CollatzResearch.WordTrace]
  refine ⟨1066762198043228583269671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1422349597390971444359561 1066762198043228583269671)
  ·
    refine ⟨1600143297064842874904507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1066762198043228583269671 1600143297064842874904507)
    ·
      refine ⟨2400214945597264312356761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1600143297064842874904507 2400214945597264312356761)
      ·
        refine ⟨1800161209197948234267571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2400214945597264312356761 1800161209197948234267571)
        ·
          refine ⟨2700241813796922351401357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1800161209197948234267571 2700241813796922351401357)
          ·
            refine ⟨1012590680173845881775509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2700241813796922351401357 1012590680173845881775509)
            ·
              refine ⟨47465188133149025708227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1012590680173845881775509 47465188133149025708227)
              ·
                refine ⟨71197782199723538562341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47465188133149025708227 71197782199723538562341)
                ·
                  refine ⟨13349584162448163480439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71197782199723538562341 13349584162448163480439)
                  ·
                    rfl

theorem cell21_58496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 4].length) (baseStart_58496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_58496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_58496 prefixEnd_58496 := by exact prefixLift 58496
  have htrace : WordTrace (prefixWord ++ tailWord_58496) baseStart_58496 baseEnd_58496 := by
    simpa [prefixWord, tailWord_58496, baseEnd_58496] using wordTrace_append hprefix tailTrace_58496
  have hstable : (prefixWord ++ tailWord_58496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58496).length < 2 ^ (prefixWord ++ tailWord_58496).sum := by decide
  have hdescent : baseEnd_58496 < baseStart_58496 := by decide
  rcases family_descends (prefixWord ++ tailWord_58496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58510 : List Nat := [4, 1, 1, 3, 2, 1, 2, 7]
def baseStart_58510 : Nat := 118140960795 + 58510 * 2 ^ 59
def prefixEnd_58510 : Nat := 4983230072969 + 3 ^ 40 * 58510 * 2
def baseEnd_58510 : Nat := 4450926384395750082359

theorem tailTrace_58510 : CollatzResearch.WordTrace tailWord_58510 prefixEnd_58510 4450926384395750082359 := by
  unfold tailWord_58510
  simp only [CollatzResearch.WordTrace]
  refine ⟨266754377254467194693623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1422690012023825038365989 266754377254467194693623)
  ·
    refine ⟨400131565881700792040435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266754377254467194693623 400131565881700792040435)
    ·
      refine ⟨600197348822551188060653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400131565881700792040435 600197348822551188060653)
      ·
        refine ⟨225074005808456695522745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 600197348822551188060653 225074005808456695522745)
        ·
          refine ⟨168805504356342521642059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225074005808456695522745 168805504356342521642059)
          ·
            refine ⟨253208256534513782463089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168805504356342521642059 253208256534513782463089)
            ·
              refine ⟨189906192400885336847317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253208256534513782463089 189906192400885336847317)
              ·
                refine ⟨4450926384395750082359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 189906192400885336847317 4450926384395750082359)
                ·
                  rfl

theorem cell21_58510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_58510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_58510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_58510 prefixEnd_58510 := by exact prefixLift 58510
  have htrace : WordTrace (prefixWord ++ tailWord_58510) baseStart_58510 baseEnd_58510 := by
    simpa [prefixWord, tailWord_58510, baseEnd_58510] using wordTrace_append hprefix tailTrace_58510
  have hstable : (prefixWord ++ tailWord_58510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58510).length < 2 ^ (prefixWord ++ tailWord_58510).sum := by decide
  have hdescent : baseEnd_58510 < baseStart_58510 := by decide
  rcases family_descends (prefixWord ++ tailWord_58510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58620 : List Nat := [2, 2, 2, 1, 6, 1, 2, 5]
def baseStart_58620 : Nat := 118140960795 + 58620 * 2 ^ 59
def prefixEnd_58620 : Nat := 4983230072969 + 3 ^ 40 * 58620 * 2
def baseEnd_58620 : Nat := 4459294217283834471173

theorem tailTrace_58620 : CollatzResearch.WordTrace tailWord_58620 prefixEnd_58620 4459294217283834471173 := by
  unfold tailWord_58620
  simp only [CollatzResearch.WordTrace]
  refine ⟨1069023523818613172026657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1425364698424817562702209 1069023523818613172026657)
  ·
    refine ⟨801767642863959879019993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1069023523818613172026657 801767642863959879019993)
    ·
      refine ⟨601325732147969909264995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 801767642863959879019993 601325732147969909264995)
      ·
        refine ⟨901988598221954863897493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601325732147969909264995 901988598221954863897493)
        ·
          refine ⟨42280715541654134245195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 901988598221954863897493 42280715541654134245195)
          ·
            refine ⟨63421073312481201367793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42280715541654134245195 63421073312481201367793)
            ·
              refine ⟨47565804984360901025845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63421073312481201367793 47565804984360901025845)
              ·
                refine ⟨4459294217283834471173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47565804984360901025845 4459294217283834471173)
                ·
                  rfl

theorem cell21_58620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 5].length) (baseStart_58620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_58620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_58620 prefixEnd_58620 := by exact prefixLift 58620
  have htrace : WordTrace (prefixWord ++ tailWord_58620) baseStart_58620 baseEnd_58620 := by
    simpa [prefixWord, tailWord_58620, baseEnd_58620] using wordTrace_append hprefix tailTrace_58620
  have hstable : (prefixWord ++ tailWord_58620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58620).length < 2 ^ (prefixWord ++ tailWord_58620).sum := by decide
  have hdescent : baseEnd_58620 < baseStart_58620 := by decide
  rcases family_descends (prefixWord ++ tailWord_58620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58707 : List Nat := [1, 1, 1, 2, 1, 1, 8, 2, 4]
def baseStart_58707 : Nat := 118140960795 + 58707 * 2 ^ 59
def prefixEnd_58707 : Nat := 4983230072969 + 3 ^ 40 * 58707 * 2
def baseEnd_58707 : Nat := 13397737237158685463341

theorem tailTrace_58707 : CollatzResearch.WordTrace tailWord_58707 prefixEnd_58707 13397737237158685463341 := by
  unfold tailWord_58707
  simp only [CollatzResearch.WordTrace]
  refine ⟨2141220198322040202470375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1427480132214693468313583 2141220198322040202470375)
  ·
    refine ⟨3211830297483060303705563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2141220198322040202470375 3211830297483060303705563)
    ·
      refine ⟨4817745446224590455558345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3211830297483060303705563 4817745446224590455558345)
      ·
        refine ⟨3613309084668442841668759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4817745446224590455558345 3613309084668442841668759)
        ·
          refine ⟨5419963627002664262503139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3613309084668442841668759 5419963627002664262503139)
          ·
            refine ⟨8129945440503996393754709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5419963627002664262503139 8129945440503996393754709)
            ·
              refine ⟨95272798130906207739313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 8129945440503996393754709 95272798130906207739313)
              ·
                refine ⟨71454598598179655804485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95272798130906207739313 71454598598179655804485)
                ·
                  refine ⟨13397737237158685463341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71454598598179655804485 13397737237158685463341)
                  ·
                    rfl

theorem cell21_58707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 4].length) (baseStart_58707 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_58707 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_58707 prefixEnd_58707 := by exact prefixLift 58707
  have htrace : WordTrace (prefixWord ++ tailWord_58707) baseStart_58707 baseEnd_58707 := by
    simpa [prefixWord, tailWord_58707, baseEnd_58707] using wordTrace_append hprefix tailTrace_58707
  have hstable : (prefixWord ++ tailWord_58707).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58707).length < 2 ^ (prefixWord ++ tailWord_58707).sum := by decide
  have hdescent : baseEnd_58707 < baseStart_58707 := by decide
  rcases family_descends (prefixWord ++ tailWord_58707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58738 : List Nat := [3, 2, 1, 2, 1, 2, 5, 5]
def baseStart_58738 : Nat := 118140960795 + 58738 * 2 ^ 59
def prefixEnd_58738 : Nat := 4983230072969 + 3 ^ 40 * 58738 * 2
def baseEnd_58738 : Nat := 4468270619836506815537

theorem tailTrace_58738 : CollatzResearch.WordTrace tailWord_58738 prefixEnd_58738 4468270619836506815537 := by
  unfold tailWord_58738
  simp only [CollatzResearch.WordTrace]
  refine ⟨535587715302433124212217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1428233907473154997899245 535587715302433124212217)
  ·
    refine ⟨401690786476824843159163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 535587715302433124212217 401690786476824843159163)
    ·
      refine ⟨602536179715237264738745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401690786476824843159163 602536179715237264738745)
      ·
        refine ⟨451902134786427948554059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 602536179715237264738745 451902134786427948554059)
        ·
          refine ⟨677853202179641922831089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451902134786427948554059 677853202179641922831089)
          ·
            refine ⟨508389901634731442123317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 677853202179641922831089 508389901634731442123317)
            ·
              refine ⟨47661553278256072699061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 508389901634731442123317 47661553278256072699061)
              ·
                refine ⟨4468270619836506815537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47661553278256072699061 4468270619836506815537)
                ·
                  rfl

theorem cell21_58738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 5].length) (baseStart_58738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_58738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_58738 prefixEnd_58738 := by exact prefixLift 58738
  have htrace : WordTrace (prefixWord ++ tailWord_58738) baseStart_58738 baseEnd_58738 := by
    simpa [prefixWord, tailWord_58738, baseEnd_58738] using wordTrace_append hprefix tailTrace_58738
  have hstable : (prefixWord ++ tailWord_58738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58738).length < 2 ^ (prefixWord ++ tailWord_58738).sum := by decide
  have hdescent : baseEnd_58738 < baseStart_58738 := by decide
  rcases family_descends (prefixWord ++ tailWord_58738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58890 : List Nat := [3, 1, 2, 2, 2, 4, 1, 6]
def baseStart_58890 : Nat := 118140960795 + 58890 * 2 ^ 59
def prefixEnd_58890 : Nat := 4983230072969 + 3 ^ 40 * 58890 * 2
def baseEnd_58890 : Nat := 4479833443463677970989

theorem tailTrace_58890 : CollatzResearch.WordTrace tailWord_58890 prefixEnd_58890 4479833443463677970989 := by
  unfold tailWord_58890
  simp only [CollatzResearch.WordTrace]
  refine ⟨536973689164765614095531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1431929837772708304254749 536973689164765614095531)
  ·
    refine ⟨805460533747148421143297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 536973689164765614095531 805460533747148421143297)
    ·
      refine ⟨604095400310361315857473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 805460533747148421143297 604095400310361315857473)
      ·
        refine ⟨453071550232770986893105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 604095400310361315857473 453071550232770986893105)
        ·
          refine ⟨339803662674578240169829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453071550232770986893105 339803662674578240169829)
          ·
            refine ⟨63713186751483420031843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 339803662674578240169829 63713186751483420031843)
            ·
              refine ⟨95569780127225130047765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63713186751483420031843 95569780127225130047765)
              ·
                refine ⟨4479833443463677970989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95569780127225130047765 4479833443463677970989)
                ·
                  rfl

theorem cell21_58890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 6].length) (baseStart_58890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_58890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_58890 prefixEnd_58890 := by exact prefixLift 58890
  have htrace : WordTrace (prefixWord ++ tailWord_58890) baseStart_58890 baseEnd_58890 := by
    simpa [prefixWord, tailWord_58890, baseEnd_58890] using wordTrace_append hprefix tailTrace_58890
  have hstable : (prefixWord ++ tailWord_58890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58890).length < 2 ^ (prefixWord ++ tailWord_58890).sum := by decide
  have hdescent : baseEnd_58890 < baseStart_58890 := by decide
  rcases family_descends (prefixWord ++ tailWord_58890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58935 : List Nat := [1, 1, 3, 1, 2, 4, 3, 2, 4]
def baseStart_58935 : Nat := 118140960795 + 58935 * 2 ^ 59
def prefixEnd_58935 : Nat := 4983230072969 + 3 ^ 40 * 58935 * 2
def baseEnd_58935 : Nat := 13449769943480955662875

theorem tailTrace_58935 : CollatzResearch.WordTrace tailWord_58935 prefixEnd_58935 13449769943480955662875 := by
  unfold tailWord_58935
  simp only [CollatzResearch.WordTrace]
  refine ⟨2149536041496035141770259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1433024027664023427846839 2149536041496035141770259)
  ·
    refine ⟨3224304062244052712655389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2149536041496035141770259 3224304062244052712655389)
    ·
      refine ⟨1209114023341519767245771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3224304062244052712655389 1209114023341519767245771)
      ·
        refine ⟨1813671035012279650868657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1209114023341519767245771 1813671035012279650868657)
        ·
          refine ⟨1360253276259209738151493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1813671035012279650868657 1360253276259209738151493)
          ·
            refine ⟨255047489298601825903405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1360253276259209738151493 255047489298601825903405)
            ·
              refine ⟨95642808486975684713777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255047489298601825903405 95642808486975684713777)
              ·
                refine ⟨71732106365231763535333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95642808486975684713777 71732106365231763535333)
                ·
                  refine ⟨13449769943480955662875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71732106365231763535333 13449769943480955662875)
                  ·
                    rfl

theorem cell21_58935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 4].length) (baseStart_58935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_58935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_58935 prefixEnd_58935 := by exact prefixLift 58935
  have htrace : WordTrace (prefixWord ++ tailWord_58935) baseStart_58935 baseEnd_58935 := by
    simpa [prefixWord, tailWord_58935, baseEnd_58935] using wordTrace_append hprefix tailTrace_58935
  have hstable : (prefixWord ++ tailWord_58935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58935).length < 2 ^ (prefixWord ++ tailWord_58935).sum := by decide
  have hdescent : baseEnd_58935 < baseStart_58935 := by decide
  rcases family_descends (prefixWord ++ tailWord_58935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58997 : List Nat := [1, 3, 4, 2, 1, 1, 3, 1, 5]
def baseStart_58997 : Nat := 118140960795 + 58997 * 2 ^ 59
def prefixEnd_58997 : Nat := 4983230072969 + 3 ^ 40 * 58997 * 2
def baseEnd_58997 : Nat := 13463919188182625629415

theorem tailTrace_58997 : CollatzResearch.WordTrace tailWord_58997 prefixEnd_58997 13463919188182625629415 := by
  unfold tailWord_58997
  simp only [CollatzResearch.WordTrace]
  refine ⟨2151797367271419730527245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1434531578180946487018163 2151797367271419730527245)
  ·
    refine ⟨806924012726782398947717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2151797367271419730527245 806924012726782398947717)
    ·
      refine ⟨151298252386271699802697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 806924012726782398947717 151298252386271699802697)
      ·
        refine ⟨113473689289703774852023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151298252386271699802697 113473689289703774852023)
        ·
          refine ⟨170210533934555662278035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113473689289703774852023 170210533934555662278035)
          ·
            refine ⟨255315800901833493417053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170210533934555662278035 255315800901833493417053)
            ·
              refine ⟨95743425338187560031395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255315800901833493417053 95743425338187560031395)
              ·
                refine ⟨143615138007281340047093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95743425338187560031395 143615138007281340047093)
                ·
                  refine ⟨13463919188182625629415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143615138007281340047093 13463919188182625629415)
                  ·
                    rfl

theorem cell21_58997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_58997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_58997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_58997 prefixEnd_58997 := by exact prefixLift 58997
  have htrace : WordTrace (prefixWord ++ tailWord_58997) baseStart_58997 baseEnd_58997 := by
    simpa [prefixWord, tailWord_58997, baseEnd_58997] using wordTrace_append hprefix tailTrace_58997
  have hstable : (prefixWord ++ tailWord_58997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58997).length < 2 ^ (prefixWord ++ tailWord_58997).sum := by decide
  have hdescent : baseEnd_58997 < baseStart_58997 := by decide
  rcases family_descends (prefixWord ++ tailWord_58997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59042 : List Nat := [3, 3, 1, 4, 1, 9]
def baseStart_59042 : Nat := 118140960795 + 59042 * 2 ^ 59
def prefixEnd_59042 : Nat := 4983230072969 + 3 ^ 40 * 59042 * 2
def baseEnd_59042 : Nat := 499044029676761014049

theorem tailTrace_59042 : CollatzResearch.WordTrace tailWord_59042 prefixEnd_59042 499044029676761014049 := by
  unfold tailWord_59042
  simp only [CollatzResearch.WordTrace]
  refine ⟨538359663027098103978845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1435625768072261610610253 538359663027098103978845)
  ·
    refine ⟨201884873635161788992067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 538359663027098103978845 201884873635161788992067)
    ·
      refine ⟨302827310452742683488101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201884873635161788992067 302827310452742683488101)
      ·
        refine ⟨56780120709889253154019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 302827310452742683488101 56780120709889253154019)
        ·
          refine ⟨85170181064833879731029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56780120709889253154019 85170181064833879731029)
          ·
            refine ⟨499044029676761014049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 85170181064833879731029 499044029676761014049)
            ·
              rfl

theorem cell21_59042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 9].length) (baseStart_59042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_59042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_59042 prefixEnd_59042 := by exact prefixLift 59042
  have htrace : WordTrace (prefixWord ++ tailWord_59042) baseStart_59042 baseEnd_59042 := by
    simpa [prefixWord, tailWord_59042, baseEnd_59042] using wordTrace_append hprefix tailTrace_59042
  have hstable : (prefixWord ++ tailWord_59042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59042).length < 2 ^ (prefixWord ++ tailWord_59042).sum := by decide
  have hdescent : baseEnd_59042 < baseStart_59042 := by decide
  rcases family_descends (prefixWord ++ tailWord_59042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59048 : List Nat := [2, 1, 7, 1, 1, 1, 1, 4, 3]
def baseStart_59048 : Nat := 118140960795 + 59048 * 2 ^ 59
def prefixEnd_59048 : Nat := 4983230072969 + 3 ^ 40 * 59048 * 2
def baseEnd_59048 : Nat := 13475558083017870279311

theorem tailTrace_59048 : CollatzResearch.WordTrace tailWord_59048 prefixEnd_59048 13475558083017870279311 := by
  unfold tailWord_59048
  simp only [CollatzResearch.WordTrace]
  refine ⟨1076828745043327720316899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1435771660057770293755865 1076828745043327720316899)
  ·
    refine ⟨1615243117564991580475349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1076828745043327720316899 1615243117564991580475349)
    ·
      refine ⟨37857260567929490167391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 1615243117564991580475349 37857260567929490167391)
      ·
        refine ⟨56785890851894235251087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37857260567929490167391 56785890851894235251087)
        ·
          refine ⟨85178836277841352876631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56785890851894235251087 85178836277841352876631)
          ·
            refine ⟨127768254416762029314947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85178836277841352876631 127768254416762029314947)
            ·
              refine ⟨191652381625143043972421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127768254416762029314947 191652381625143043972421)
              ·
                refine ⟨35934821554714320744829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191652381625143043972421 35934821554714320744829)
                ·
                  refine ⟨13475558083017870279311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35934821554714320744829 13475558083017870279311)
                  ·
                    rfl

theorem cell21_59048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 4, 3].length) (baseStart_59048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_59048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_59048 prefixEnd_59048 := by exact prefixLift 59048
  have htrace : WordTrace (prefixWord ++ tailWord_59048) baseStart_59048 baseEnd_59048 := by
    simpa [prefixWord, tailWord_59048, baseEnd_59048] using wordTrace_append hprefix tailTrace_59048
  have hstable : (prefixWord ++ tailWord_59048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59048).length < 2 ^ (prefixWord ++ tailWord_59048).sum := by decide
  have hdescent : baseEnd_59048 < baseStart_59048 := by decide
  rcases family_descends (prefixWord ++ tailWord_59048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59090 : List Nat := [3, 2, 2, 2, 2, 2, 2, 3, 3]
def baseStart_59090 : Nat := 118140960795 + 59090 * 2 ^ 59
def prefixEnd_59090 : Nat := 4983230072969 + 3 ^ 40 * 59090 * 2
def baseEnd_59090 : Nat := 13485143055235130579225

theorem tailTrace_59090 : CollatzResearch.WordTrace tailWord_59090 prefixEnd_59090 13485143055235130579225 := by
  unfold tailWord_59090
  simp only [CollatzResearch.WordTrace]
  refine ⟨538797338983624153415681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1436792903956331075775149 538797338983624153415681)
  ·
    refine ⟨404098004237718115061761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 538797338983624153415681 404098004237718115061761)
    ·
      refine ⟨303073503178288586296321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404098004237718115061761 303073503178288586296321)
      ·
        refine ⟨227305127383716439722241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303073503178288586296321 227305127383716439722241)
        ·
          refine ⟨170478845537787329791681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227305127383716439722241 170478845537787329791681)
          ·
            refine ⟨127859134153340497343761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170478845537787329791681 127859134153340497343761)
            ·
              refine ⟨95894350615005373007821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127859134153340497343761 95894350615005373007821)
              ·
                refine ⟨35960381480627014877933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95894350615005373007821 35960381480627014877933)
                ·
                  refine ⟨13485143055235130579225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35960381480627014877933 13485143055235130579225)
                  ·
                    rfl

theorem cell21_59090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_59090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_59090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_59090 prefixEnd_59090 := by exact prefixLift 59090
  have htrace : WordTrace (prefixWord ++ tailWord_59090) baseStart_59090 baseEnd_59090 := by
    simpa [prefixWord, tailWord_59090, baseEnd_59090] using wordTrace_append hprefix tailTrace_59090
  have hstable : (prefixWord ++ tailWord_59090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59090).length < 2 ^ (prefixWord ++ tailWord_59090).sum := by decide
  have hdescent : baseEnd_59090 < baseStart_59090 := by decide
  rcases family_descends (prefixWord ++ tailWord_59090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59115 : List Nat := [1, 1, 1, 1, 2, 4, 3, 3, 5]
def baseStart_59115 : Nat := 118140960795 + 59115 * 2 ^ 59
def prefixEnd_59115 : Nat := 4983230072969 + 3 ^ 40 * 59115 * 2
def baseEnd_59115 : Nat := 13490848395840642662507

theorem tailTrace_59115 : CollatzResearch.WordTrace tailWord_59115 prefixEnd_59115 13490848395840642662507 := by
  unfold tailWord_59115
  simp only [CollatzResearch.WordTrace]
  refine ⟨2156101180843925883322799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1437400787229283922215199 2156101180843925883322799)
  ·
    refine ⟨3234151771265888824984199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2156101180843925883322799 3234151771265888824984199)
    ·
      refine ⟨4851227656898833237476299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3234151771265888824984199 4851227656898833237476299)
      ·
        refine ⟨7276841485348249856214449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4851227656898833237476299 7276841485348249856214449)
        ·
          refine ⟨5457631114011187392160837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7276841485348249856214449 5457631114011187392160837)
          ·
            refine ⟨1023305833877097636030157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5457631114011187392160837 1023305833877097636030157)
            ·
              refine ⟨383739687703911613511309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1023305833877097636030157 383739687703911613511309)
              ·
                refine ⟨143902382888966855066741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 383739687703911613511309 143902382888966855066741)
                ·
                  refine ⟨13490848395840642662507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143902382888966855066741 13490848395840642662507)
                  ·
                    rfl

theorem cell21_59115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 5].length) (baseStart_59115 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_59115 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_59115 prefixEnd_59115 := by exact prefixLift 59115
  have htrace : WordTrace (prefixWord ++ tailWord_59115) baseStart_59115 baseEnd_59115 := by
    simpa [prefixWord, tailWord_59115, baseEnd_59115] using wordTrace_append hprefix tailTrace_59115
  have hstable : (prefixWord ++ tailWord_59115).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59115).length < 2 ^ (prefixWord ++ tailWord_59115).sum := by decide
  have hdescent : baseEnd_59115 < baseStart_59115 := by decide
  rcases family_descends (prefixWord ++ tailWord_59115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59146 : List Nat := [3, 1, 2, 2, 1, 3, 1, 2, 6]
def baseStart_59146 : Nat := 118140960795 + 59146 * 2 ^ 59
def prefixEnd_59146 : Nat := 4983230072969 + 3 ^ 40 * 59146 * 2
def baseEnd_59146 : Nat := 13497923018191477645777

theorem tailTrace_59146 : CollatzResearch.WordTrace tailWord_59146 prefixEnd_59146 13497923018191477645777 := by
  unfold tailWord_59146
  simp only [CollatzResearch.WordTrace]
  refine ⟨539307960932904544425323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1438154562487745451800861 539307960932904544425323)
  ·
    refine ⟨808961941399356816637985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 539307960932904544425323 808961941399356816637985)
    ·
      refine ⟨606721456049517612478489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 808961941399356816637985 606721456049517612478489)
      ·
        refine ⟨455041092037138209358867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 606721456049517612478489 455041092037138209358867)
        ·
          refine ⟨682561638055707314038301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455041092037138209358867 682561638055707314038301)
          ·
            refine ⟨255960614270890242764363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 682561638055707314038301 255960614270890242764363)
            ·
              refine ⟨383940921406335364146545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255960614270890242764363 383940921406335364146545)
              ·
                refine ⟨287955691054751523109909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 383940921406335364146545 287955691054751523109909)
                ·
                  refine ⟨13497923018191477645777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 287955691054751523109909 13497923018191477645777)
                  ·
                    rfl

theorem cell21_59146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_59146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_59146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_59146 prefixEnd_59146 := by exact prefixLift 59146
  have htrace : WordTrace (prefixWord ++ tailWord_59146) baseStart_59146 baseEnd_59146 := by
    simpa [prefixWord, tailWord_59146, baseEnd_59146] using wordTrace_append hprefix tailTrace_59146
  have hstable : (prefixWord ++ tailWord_59146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59146).length < 2 ^ (prefixWord ++ tailWord_59146).sum := by decide
  have hdescent : baseEnd_59146 < baseStart_59146 := by decide
  rcases family_descends (prefixWord ++ tailWord_59146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59160 : List Nat := [2, 1, 2, 3, 1, 1, 11]
def baseStart_59160 : Nat := 118140960795 + 59160 * 2 ^ 59
def prefixEnd_59160 : Nat := 4983230072969 + 3 ^ 40 * 59160 * 2
def baseEnd_59160 : Nat := 1500124223214507156935

theorem tailTrace_59160 : CollatzResearch.WordTrace tailWord_59160 prefixEnd_59160 1500124223214507156935 := by
  unfold tailWord_59160
  simp only [CollatzResearch.WordTrace]
  refine ⟨1078871232840449284355467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1438494977120599045807289 1078871232840449284355467)
  ·
    refine ⟨1618306849260673926533201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1078871232840449284355467 1618306849260673926533201)
    ·
      refine ⟨1213730136945505444899901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1618306849260673926533201 1213730136945505444899901)
      ·
        refine ⟨455148801354564541837463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1213730136945505444899901 455148801354564541837463)
        ·
          refine ⟨682723202031846812756195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455148801354564541837463 682723202031846812756195)
          ·
            refine ⟨1024084803047770219134293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682723202031846812756195 1024084803047770219134293)
            ·
              refine ⟨1500124223214507156935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 1024084803047770219134293 1500124223214507156935)
              ·
                rfl

theorem cell21_59160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 11].length) (baseStart_59160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_59160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_59160 prefixEnd_59160 := by exact prefixLift 59160
  have htrace : WordTrace (prefixWord ++ tailWord_59160) baseStart_59160 baseEnd_59160 := by
    simpa [prefixWord, tailWord_59160, baseEnd_59160] using wordTrace_append hprefix tailTrace_59160
  have hstable : (prefixWord ++ tailWord_59160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59160).length < 2 ^ (prefixWord ++ tailWord_59160).sum := by decide
  have hdescent : baseEnd_59160 < baseStart_59160 := by decide
  rcases family_descends (prefixWord ++ tailWord_59160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59180 : List Nat := [2, 2, 1, 1, 1, 7, 2, 1, 4]
def baseStart_59180 : Nat := 118140960795 + 59180 * 2 ^ 59
def prefixEnd_59180 : Nat := 4983230072969 + 3 ^ 40 * 59180 * 2
def baseEnd_59180 : Nat := 13505682281414974079041

theorem tailTrace_59180 : CollatzResearch.WordTrace tailWord_59180 prefixEnd_59180 13505682281414974079041 := by
  unfold tailWord_59180
  simp only [CollatzResearch.WordTrace]
  refine ⟨1079235962804220992219497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1438981283738961322959329 1079235962804220992219497)
  ·
    refine ⟨809426972103165744164623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1079235962804220992219497 809426972103165744164623)
    ·
      refine ⟨1214140458154748616246935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 809426972103165744164623 1214140458154748616246935)
      ·
        refine ⟨1821210687232122924370403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1214140458154748616246935 1821210687232122924370403)
        ·
          refine ⟨2731816030848184386555605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1821210687232122924370403 2731816030848184386555605)
          ·
            refine ⟨64026938223004321559897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 2731816030848184386555605 64026938223004321559897)
            ·
              refine ⟨48020203667253241169923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64026938223004321559897 48020203667253241169923)
              ·
                refine ⟨72030305500879861754885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48020203667253241169923 72030305500879861754885)
                ·
                  refine ⟨13505682281414974079041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72030305500879861754885 13505682281414974079041)
                  ·
                    rfl

theorem cell21_59180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_59180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_59180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_59180 prefixEnd_59180 := by exact prefixLift 59180
  have htrace : WordTrace (prefixWord ++ tailWord_59180) baseStart_59180 baseEnd_59180 := by
    simpa [prefixWord, tailWord_59180, baseEnd_59180] using wordTrace_append hprefix tailTrace_59180
  have hstable : (prefixWord ++ tailWord_59180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59180).length < 2 ^ (prefixWord ++ tailWord_59180).sum := by decide
  have hdescent : baseEnd_59180 < baseStart_59180 := by decide
  rcases family_descends (prefixWord ++ tailWord_59180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59284 : List Nat := [2, 4, 2, 1, 1, 2, 1, 3, 5]
def baseStart_59284 : Nat := 118140960795 + 59284 * 2 ^ 59
def prefixEnd_59284 : Nat := 4983230072969 + 3 ^ 40 * 59284 * 2
def baseEnd_59284 : Nat := 13529416498333904345495

theorem tailTrace_59284 : CollatzResearch.WordTrace tailWord_59284 prefixEnd_59284 13529416498333904345495 := by
  unfold tailWord_59284
  simp only [CollatzResearch.WordTrace]
  refine ⟨1081132558615833873112453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1441510078154445164149937 1081132558615833873112453)
  ·
    refine ⟨202712354740468851208585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1081132558615833873112453 202712354740468851208585)
    ·
      refine ⟨152034266055351638406439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202712354740468851208585 152034266055351638406439)
      ·
        refine ⟨228051399083027457609659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152034266055351638406439 228051399083027457609659)
        ·
          refine ⟨342077098624541186414489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228051399083027457609659 342077098624541186414489)
          ·
            refine ⟨256557823968405889810867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342077098624541186414489 256557823968405889810867)
            ·
              refine ⟨384836735952608834716301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256557823968405889810867 384836735952608834716301)
              ·
                refine ⟨144313775982228313018613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 384836735952608834716301 144313775982228313018613)
                ·
                  refine ⟨13529416498333904345495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144313775982228313018613 13529416498333904345495)
                  ·
                    rfl

theorem cell21_59284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_59284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_59284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_59284 prefixEnd_59284 := by exact prefixLift 59284
  have htrace : WordTrace (prefixWord ++ tailWord_59284) baseStart_59284 baseEnd_59284 := by
    simpa [prefixWord, tailWord_59284, baseEnd_59284] using wordTrace_append hprefix tailTrace_59284
  have hstable : (prefixWord ++ tailWord_59284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59284).length < 2 ^ (prefixWord ++ tailWord_59284).sum := by decide
  have hdescent : baseEnd_59284 < baseStart_59284 := by decide
  rcases family_descends (prefixWord ++ tailWord_59284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59304 : List Nat := [2, 1, 6, 2, 1, 2, 2, 5]
def baseStart_59304 : Nat := 118140960795 + 59304 * 2 ^ 59
def prefixEnd_59304 : Nat := 4983230072969 + 3 ^ 40 * 59304 * 2
def baseEnd_59304 : Nat := 4511326923606104670707

theorem tailTrace_59304 : CollatzResearch.WordTrace tailWord_59304 prefixEnd_59304 4511326923606104670707 := by
  unfold tailWord_59304
  simp only [CollatzResearch.WordTrace]
  refine ⟨1081497288579605580976483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1441996384772807441301977 1081497288579605580976483)
  ·
    refine ⟨1622245932869408371464725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1081497288579605580976483 1622245932869408371464725)
    ·
      refine ⟨76042778103253517412409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1622245932869408371464725 76042778103253517412409)
      ·
        refine ⟨57032083577440138059307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76042778103253517412409 57032083577440138059307)
        ·
          refine ⟨85548125366160207088961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57032083577440138059307 85548125366160207088961)
          ·
            refine ⟨64161094024620155316721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85548125366160207088961 64161094024620155316721)
            ·
              refine ⟨48120820518465116487541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64161094024620155316721 48120820518465116487541)
              ·
                refine ⟨4511326923606104670707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48120820518465116487541 4511326923606104670707)
                ·
                  rfl

theorem cell21_59304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 5].length) (baseStart_59304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_59304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_59304 prefixEnd_59304 := by exact prefixLift 59304
  have htrace : WordTrace (prefixWord ++ tailWord_59304) baseStart_59304 baseEnd_59304 := by
    simpa [prefixWord, tailWord_59304, baseEnd_59304] using wordTrace_append hprefix tailTrace_59304
  have hstable : (prefixWord ++ tailWord_59304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59304).length < 2 ^ (prefixWord ++ tailWord_59304).sum := by decide
  have hdescent : baseEnd_59304 < baseStart_59304 := by decide
  rcases family_descends (prefixWord ++ tailWord_59304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59346 : List Nat := [3, 2, 2, 3, 2, 1, 2, 6]
def baseStart_59346 : Nat := 118140960795 + 59346 * 2 ^ 59
def prefixEnd_59346 : Nat := 4983230072969 + 3 ^ 40 * 59346 * 2
def baseEnd_59346 : Nat := 4514521914345191437345

theorem tailTrace_59346 : CollatzResearch.WordTrace tailWord_59346 prefixEnd_59346 4514521914345191437345 := by
  unfold tailWord_59346
  simp only [CollatzResearch.WordTrace]
  refine ⟨541131610751763083745473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1443017628671368223321261 541131610751763083745473)
  ·
    refine ⟨405848708063822312809105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 541131610751763083745473 405848708063822312809105)
    ·
      refine ⟨304386531047866734606829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405848708063822312809105 304386531047866734606829)
      ·
        refine ⟨114144949142950025477561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304386531047866734606829 114144949142950025477561)
        ·
          refine ⟨85608711857212519108171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114144949142950025477561 85608711857212519108171)
          ·
            refine ⟨128413067785818778662257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85608711857212519108171 128413067785818778662257)
            ·
              refine ⟨96309800839364083996693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128413067785818778662257 96309800839364083996693)
              ·
                refine ⟨4514521914345191437345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96309800839364083996693 4514521914345191437345)
                ·
                  rfl

theorem cell21_59346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 6].length) (baseStart_59346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_59346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_59346 prefixEnd_59346 := by exact prefixLift 59346
  have htrace : WordTrace (prefixWord ++ tailWord_59346) baseStart_59346 baseEnd_59346 := by
    simpa [prefixWord, tailWord_59346, baseEnd_59346] using wordTrace_append hprefix tailTrace_59346
  have hstable : (prefixWord ++ tailWord_59346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59346).length < 2 ^ (prefixWord ++ tailWord_59346).sum := by decide
  have hdescent : baseEnd_59346 < baseStart_59346 := by decide
  rcases family_descends (prefixWord ++ tailWord_59346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59498 : List Nat := [3, 1, 3, 2, 4, 1, 7]
def baseStart_59498 : Nat := 118140960795 + 59498 * 2 ^ 59
def prefixEnd_59498 : Nat := 4983230072969 + 3 ^ 40 * 59498 * 2
def baseEnd_59498 : Nat := 1508694912657454197599

theorem tailTrace_59498 : CollatzResearch.WordTrace tailWord_59498 prefixEnd_59498 1508694912657454197599 := by
  unfold tailWord_59498
  simp only [CollatzResearch.WordTrace]
  refine ⟨542517584614095573628787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1446713558970921529676765 542517584614095573628787)
  ·
    refine ⟨813776376921143360443181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 542517584614095573628787 813776376921143360443181)
    ·
      refine ⟨305166141345428760166193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 813776376921143360443181 305166141345428760166193)
      ·
        refine ⟨228874606009071570124645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305166141345428760166193 228874606009071570124645)
        ·
          refine ⟨42913988626700919398371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228874606009071570124645 42913988626700919398371)
          ·
            refine ⟨64370982940051379097557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42913988626700919398371 64370982940051379097557)
            ·
              refine ⟨1508694912657454197599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 64370982940051379097557 1508694912657454197599)
              ·
                rfl

theorem cell21_59498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 7].length) (baseStart_59498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_59498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_59498 prefixEnd_59498 := by exact prefixLift 59498
  have htrace : WordTrace (prefixWord ++ tailWord_59498) baseStart_59498 baseEnd_59498 := by
    simpa [prefixWord, tailWord_59498, baseEnd_59498] using wordTrace_append hprefix tailTrace_59498
  have hstable : (prefixWord ++ tailWord_59498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59498).length < 2 ^ (prefixWord ++ tailWord_59498).sum := by decide
  have hdescent : baseEnd_59498 < baseStart_59498 := by decide
  rcases family_descends (prefixWord ++ tailWord_59498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59588 : List Nat := [2, 3, 3, 1, 2, 2, 1, 2, 5]
def baseStart_59588 : Nat := 118140960795 + 59588 * 2 ^ 59
def prefixEnd_59588 : Nat := 4983230072969 + 3 ^ 40 * 59588 * 2
def baseEnd_59588 : Nat := 13598793440096931278207

theorem tailTrace_59588 : CollatzResearch.WordTrace tailWord_59588 prefixEnd_59588 13598793440096931278207 := by
  unfold tailWord_59588
  simp only [CollatzResearch.WordTrace]
  refine ⟨1086676454065163832645709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1448901938753551776860945 1086676454065163832645709)
  ·
    refine ⟨407503670274436437242141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1086676454065163832645709 407503670274436437242141)
    ·
      refine ⟨152813876352913663965803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407503670274436437242141 152813876352913663965803)
      ·
        refine ⟨229220814529370495948705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152813876352913663965803 229220814529370495948705)
        ·
          refine ⟨171915610897027871961529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229220814529370495948705 171915610897027871961529)
          ·
            refine ⟨128936708172770903971147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171915610897027871961529 128936708172770903971147)
            ·
              refine ⟨193405062259156355956721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128936708172770903971147 193405062259156355956721)
              ·
                refine ⟨145053796694367266967541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193405062259156355956721 145053796694367266967541)
                ·
                  refine ⟨13598793440096931278207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 145053796694367266967541 13598793440096931278207)
                  ·
                    rfl

theorem cell21_59588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_59588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_59588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_59588 prefixEnd_59588 := by exact prefixLift 59588
  have htrace : WordTrace (prefixWord ++ tailWord_59588) baseStart_59588 baseEnd_59588 := by
    simpa [prefixWord, tailWord_59588, baseEnd_59588] using wordTrace_append hprefix tailTrace_59588
  have hstable : (prefixWord ++ tailWord_59588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59588).length < 2 ^ (prefixWord ++ tailWord_59588).sum := by decide
  have hdescent : baseEnd_59588 < baseStart_59588 := by decide
  rcases family_descends (prefixWord ++ tailWord_59588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59619 : List Nat := [1, 1, 1, 8, 1, 1, 1, 1, 6]
def baseStart_59619 : Nat := 118140960795 + 59619 * 2 ^ 59
def prefixEnd_59619 : Nat := 4983230072969 + 3 ^ 40 * 59619 * 2
def baseEnd_59619 : Nat := 13605868062447766261477

theorem tailTrace_59619 : CollatzResearch.WordTrace tailWord_59619 prefixEnd_59619 13605868062447766261477 := by
  unfold tailWord_59619
  simp only [CollatzResearch.WordTrace]
  refine ⟨2174483571018019959669911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1449655714012013306446607 2174483571018019959669911)
  ·
    refine ⟨3261725356527029939504867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2174483571018019959669911 3261725356527029939504867)
    ·
      refine ⟨4892588034790544909257301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3261725356527029939504867 4892588034790544909257301)
      ·
        refine ⟨57335016032701698155359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 4892588034790544909257301 57335016032701698155359)
        ·
          refine ⟨86002524049052547233039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57335016032701698155359 86002524049052547233039)
          ·
            refine ⟨129003786073578820849559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86002524049052547233039 129003786073578820849559)
            ·
              refine ⟨193505679110368231274339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129003786073578820849559 193505679110368231274339)
              ·
                refine ⟨290258518665552346911509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193505679110368231274339 290258518665552346911509)
                ·
                  refine ⟨13605868062447766261477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 290258518665552346911509 13605868062447766261477)
                  ·
                    rfl

theorem cell21_59619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 6].length) (baseStart_59619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_59619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_59619 prefixEnd_59619 := by exact prefixLift 59619
  have htrace : WordTrace (prefixWord ++ tailWord_59619) baseStart_59619 baseEnd_59619 := by
    simpa [prefixWord, tailWord_59619, baseEnd_59619] using wordTrace_append hprefix tailTrace_59619
  have hstable : (prefixWord ++ tailWord_59619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59619).length < 2 ^ (prefixWord ++ tailWord_59619).sum := by decide
  have hdescent : baseEnd_59619 < baseStart_59619 := by decide
  rcases family_descends (prefixWord ++ tailWord_59619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59650 : List Nat := [3, 4, 1, 1, 2, 1, 4, 5]
def baseStart_59650 : Nat := 118140960795 + 59650 * 2 ^ 59
def prefixEnd_59650 : Nat := 4983230072969 + 3 ^ 40 * 59650 * 2
def baseEnd_59650 : Nat := 4537647561599533748249

theorem tailTrace_59650 : CollatzResearch.WordTrace tailWord_59650 prefixEnd_59650 4537647561599533748249 := by
  unfold tailWord_59650
  simp only [CollatzResearch.WordTrace]
  refine ⟨543903558476428063512101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1450409489270474836032269 543903558476428063512101)
  ·
    refine ⟨101981917214330261908519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 543903558476428063512101 101981917214330261908519)
    ·
      refine ⟨152972875821495392862779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101981917214330261908519 152972875821495392862779)
      ·
        refine ⟨229459313732243089294169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152972875821495392862779 229459313732243089294169)
        ·
          refine ⟨172094485299182316970627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229459313732243089294169 172094485299182316970627)
          ·
            refine ⟨258141727948773475455941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172094485299182316970627 258141727948773475455941)
            ·
              refine ⟨48401573990395026647989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 258141727948773475455941 48401573990395026647989)
              ·
                refine ⟨4537647561599533748249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48401573990395026647989 4537647561599533748249)
                ·
                  rfl

theorem cell21_59650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 5].length) (baseStart_59650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_59650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_59650 prefixEnd_59650 := by exact prefixLift 59650
  have htrace : WordTrace (prefixWord ++ tailWord_59650) baseStart_59650 baseEnd_59650 := by
    simpa [prefixWord, tailWord_59650, baseEnd_59650] using wordTrace_append hprefix tailTrace_59650
  have hstable : (prefixWord ++ tailWord_59650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59650).length < 2 ^ (prefixWord ++ tailWord_59650).sum := by decide
  have hdescent : baseEnd_59650 < baseStart_59650 := by decide
  rcases family_descends (prefixWord ++ tailWord_59650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59675 : List Nat := [1, 1, 1, 1, 1, 1, 15]
def baseStart_59675 : Nat := 118140960795 + 59675 * 2 ^ 59
def prefixEnd_59675 : Nat := 4983230072969 + 3 ^ 40 * 59675 * 2
def baseEnd_59675 : Nat := 1513183113933790369781

theorem tailTrace_59675 : CollatzResearch.WordTrace tailWord_59675 prefixEnd_59675 1513183113933790369781 := by
  unfold tailWord_59675
  simp only [CollatzResearch.WordTrace]
  refine ⟨2176526058815141523708479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1451017372543427682472319 2176526058815141523708479)
  ·
    refine ⟨3264789088222712285562719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2176526058815141523708479 3264789088222712285562719)
    ·
      refine ⟨4897183632334068428344079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3264789088222712285562719 4897183632334068428344079)
      ·
        refine ⟨7345775448501102642516119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4897183632334068428344079 7345775448501102642516119)
        ·
          refine ⟨11018663172751653963774179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7345775448501102642516119 11018663172751653963774179)
          ·
            refine ⟨16527994759127480945661269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11018663172751653963774179 16527994759127480945661269)
            ·
              refine ⟨1513183113933790369781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 15 16527994759127480945661269 1513183113933790369781)
              ·
                rfl

theorem cell21_59675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 15].length) (baseStart_59675 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_59675 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_59675 prefixEnd_59675 := by exact prefixLift 59675
  have htrace : WordTrace (prefixWord ++ tailWord_59675) baseStart_59675 baseEnd_59675 := by
    simpa [prefixWord, tailWord_59675, baseEnd_59675] using wordTrace_append hprefix tailTrace_59675
  have hstable : (prefixWord ++ tailWord_59675).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59675).length < 2 ^ (prefixWord ++ tailWord_59675).sum := by decide
  have hdescent : baseEnd_59675 < baseStart_59675 := by decide
  rcases family_descends (prefixWord ++ tailWord_59675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59687 : List Nat := [1, 1, 8, 1, 2, 1, 2, 1, 4]
def baseStart_59687 : Nat := 118140960795 + 59687 * 2 ^ 59
def prefixEnd_59687 : Nat := 4983230072969 + 3 ^ 40 * 59687 * 2
def baseEnd_59687 : Nat := 13621386588894759128005

theorem tailTrace_59687 : CollatzResearch.WordTrace tailWord_59687 prefixEnd_59687 13621386588894759128005 := by
  unfold tailWord_59687
  simp only [CollatzResearch.WordTrace]
  refine ⟨2176963734771667573145315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1451309156514445048763543 2176963734771667573145315)
  ·
    refine ⟨3265445602157501359717973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2176963734771667573145315 3265445602157501359717973)
    ·
      refine ⟨38266940650283219059195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 3265445602157501359717973 38266940650283219059195)
      ·
        refine ⟨57400410975424828588793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38266940650283219059195 57400410975424828588793)
        ·
          refine ⟨43050308231568621441595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57400410975424828588793 43050308231568621441595)
          ·
            refine ⟨64575462347352932162393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43050308231568621441595 64575462347352932162393)
            ·
              refine ⟨48431596760514699121795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64575462347352932162393 48431596760514699121795)
              ·
                refine ⟨72647395140772048682693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48431596760514699121795 72647395140772048682693)
                ·
                  refine ⟨13621386588894759128005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72647395140772048682693 13621386588894759128005)
                  ·
                    rfl

theorem cell21_59687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 4].length) (baseStart_59687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_59687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_59687 prefixEnd_59687 := by exact prefixLift 59687
  have htrace : WordTrace (prefixWord ++ tailWord_59687) baseStart_59687 baseEnd_59687 := by
    simpa [prefixWord, tailWord_59687, baseEnd_59687] using wordTrace_append hprefix tailTrace_59687
  have hstable : (prefixWord ++ tailWord_59687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59687).length < 2 ^ (prefixWord ++ tailWord_59687).sum := by decide
  have hdescent : baseEnd_59687 < baseStart_59687 := by decide
  rcases family_descends (prefixWord ++ tailWord_59687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59816 : List Nat := [2, 1, 6, 1, 1, 1, 2, 2, 5]
def baseStart_59816 : Nat := 118140960795 + 59816 * 2 ^ 59
def prefixEnd_59816 : Nat := 4983230072969 + 3 ^ 40 * 59816 * 2
def baseEnd_59816 : Nat := 13650826146419201477741

theorem tailTrace_59816 : CollatzResearch.WordTrace tailWord_59816 prefixEnd_59816 13650826146419201477741 := by
  unfold tailWord_59816
  simp only [CollatzResearch.WordTrace]
  refine ⟨1090834375652161302295651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1454445834202881736394201 1090834375652161302295651)
  ·
    refine ⟨1636251563478241953443477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1090834375652161302295651 1636251563478241953443477)
    ·
      refine ⟨76699292038042591567663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1636251563478241953443477 76699292038042591567663)
      ·
        refine ⟨115048938057063887351495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76699292038042591567663 115048938057063887351495)
        ·
          refine ⟨172573407085595831027243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115048938057063887351495 172573407085595831027243)
          ·
            refine ⟨258860110628393746540865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172573407085595831027243 258860110628393746540865)
            ·
              refine ⟨194145082971295309905649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258860110628393746540865 194145082971295309905649)
              ·
                refine ⟨145608812228471482429237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194145082971295309905649 145608812228471482429237)
                ·
                  refine ⟨13650826146419201477741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 145608812228471482429237 13650826146419201477741)
                  ·
                    rfl

theorem cell21_59816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 5].length) (baseStart_59816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_59816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_59816 prefixEnd_59816 := by exact prefixLift 59816
  have htrace : WordTrace (prefixWord ++ tailWord_59816) baseStart_59816 baseEnd_59816 := by
    simpa [prefixWord, tailWord_59816, baseEnd_59816] using wordTrace_append hprefix tailTrace_59816
  have hstable : (prefixWord ++ tailWord_59816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59816).length < 2 ^ (prefixWord ++ tailWord_59816).sum := by decide
  have hdescent : baseEnd_59816 < baseStart_59816 := by decide
  rcases family_descends (prefixWord ++ tailWord_59816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59833 : List Nat := [1, 2, 1, 4, 3, 3, 1, 3, 3]
def baseStart_59833 : Nat := 118140960795 + 59833 * 2 ^ 59
def prefixEnd_59833 : Nat := 4983230072969 + 3 ^ 40 * 59833 * 2
def baseEnd_59833 : Nat := 13654705778030949694373

theorem tailTrace_59833 : CollatzResearch.WordTrace tailWord_59833 prefixEnd_59833 13654705778030949694373 := by
  unfold tailWord_59833
  simp only [CollatzResearch.WordTrace]
  refine ⟨2182288792242734507960153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1454859194828489671973435 2182288792242734507960153)
  ·
    refine ⟨1636716594182050880970115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2182288792242734507960153 1636716594182050880970115)
    ·
      refine ⟨2455074891273076321455173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1636716594182050880970115 2455074891273076321455173)
      ·
        refine ⟨460326542113701810272845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2455074891273076321455173 460326542113701810272845)
        ·
          refine ⟨172622453292638178852317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 460326542113701810272845 172622453292638178852317)
          ·
            refine ⟨64733419984739317069619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172622453292638178852317 64733419984739317069619)
            ·
              refine ⟨97100129977108975604429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64733419984739317069619 97100129977108975604429)
              ·
                refine ⟨36412548741415865851661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97100129977108975604429 36412548741415865851661)
                ·
                  refine ⟨13654705778030949694373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36412548741415865851661 13654705778030949694373)
                  ·
                    rfl

theorem cell21_59833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3, 3].length) (baseStart_59833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_59833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_59833 prefixEnd_59833 := by exact prefixLift 59833
  have htrace : WordTrace (prefixWord ++ tailWord_59833) baseStart_59833 baseEnd_59833 := by
    simpa [prefixWord, tailWord_59833, baseEnd_59833] using wordTrace_append hprefix tailTrace_59833
  have hstable : (prefixWord ++ tailWord_59833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59833).length < 2 ^ (prefixWord ++ tailWord_59833).sum := by decide
  have hdescent : baseEnd_59833 < baseStart_59833 := by decide
  rcases family_descends (prefixWord ++ tailWord_59833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60055 : List Nat := [1, 1, 3, 3, 2, 1, 1, 9]
def baseStart_60055 : Nat := 118140960795 + 60055 * 2 ^ 59
def prefixEnd_60055 : Nat := 4983230072969 + 3 ^ 40 * 60055 * 2
def baseEnd_60055 : Nat := 4568456400869298997973

theorem tailTrace_60055 : CollatzResearch.WordTrace tailWord_60055 prefixEnd_60055 4568456400869298997973 := by
  unfold tailWord_60055
  simp only [CollatzResearch.WordTrace]
  refine ⟨2190385797438466422541619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1460257198292310948361079 2190385797438466422541619)
  ·
    refine ⟨3285578696157699633812429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2190385797438466422541619 3285578696157699633812429)
    ·
      refine ⟨1232092011059137362679661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3285578696157699633812429 1232092011059137362679661)
      ·
        refine ⟨462034504147176511004873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1232092011059137362679661 462034504147176511004873)
        ·
          refine ⟨346525878110382383253655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462034504147176511004873 346525878110382383253655)
          ·
            refine ⟨519788817165573574880483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346525878110382383253655 519788817165573574880483)
            ·
              refine ⟨779683225748360362320725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519788817165573574880483 779683225748360362320725)
              ·
                refine ⟨4568456400869298997973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 779683225748360362320725 4568456400869298997973)
                ·
                  rfl

theorem cell21_60055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 9].length) (baseStart_60055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_60055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_60055 prefixEnd_60055 := by exact prefixLift 60055
  have htrace : WordTrace (prefixWord ++ tailWord_60055) baseStart_60055 baseEnd_60055 := by
    simpa [prefixWord, tailWord_60055, baseEnd_60055] using wordTrace_append hprefix tailTrace_60055
  have hstable : (prefixWord ++ tailWord_60055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60055).length < 2 ^ (prefixWord ++ tailWord_60055).sum := by decide
  have hdescent : baseEnd_60055 < baseStart_60055 := by decide
  rcases family_descends (prefixWord ++ tailWord_60055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60072 : List Nat := [2, 1, 7, 11]
def baseStart_60072 : Nat := 118140960795 + 60072 * 2 ^ 59
def prefixEnd_60072 : Nat := 4983230072969 + 3 ^ 40 * 60072 * 2
def baseEnd_60072 : Nat := 56416661869216646957

theorem tailTrace_60072 : CollatzResearch.WordTrace tailWord_60072 prefixEnd_60072 56416661869216646957 := by
  unfold tailWord_60072
  simp only [CollatzResearch.WordTrace]
  refine ⟨1095502919188439162955235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1460670558917918883940313 1095502919188439162955235)
  ·
    refine ⟨1643254378782658744432853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1095502919188439162955235 1643254378782658744432853)
    ·
      refine ⟨38513774502718564322645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 1643254378782658744432853 38513774502718564322645)
      ·
        refine ⟨56416661869216646957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 38513774502718564322645 56416661869216646957)
        ·
          rfl

theorem cell21_60072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 11].length) (baseStart_60072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_60072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_60072 prefixEnd_60072 := by exact prefixLift 60072
  have htrace : WordTrace (prefixWord ++ tailWord_60072) baseStart_60072 baseEnd_60072 := by
    simpa [prefixWord, tailWord_60072, baseEnd_60072] using wordTrace_append hprefix tailTrace_60072
  have hstable : (prefixWord ++ tailWord_60072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60072).length < 2 ^ (prefixWord ++ tailWord_60072).sum := by decide
  have hdescent : baseEnd_60072 < baseStart_60072 := by decide
  rcases family_descends (prefixWord ++ tailWord_60072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60078 : List Nat := [4, 1, 4, 1, 1, 1, 4, 2, 3]
def baseStart_60078 : Nat := 118140960795 + 60078 * 2 ^ 59
def prefixEnd_60078 : Nat := 4983230072969 + 3 ^ 40 * 60078 * 2
def baseEnd_60078 : Nat := 13710618115964968110539

theorem tailTrace_60078 : CollatzResearch.WordTrace tailWord_60078 prefixEnd_60078 13710618115964968110539 := by
  unfold tailWord_60078
  simp only [CollatzResearch.WordTrace]
  refine ⟨273903084544392668828611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1460816450903427567085925 273903084544392668828611)
  ·
    refine ⟨410854626816589003242917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273903084544392668828611 410854626816589003242917)
    ·
      refine ⟨77035242528110438108047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 410854626816589003242917 77035242528110438108047)
      ·
        refine ⟨115552863792165657162071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77035242528110438108047 115552863792165657162071)
        ·
          refine ⟨173329295688248485743107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115552863792165657162071 173329295688248485743107)
          ·
            refine ⟨259993943532372728614661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173329295688248485743107 259993943532372728614661)
            ·
              refine ⟨48748864412319886615249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 259993943532372728614661 48748864412319886615249)
              ·
                refine ⟨36561648309239914961437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48748864412319886615249 36561648309239914961437)
                ·
                  refine ⟨13710618115964968110539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36561648309239914961437 13710618115964968110539)
                  ·
                    rfl

theorem cell21_60078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_60078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_60078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_60078 prefixEnd_60078 := by exact prefixLift 60078
  have htrace : WordTrace (prefixWord ++ tailWord_60078) baseStart_60078 baseEnd_60078 := by
    simpa [prefixWord, tailWord_60078, baseEnd_60078] using wordTrace_append hprefix tailTrace_60078
  have hstable : (prefixWord ++ tailWord_60078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60078).length < 2 ^ (prefixWord ++ tailWord_60078).sum := by decide
  have hdescent : baseEnd_60078 < baseStart_60078 := by decide
  rcases family_descends (prefixWord ++ tailWord_60078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60120 : List Nat := [2, 1, 2, 2, 3, 3, 2, 3, 3]
def baseStart_60120 : Nat := 118140960795 + 60120 * 2 ^ 59
def prefixEnd_60120 : Nat := 4983230072969 + 3 ^ 40 * 60120 * 2
def baseEnd_60120 : Nat := 13720203088182228410453

theorem tailTrace_60120 : CollatzResearch.WordTrace tailWord_60120 prefixEnd_60120 13720203088182228410453 := by
  unfold tailWord_60120
  simp only [CollatzResearch.WordTrace]
  refine ⟨1096378271101491261828907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1461837694801988349105209 1096378271101491261828907)
  ·
    refine ⟨1644567406652236892743361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1096378271101491261828907 1644567406652236892743361)
    ·
      refine ⟨1233425554989177669557521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1644567406652236892743361 1233425554989177669557521)
      ·
        refine ⟨925069166241883252168141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1233425554989177669557521 925069166241883252168141)
        ·
          refine ⟨346900937340706219563053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 925069166241883252168141 346900937340706219563053)
          ·
            refine ⟨130087851502764832336145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346900937340706219563053 130087851502764832336145)
            ·
              refine ⟨97565888627073624252109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130087851502764832336145 97565888627073624252109)
              ·
                refine ⟨36587208235152609094541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97565888627073624252109 36587208235152609094541)
                ·
                  refine ⟨13720203088182228410453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36587208235152609094541 13720203088182228410453)
                  ·
                    rfl

theorem cell21_60120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3, 3].length) (baseStart_60120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_60120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_60120 prefixEnd_60120 := by exact prefixLift 60120
  have htrace : WordTrace (prefixWord ++ tailWord_60120) baseStart_60120 baseEnd_60120 := by
    simpa [prefixWord, tailWord_60120, baseEnd_60120] using wordTrace_append hprefix tailTrace_60120
  have hstable : (prefixWord ++ tailWord_60120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60120).length < 2 ^ (prefixWord ++ tailWord_60120).sum := by decide
  have hdescent : baseEnd_60120 < baseStart_60120 := by decide
  rcases family_descends (prefixWord ++ tailWord_60120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60193 : List Nat := [1, 2, 3, 2, 1, 2, 2, 4, 4]
def baseStart_60193 : Nat := 118140960795 + 60193 * 2 ^ 59
def prefixEnd_60193 : Nat := 4983230072969 + 3 ^ 40 * 60193 * 2
def baseEnd_60193 : Nat := 13736862682750323693637

theorem tailTrace_60193 : CollatzResearch.WordTrace tailWord_60193 prefixEnd_60193 13736862682750323693637 := by
  unfold tailWord_60193
  simp only [CollatzResearch.WordTrace]
  refine ⟨2195419070938515991065233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1463612713959010660710155 2195419070938515991065233)
  ·
    refine ⟨1646564303203886993298925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2195419070938515991065233 1646564303203886993298925)
    ·
      refine ⟨617461613701457622487097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1646564303203886993298925 617461613701457622487097)
      ·
        refine ⟨463096210276093216865323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 617461613701457622487097 463096210276093216865323)
        ·
          refine ⟨694644315414139825297985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463096210276093216865323 694644315414139825297985)
          ·
            refine ⟨520983236560604868973489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 694644315414139825297985 520983236560604868973489)
            ·
              refine ⟨390737427420453651730117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 520983236560604868973489 390737427420453651730117)
              ·
                refine ⟨73263267641335059699397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 390737427420453651730117 73263267641335059699397)
                ·
                  refine ⟨13736862682750323693637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73263267641335059699397 13736862682750323693637)
                  ·
                    rfl

theorem cell21_60193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 4].length) (baseStart_60193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_60193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_60193 prefixEnd_60193 := by exact prefixLift 60193
  have htrace : WordTrace (prefixWord ++ tailWord_60193) baseStart_60193 baseEnd_60193 := by
    simpa [prefixWord, tailWord_60193, baseEnd_60193] using wordTrace_append hprefix tailTrace_60193
  have hstable : (prefixWord ++ tailWord_60193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60193).length < 2 ^ (prefixWord ++ tailWord_60193).sum := by decide
  have hdescent : baseEnd_60193 < baseStart_60193 := by decide
  rcases family_descends (prefixWord ++ tailWord_60193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60196 : List Nat := [2, 3, 1, 3, 3, 2, 1, 1, 5]
def baseStart_60196 : Nat := 118140960795 + 60196 * 2 ^ 59
def prefixEnd_60196 : Nat := 4983230072969 + 3 ^ 40 * 60196 * 2
def baseEnd_60196 : Nat := 13737547323622985143631

theorem tailTrace_60196 : CollatzResearch.WordTrace tailWord_60196 prefixEnd_60196 13737547323622985143631 := by
  unfold tailWord_60196
  simp only [CollatzResearch.WordTrace]
  refine ⟨1097764244963823751712221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1463685659951765002282961 1097764244963823751712221)
  ·
    refine ⟨411661591861433906892083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1097764244963823751712221 411661591861433906892083)
    ·
      refine ⟨617492387792150860338125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411661591861433906892083 617492387792150860338125)
      ·
        refine ⟨231559645422056572626797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 617492387792150860338125 231559645422056572626797)
        ·
          refine ⟨86834867033271214735049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231559645422056572626797 86834867033271214735049)
          ·
            refine ⟨65126150274953411051287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86834867033271214735049 65126150274953411051287)
            ·
              refine ⟨97689225412430116576931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65126150274953411051287 97689225412430116576931)
              ·
                refine ⟨146533838118645174865397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97689225412430116576931 146533838118645174865397)
                ·
                  refine ⟨13737547323622985143631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146533838118645174865397 13737547323622985143631)
                  ·
                    rfl

theorem cell21_60196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_60196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_60196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_60196 prefixEnd_60196 := by exact prefixLift 60196
  have htrace : WordTrace (prefixWord ++ tailWord_60196) baseStart_60196 baseEnd_60196 := by
    simpa [prefixWord, tailWord_60196, baseEnd_60196] using wordTrace_append hprefix tailTrace_60196
  have hstable : (prefixWord ++ tailWord_60196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60196).length < 2 ^ (prefixWord ++ tailWord_60196).sum := by decide
  have hdescent : baseEnd_60196 < baseStart_60196 := by decide
  rcases family_descends (prefixWord ++ tailWord_60196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60255 : List Nat := [1, 1, 2, 3, 1, 3, 3, 4, 3]
def baseStart_60255 : Nat := 118140960795 + 60255 * 2 ^ 59
def prefixEnd_60255 : Nat := 4983230072969 + 3 ^ 40 * 60255 * 2
def baseEnd_60255 : Nat := 13751011927451993660177

theorem tailTrace_60255 : CollatzResearch.WordTrace tailWord_60255 prefixEnd_60255 13751011927451993660177 := by
  unfold tailWord_60255
  simp only [CollatzResearch.WordTrace]
  refine ⟨2197680396713900579822219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1465120264475933719881479 2197680396713900579822219)
  ·
    refine ⟨3296520595070850869733329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2197680396713900579822219 3296520595070850869733329)
    ·
      refine ⟨2472390446303138152299997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3296520595070850869733329 2472390446303138152299997)
      ·
        refine ⟨927146417363676807112499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2472390446303138152299997 927146417363676807112499)
        ·
          refine ⟨1390719626045515210668749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927146417363676807112499 1390719626045515210668749)
          ·
            refine ⟨521519859767068204000781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1390719626045515210668749 521519859767068204000781)
            ·
              refine ⟨195569947412650576500293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 521519859767068204000781 195569947412650576500293)
              ·
                refine ⟨36669365139871983093805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195569947412650576500293 36669365139871983093805)
                ·
                  refine ⟨13751011927451993660177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36669365139871983093805 13751011927451993660177)
                  ·
                    rfl

theorem cell21_60255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4, 3].length) (baseStart_60255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_60255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_60255 prefixEnd_60255 := by exact prefixLift 60255
  have htrace : WordTrace (prefixWord ++ tailWord_60255) baseStart_60255 baseEnd_60255 := by
    simpa [prefixWord, tailWord_60255, baseEnd_60255] using wordTrace_append hprefix tailTrace_60255
  have hstable : (prefixWord ++ tailWord_60255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60255).length < 2 ^ (prefixWord ++ tailWord_60255).sum := by decide
  have hdescent : baseEnd_60255 < baseStart_60255 := by decide
  rcases family_descends (prefixWord ++ tailWord_60255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60258 : List Nat := [3, 3, 2, 1, 4, 1, 1, 6]
def baseStart_60258 : Nat := 118140960795 + 60258 * 2 ^ 59
def prefixEnd_60258 : Nat := 4983230072969 + 3 ^ 40 * 60258 * 2
def baseEnd_60258 : Nat := 4583898856108218370057

theorem tailTrace_60258 : CollatzResearch.WordTrace tailWord_60258 prefixEnd_60258 4583898856108218370057 := by
  unfold tailWord_60258
  simp only [CollatzResearch.WordTrace]
  refine ⟨549447453925758023045357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1465193210468688061454285 549447453925758023045357)
  ·
    refine ⟨206042795222159258642009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 549447453925758023045357 206042795222159258642009)
    ·
      refine ⟨154532096416619443981507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206042795222159258642009 154532096416619443981507)
      ·
        refine ⟨231798144624929165972261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154532096416619443981507 231798144624929165972261)
        ·
          refine ⟨43462152117174218619799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231798144624929165972261 43462152117174218619799)
          ·
            refine ⟨65193228175761327929699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43462152117174218619799 65193228175761327929699)
            ·
              refine ⟨97789842263641991894549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65193228175761327929699 97789842263641991894549)
              ·
                refine ⟨4583898856108218370057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97789842263641991894549 4583898856108218370057)
                ·
                  rfl

theorem cell21_60258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 6].length) (baseStart_60258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_60258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_60258 prefixEnd_60258 := by exact prefixLift 60258
  have htrace : WordTrace (prefixWord ++ tailWord_60258) baseStart_60258 baseEnd_60258 := by
    simpa [prefixWord, tailWord_60258, baseEnd_60258] using wordTrace_append hprefix tailTrace_60258
  have hstable : (prefixWord ++ tailWord_60258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60258).length < 2 ^ (prefixWord ++ tailWord_60258).sum := by decide
  have hdescent : baseEnd_60258 < baseStart_60258 := by decide
  rcases family_descends (prefixWord ++ tailWord_60258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60421 : List Nat := [1, 3, 1, 1, 2, 3, 4, 2, 4]
def baseStart_60421 : Nat := 118140960795 + 60421 * 2 ^ 59
def prefixEnd_60421 : Nat := 4983230072969 + 3 ^ 40 * 60421 * 2
def baseEnd_60421 : Nat := 13788895389072593893171

theorem tailTrace_60421 : CollatzResearch.WordTrace tailWord_60421 prefixEnd_60421 13788895389072593893171 := by
  unfold tailWord_60421
  simp only [CollatzResearch.WordTrace]
  refine ⟨2203734914112510930365117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1469156609408340620243411 2203734914112510930365117)
  ·
    refine ⟨826400592792191598886919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2203734914112510930365117 826400592792191598886919)
    ·
      refine ⟨1239600889188287398330379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 826400592792191598886919 1239600889188287398330379)
      ·
        refine ⟨1859401333782431097495569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1239600889188287398330379 1859401333782431097495569)
        ·
          refine ⟨1394551000336823323121677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1859401333782431097495569 1394551000336823323121677)
          ·
            refine ⟨522956625126308746170629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1394551000336823323121677 522956625126308746170629)
            ·
              refine ⟨98054367211182889906993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 522956625126308746170629 98054367211182889906993)
              ·
                refine ⟨73540775408387167430245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98054367211182889906993 73540775408387167430245)
                ·
                  refine ⟨13788895389072593893171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73540775408387167430245 13788895389072593893171)
                  ·
                    rfl

theorem cell21_60421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_60421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_60421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_60421 prefixEnd_60421 := by exact prefixLift 60421
  have htrace : WordTrace (prefixWord ++ tailWord_60421) baseStart_60421 baseEnd_60421 := by
    simpa [prefixWord, tailWord_60421, baseEnd_60421] using wordTrace_append hprefix tailTrace_60421
  have hstable : (prefixWord ++ tailWord_60421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60421).length < 2 ^ (prefixWord ++ tailWord_60421).sum := by decide
  have hdescent : baseEnd_60421 < baseStart_60421 := by decide
  rcases family_descends (prefixWord ++ tailWord_60421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
