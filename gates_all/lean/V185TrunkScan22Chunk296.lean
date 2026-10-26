import V185TrunkScan22Chunk295

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2640509 : List Nat := [1, 4, 1, 1, 6, 1, 1, 2, 1, 4]
def baseStart_2640509 : Nat := 118140960795 + 2640509 * 2 ^ 59
def prefixEnd_2640509 : Nat := 4983230072969 + 3 ^ 40 * 2640509 * 2
def baseEnd_2640509 : Nat := 903900193015276486729351

theorem tailTrace_2640509 : CollatzResearch.WordTrace tailWord_2640509 prefixEnd_2640509 903900193015276486729351 := by
  unfold tailWord_2640509
  simp only [CollatzResearch.WordTrace]
  refine ⟨96307275190894330879308581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64204850127262887252872387 96307275190894330879308581)
  ·
    refine ⟨18057614098292687039870359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96307275190894330879308581 18057614098292687039870359)
    ·
      refine ⟨27086421147439030559805539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18057614098292687039870359 27086421147439030559805539)
      ·
        refine ⟨40629631721158545839708309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27086421147439030559805539 40629631721158545839708309)
        ·
          refine ⟨1904513986929306836236327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40629631721158545839708309 1904513986929306836236327)
          ·
            refine ⟨2856770980393960254354491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1904513986929306836236327 2856770980393960254354491)
            ·
              refine ⟨4285156470590940381531737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2856770980393960254354491 4285156470590940381531737)
              ·
                refine ⟨3213867352943205286148803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4285156470590940381531737 3213867352943205286148803)
                ·
                  refine ⟨4820801029414807929223205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3213867352943205286148803 4820801029414807929223205)
                  ·
                    refine ⟨903900193015276486729351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4820801029414807929223205 903900193015276486729351)
                    ·
                      rfl

theorem cell22_2640509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_2640509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640509 prefixEnd_2640509 := by exact prefixLift 2640509
  have htrace : WordTrace (prefixWord ++ tailWord_2640509) baseStart_2640509 baseEnd_2640509 := by
    simpa [prefixWord, tailWord_2640509, baseEnd_2640509] using wordTrace_append hprefix tailTrace_2640509
  have hstable : (prefixWord ++ tailWord_2640509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640509).length < 2 ^ (prefixWord ++ tailWord_2640509).sum := by decide
  have hdescent : baseEnd_2640509 < baseStart_2640509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640548 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 1, 8]
def baseStart_2640548 : Nat := 118140960795 + 2640548 * 2 ^ 59
def prefixEnd_2640548 : Nat := 4983230072969 + 3 ^ 40 * 2640548 * 2
def baseEnd_2640548 : Nat := 903913543512293385004231

theorem tailTrace_2640548 : CollatzResearch.WordTrace tailWord_2640548 prefixEnd_2640548 903913543512293385004231 := by
  unfold tailWord_2640548
  simp only [CollatzResearch.WordTrace]
  refine ⟨48154348818876520269989149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64205798425168693693318865 48154348818876520269989149)
  ·
    refine ⟨18057880807078695101245931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48154348818876520269989149 18057880807078695101245931)
    ·
      refine ⟨27086821210618042651868897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18057880807078695101245931 27086821210618042651868897)
      ·
        refine ⟨20315115907963531988901673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27086821210618042651868897 20315115907963531988901673)
        ·
          refine ⟨15236336930972648991676255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20315115907963531988901673 15236336930972648991676255)
          ·
            refine ⟨22854505396458973487514383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15236336930972648991676255 22854505396458973487514383)
            ·
              refine ⟨34281758094688460231271575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22854505396458973487514383 34281758094688460231271575)
              ·
                refine ⟨51422637142032690346907363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34281758094688460231271575 51422637142032690346907363)
                ·
                  refine ⟨77133955713049035520361045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51422637142032690346907363 77133955713049035520361045)
                  ·
                    refine ⟨903913543512293385004231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77133955713049035520361045 903913543512293385004231)
                    ·
                      rfl

theorem cell22_2640548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_2640548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640548 prefixEnd_2640548 := by exact prefixLift 2640548
  have htrace : WordTrace (prefixWord ++ tailWord_2640548) baseStart_2640548 baseEnd_2640548 := by
    simpa [prefixWord, tailWord_2640548, baseEnd_2640548] using wordTrace_append hprefix tailTrace_2640548
  have hstable : (prefixWord ++ tailWord_2640548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640548).length < 2 ^ (prefixWord ++ tailWord_2640548).sum := by decide
  have hdescent : baseEnd_2640548 < baseStart_2640548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640567 : List Nat := [1, 1, 3, 1, 6, 1, 1, 2, 3, 3]
def baseStart_2640567 : Nat := 118140960795 + 2640567 * 2 ^ 59
def prefixEnd_2640567 : Nat := 4983230072969 + 3 ^ 40 * 2640567 * 2
def baseEnd_2640567 : Nat := 903920047600583668779173

theorem tailTrace_2640567 : CollatzResearch.WordTrace tailWord_2640567 prefixEnd_2640567 903920047600583668779173 := by
  unfold tailWord_2640567
  simp only [CollatzResearch.WordTrace]
  refine ⟨96309390624684206784919955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64206260416456137856613303 96309390624684206784919955)
  ·
    refine ⟨144464085937026310177379933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96309390624684206784919955 144464085937026310177379933)
    ·
      refine ⟨54174032226384866316517475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144464085937026310177379933 54174032226384866316517475)
      ·
        refine ⟨81261048339577299474776213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54174032226384866316517475 81261048339577299474776213)
        ·
          refine ⟨3809111640917685912880135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 81261048339577299474776213 3809111640917685912880135)
          ·
            refine ⟨5713667461376528869320203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3809111640917685912880135 5713667461376528869320203)
            ·
              refine ⟨8570501192064793303980305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5713667461376528869320203 8570501192064793303980305)
              ·
                refine ⟨6427875894048594977985229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8570501192064793303980305 6427875894048594977985229)
                ·
                  refine ⟨2410453460268223116744461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6427875894048594977985229 2410453460268223116744461)
                  ·
                    refine ⟨903920047600583668779173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2410453460268223116744461 903920047600583668779173)
                    ·
                      rfl

theorem cell22_2640567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3, 3].length) (baseStart_2640567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640567 prefixEnd_2640567 := by exact prefixLift 2640567
  have htrace : WordTrace (prefixWord ++ tailWord_2640567) baseStart_2640567 baseEnd_2640567 := by
    simpa [prefixWord, tailWord_2640567, baseEnd_2640567] using wordTrace_append hprefix tailTrace_2640567
  have hstable : (prefixWord ++ tailWord_2640567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640567).length < 2 ^ (prefixWord ++ tailWord_2640567).sum := by decide
  have hdescent : baseEnd_2640567 < baseStart_2640567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640584 : List Nat := [2, 1, 3, 1, 2, 4, 2, 3, 1, 3]
def baseStart_2640584 : Nat := 118140960795 + 2640584 * 2 ^ 59
def prefixEnd_2640584 : Nat := 4983230072969 + 3 ^ 40 * 2640584 * 2
def baseEnd_2640584 : Nat := 903925867048001291104121

theorem tailTrace_2640584 : CollatzResearch.WordTrace tailWord_2640584 prefixEnd_2640584 903925867048001291104121 := by
  unfold tailWord_2640584
  simp only [CollatzResearch.WordTrace]
  refine ⟨48155005332811309344144403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64206673777081745792192537 48155005332811309344144403)
  ·
    refine ⟨72232507999216964016216605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48155005332811309344144403 72232507999216964016216605)
    ·
      refine ⟨27087190499706361506081227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72232507999216964016216605 27087190499706361506081227)
      ·
        refine ⟨40630785749559542259121841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27087190499706361506081227 40630785749559542259121841)
        ·
          refine ⟨30473089312169656694341381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40630785749559542259121841 30473089312169656694341381)
          ·
            refine ⟨5713704246031810630189009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30473089312169656694341381 5713704246031810630189009)
            ·
              refine ⟨4285278184523857972641757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5713704246031810630189009 4285278184523857972641757)
              ·
                refine ⟨1606979319196446739740659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4285278184523857972641757 1606979319196446739740659)
                ·
                  refine ⟨2410468978794670109610989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1606979319196446739740659 2410468978794670109610989)
                  ·
                    refine ⟨903925867048001291104121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2410468978794670109610989 903925867048001291104121)
                    ·
                      rfl

theorem cell22_2640584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_2640584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640584 prefixEnd_2640584 := by exact prefixLift 2640584
  have htrace : WordTrace (prefixWord ++ tailWord_2640584) baseStart_2640584 baseEnd_2640584 := by
    simpa [prefixWord, tailWord_2640584, baseEnd_2640584] using wordTrace_append hprefix tailTrace_2640584
  have hstable : (prefixWord ++ tailWord_2640584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640584).length < 2 ^ (prefixWord ++ tailWord_2640584).sum := by decide
  have hdescent : baseEnd_2640584 < baseStart_2640584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640597 : List Nat := [1, 3, 2, 5, 1, 1, 1, 1, 7]
def baseStart_2640597 : Nat := 118140960795 + 2640597 * 2 ^ 59
def prefixEnd_2640597 : Nat := 4983230072969 + 3 ^ 40 * 2640597 * 2
def baseEnd_2640597 : Nat := 301310105737891196843027

theorem tailTrace_2640597 : CollatzResearch.WordTrace tailWord_2640597 prefixEnd_2640597 301310105737891196843027 := by
  unfold tailWord_2640597
  simp only [CollatzResearch.WordTrace]
  refine ⟨96310484814575521908512045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64206989876383681272341363 96310484814575521908512045)
  ·
    refine ⟨36116431805465820715692017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96310484814575521908512045 36116431805465820715692017)
    ·
      refine ⟨27087323854099365536769013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36116431805465820715692017 27087323854099365536769013)
      ·
        refine ⟨2539436611321815519072095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27087323854099365536769013 2539436611321815519072095)
        ·
          refine ⟨3809154916982723278608143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2539436611321815519072095 3809154916982723278608143)
          ·
            refine ⟨5713732375474084917912215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3809154916982723278608143 5713732375474084917912215)
            ·
              refine ⟨8570598563211127376868323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5713732375474084917912215 8570598563211127376868323)
              ·
                refine ⟨12855897844816691065302485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8570598563211127376868323 12855897844816691065302485)
                ·
                  refine ⟨301310105737891196843027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12855897844816691065302485 301310105737891196843027)
                  ·
                    rfl

theorem cell22_2640597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 7].length) (baseStart_2640597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640597 prefixEnd_2640597 := by exact prefixLift 2640597
  have htrace : WordTrace (prefixWord ++ tailWord_2640597) baseStart_2640597 baseEnd_2640597 := by
    simpa [prefixWord, tailWord_2640597, baseEnd_2640597] using wordTrace_append hprefix tailTrace_2640597
  have hstable : (prefixWord ++ tailWord_2640597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640597).length < 2 ^ (prefixWord ++ tailWord_2640597).sum := by decide
  have hdescent : baseEnd_2640597 < baseStart_2640597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640655 : List Nat := [1, 1, 2, 1, 1, 1, 7, 2, 2, 4]
def baseStart_2640655 : Nat := 118140960795 + 2640655 * 2 ^ 59
def prefixEnd_2640655 : Nat := 4983230072969 + 3 ^ 40 * 2640655 * 2
def baseEnd_2640655 : Nat := 903950171798980772578903

theorem tailTrace_2640655 : CollatzResearch.WordTrace tailWord_2640655 prefixEnd_2640655 903950171798980772578903 := by
  unfold tailWord_2640655
  simp only [CollatzResearch.WordTrace]
  refine ⟨96312600248365397814123419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64208400165576931876082279 96312600248365397814123419)
  ·
    refine ⟨144468900372548096721185129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96312600248365397814123419 144468900372548096721185129)
    ·
      refine ⟨108351675279411072540888847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144468900372548096721185129 108351675279411072540888847)
      ·
        refine ⟨162527512919116608811333271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108351675279411072540888847 162527512919116608811333271)
        ·
          refine ⟨243791269378674913216999907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162527512919116608811333271 243791269378674913216999907)
          ·
            refine ⟨365686904068012369825499861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243791269378674913216999907 365686904068012369825499861)
            ·
              refine ⟨8570786814094039917785153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 365686904068012369825499861 8570786814094039917785153)
              ·
                refine ⟨6428090110570529938338865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8570786814094039917785153 6428090110570529938338865)
                ·
                  refine ⟨4821067582927897453754149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6428090110570529938338865 4821067582927897453754149)
                  ·
                    refine ⟨903950171798980772578903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4821067582927897453754149 903950171798980772578903)
                    ·
                      rfl

theorem cell22_2640655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 4].length) (baseStart_2640655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640655 prefixEnd_2640655 := by exact prefixLift 2640655
  have htrace : WordTrace (prefixWord ++ tailWord_2640655) baseStart_2640655 baseEnd_2640655 := by
    simpa [prefixWord, tailWord_2640655, baseEnd_2640655] using wordTrace_append hprefix tailTrace_2640655
  have hstable : (prefixWord ++ tailWord_2640655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640655).length < 2 ^ (prefixWord ++ tailWord_2640655).sum := by decide
  have hdescent : baseEnd_2640655 < baseStart_2640655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640674 : List Nat := [3, 3, 1, 1, 2, 3, 1, 3, 2, 3]
def baseStart_2640674 : Nat := 118140960795 + 2640674 * 2 ^ 59
def prefixEnd_2640674 : Nat := 4983230072969 + 3 ^ 40 * 2640674 * 2
def baseEnd_2640674 : Nat := 903956675887271056353845

theorem tailTrace_2640674 : CollatzResearch.WordTrace tailWord_2640674 prefixEnd_2640674 903956675887271056353845 := by
  unfold tailWord_2640674
  simp only [CollatzResearch.WordTrace]
  refine ⟨24078323308824141014766269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64208862156864376039376717 24078323308824141014766269)
  ·
    refine ⟨9029371240809052880537351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24078323308824141014766269 9029371240809052880537351)
    ·
      refine ⟨13544056861213579320806027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9029371240809052880537351 13544056861213579320806027)
      ·
        refine ⟨20316085291820368981209041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13544056861213579320806027 20316085291820368981209041)
        ·
          refine ⟨15237063968865276735906781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20316085291820368981209041 15237063968865276735906781)
          ·
            refine ⟨5713898988324478775965043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15237063968865276735906781 5713898988324478775965043)
            ·
              refine ⟨8570848482486718163947565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5713898988324478775965043 8570848482486718163947565)
              ·
                refine ⟨3214068180932519311480337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8570848482486718163947565 3214068180932519311480337)
                ·
                  refine ⟨2410551135699389483610253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3214068180932519311480337 2410551135699389483610253)
                  ·
                    refine ⟨903956675887271056353845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2410551135699389483610253 903956675887271056353845)
                    ·
                      rfl

theorem cell22_2640674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_2640674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640674 prefixEnd_2640674 := by exact prefixLift 2640674
  have htrace : WordTrace (prefixWord ++ tailWord_2640674) baseStart_2640674 baseEnd_2640674 := by
    simpa [prefixWord, tailWord_2640674, baseEnd_2640674] using wordTrace_append hprefix tailTrace_2640674
  have hstable : (prefixWord ++ tailWord_2640674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640674).length < 2 ^ (prefixWord ++ tailWord_2640674).sum := by decide
  have hdescent : baseEnd_2640674 < baseStart_2640674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640708 : List Nat := [2, 3, 4, 2, 1, 1, 2, 2, 2, 3]
def baseStart_2640708 : Nat := 118140960795 + 2640708 * 2 ^ 59
def prefixEnd_2640708 : Nat := 4983230072969 + 3 ^ 40 * 2640708 * 2
def baseEnd_2640708 : Nat := 903968314782106301003741

theorem tailTrace_2640708 : CollatzResearch.WordTrace tailWord_2640708 prefixEnd_2640708 903968314782106301003741 := by
  unfold tailWord_2640708
  simp only [CollatzResearch.WordTrace]
  refine ⟨48157266658586693932901389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64209688878115591910535185 48157266658586693932901389)
  ·
    refine ⟨18058974996970010224838021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48157266658586693932901389 18058974996970010224838021)
    ·
      refine ⟨3386057811931876917157129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18058974996970010224838021 3386057811931876917157129)
      ·
        refine ⟨2539543358948907687867847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3386057811931876917157129 2539543358948907687867847)
        ·
          refine ⟨3809315038423361531801771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2539543358948907687867847 3809315038423361531801771)
          ·
            refine ⟨5713972557635042297702657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3809315038423361531801771 5713972557635042297702657)
            ·
              refine ⟨4285479418226281723276993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5713972557635042297702657 4285479418226281723276993)
              ·
                refine ⟨3214109563669711292457745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4285479418226281723276993 3214109563669711292457745)
                ·
                  refine ⟨2410582172752283469343309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3214109563669711292457745 2410582172752283469343309)
                  ·
                    refine ⟨903968314782106301003741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2410582172752283469343309 903968314782106301003741)
                    ·
                      rfl

theorem cell22_2640708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_2640708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640708 prefixEnd_2640708 := by exact prefixLift 2640708
  have htrace : WordTrace (prefixWord ++ tailWord_2640708) baseStart_2640708 baseEnd_2640708 := by
    simpa [prefixWord, tailWord_2640708, baseEnd_2640708] using wordTrace_append hprefix tailTrace_2640708
  have hstable : (prefixWord ++ tailWord_2640708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640708).length < 2 ^ (prefixWord ++ tailWord_2640708).sum := by decide
  have hdescent : baseEnd_2640708 < baseStart_2640708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640710 : List Nat := [6, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_2640710 : Nat := 118140960795 + 2640710 * 2 ^ 59
def prefixEnd_2640710 : Nat := 4983230072969 + 3 ^ 40 * 2640710 * 2
def baseEnd_2640710 : Nat := 301322999807659654151245

theorem tailTrace_2640710 : CollatzResearch.WordTrace tailWord_2640710 prefixEnd_2640710 301322999807659654151245 := by
  unfold tailWord_2640710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3009831445723941943980487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 64209737508777428138250389 3009831445723941943980487)
  ·
    refine ⟨4514747168585912915970731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3009831445723941943980487 4514747168585912915970731)
    ·
      refine ⟨6772120752878869373956097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4514747168585912915970731 6772120752878869373956097)
      ·
        refine ⟨5079090564659152030467073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6772120752878869373956097 5079090564659152030467073)
        ·
          refine ⟨3809317923494364022850305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5079090564659152030467073 3809317923494364022850305)
          ·
            refine ⟨2856988442620773017137729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3809317923494364022850305 2856988442620773017137729)
            ·
              refine ⟨2142741331965579762853297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2856988442620773017137729 2142741331965579762853297)
              ·
                refine ⟨1607055998974184822139973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2142741331965579762853297 1607055998974184822139973)
                ·
                  refine ⟨301322999807659654151245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1607055998974184822139973 301322999807659654151245)
                  ·
                    rfl

theorem cell22_2640710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_2640710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640710 prefixEnd_2640710 := by exact prefixLift 2640710
  have htrace : WordTrace (prefixWord ++ tailWord_2640710) baseStart_2640710 baseEnd_2640710 := by
    simpa [prefixWord, tailWord_2640710, baseEnd_2640710] using wordTrace_append hprefix tailTrace_2640710
  have hstable : (prefixWord ++ tailWord_2640710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640710).length < 2 ^ (prefixWord ++ tailWord_2640710).sum := by decide
  have hdescent : baseEnd_2640710 < baseStart_2640710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640730 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 1, 7]
def baseStart_2640730 : Nat := 118140960795 + 2640730 * 2 ^ 59
def prefixEnd_2640730 : Nat := 4983230072969 + 3 ^ 40 * 2640730 * 2
def baseEnd_2640730 : Nat := 903975845831705576953673

theorem tailTrace_2640730 : CollatzResearch.WordTrace tailWord_2640730 prefixEnd_2640730 903975845831705576953673 := by
  unfold tailWord_2640730
  simp only [CollatzResearch.WordTrace]
  refine ⟨24078833930773421405775911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64210223815395790415402429 24078833930773421405775911)
  ·
    refine ⟨36118250896160132108663867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24078833930773421405775911 36118250896160132108663867)
    ·
      refine ⟨54177376344240198162995801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36118250896160132108663867 54177376344240198162995801)
      ·
        refine ⟨40633032258180148622246851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54177376344240198162995801 40633032258180148622246851)
        ·
          refine ⟨60949548387270222933370277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40633032258180148622246851 60949548387270222933370277)
          ·
            refine ⟨11428040322613166800006927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60949548387270222933370277 11428040322613166800006927)
            ·
              refine ⟨17142060483919750200010391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11428040322613166800006927 17142060483919750200010391)
              ·
                refine ⟨25713090725879625300015587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17142060483919750200010391 25713090725879625300015587)
                ·
                  refine ⟨38569636088819437950023381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25713090725879625300015587 38569636088819437950023381)
                  ·
                    refine ⟨903975845831705576953673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38569636088819437950023381 903975845831705576953673)
                    ·
                      rfl

theorem cell22_2640730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_2640730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640730 prefixEnd_2640730 := by exact prefixLift 2640730
  have htrace : WordTrace (prefixWord ++ tailWord_2640730) baseStart_2640730 baseEnd_2640730 := by
    simpa [prefixWord, tailWord_2640730, baseEnd_2640730] using wordTrace_append hprefix tailTrace_2640730
  have hstable : (prefixWord ++ tailWord_2640730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640730).length < 2 ^ (prefixWord ++ tailWord_2640730).sum := by decide
  have hdescent : baseEnd_2640730 < baseStart_2640730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640777 : List Nat := [1, 2, 1, 1, 5, 3, 2, 1, 6]
def baseStart_2640777 : Nat := 118140960795 + 2640777 * 2 ^ 59
def prefixEnd_2640777 : Nat := 4983230072969 + 3 ^ 40 * 2640777 * 2
def baseEnd_2640777 : Nat := 301330644964071040342843

theorem tailTrace_2640777 : CollatzResearch.WordTrace tailWord_2640777 prefixEnd_2640777 301330644964071040342843 := by
  unfold tailWord_2640777
  simp only [CollatzResearch.WordTrace]
  refine ⟨96317049953923412650064585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64211366635948941766709723 96317049953923412650064585)
  ·
    refine ⟨72237787465442559487548439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96317049953923412650064585 72237787465442559487548439)
    ·
      refine ⟨108356681198163839231322659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72237787465442559487548439 108356681198163839231322659)
      ·
        refine ⟨162535021797245758846983989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108356681198163839231322659 162535021797245758846983989)
        ·
          refine ⟨15237658293491789891904749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 162535021797245758846983989 15237658293491789891904749)
          ·
            refine ⟨5714121860059421209464281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15237658293491789891904749 5714121860059421209464281)
            ·
              refine ⟨4285591395044565907098211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5714121860059421209464281 4285591395044565907098211)
              ·
                refine ⟨6428387092566848860647317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4285591395044565907098211 6428387092566848860647317)
                ·
                  refine ⟨301330644964071040342843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6428387092566848860647317 301330644964071040342843)
                  ·
                    rfl

theorem cell22_2640777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 6].length) (baseStart_2640777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640777 prefixEnd_2640777 := by exact prefixLift 2640777
  have htrace : WordTrace (prefixWord ++ tailWord_2640777) baseStart_2640777 baseEnd_2640777 := by
    simpa [prefixWord, tailWord_2640777, baseEnd_2640777] using wordTrace_append hprefix tailTrace_2640777
  have hstable : (prefixWord ++ tailWord_2640777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640777).length < 2 ^ (prefixWord ++ tailWord_2640777).sum := by decide
  have hdescent : baseEnd_2640777 < baseStart_2640777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640796 : List Nat := [2, 2, 3, 3, 2, 1, 2, 2, 1, 4]
def baseStart_2640796 : Nat := 118140960795 + 2640796 * 2 ^ 59
def prefixEnd_2640796 : Nat := 4983230072969 + 3 ^ 40 * 2640796 * 2
def baseEnd_2640796 : Nat := 903998438980503404803471

theorem tailTrace_2640796 : CollatzResearch.WordTrace tailWord_2640796 prefixEnd_2640796 903998438980503404803471 := by
  unfold tailWord_2640796
  simp only [CollatzResearch.WordTrace]
  refine ⟨48158871470427289447503121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64211828627236385930004161 48158871470427289447503121)
  ·
    refine ⟨36119153602820467085627341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48158871470427289447503121 36119153602820467085627341)
    ·
      refine ⟨13544682601057675157110253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36119153602820467085627341 13544682601057675157110253)
      ·
        refine ⟨5079255975396628183916345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13544682601057675157110253 5079255975396628183916345)
        ·
          refine ⟨3809441981547471137937259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5079255975396628183916345 3809441981547471137937259)
          ·
            refine ⟨5714162972321206706905889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3809441981547471137937259 5714162972321206706905889)
            ·
              refine ⟨4285622229240905030179417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5714162972321206706905889 4285622229240905030179417)
              ·
                refine ⟨3214216671930678772634563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4285622229240905030179417 3214216671930678772634563)
                ·
                  refine ⟨4821325007896018158951845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3214216671930678772634563 4821325007896018158951845)
                  ·
                    refine ⟨903998438980503404803471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4821325007896018158951845 903998438980503404803471)
                    ·
                      rfl

theorem cell22_2640796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_2640796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640796 prefixEnd_2640796 := by exact prefixLift 2640796
  have htrace : WordTrace (prefixWord ++ tailWord_2640796) baseStart_2640796 baseEnd_2640796 := by
    simpa [prefixWord, tailWord_2640796, baseEnd_2640796] using wordTrace_append hprefix tailTrace_2640796
  have hstable : (prefixWord ++ tailWord_2640796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640796).length < 2 ^ (prefixWord ++ tailWord_2640796).sum := by decide
  have hdescent : baseEnd_2640796 < baseStart_2640796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640835 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 1, 8]
def baseStart_2640835 : Nat := 118140960795 + 2640835 * 2 ^ 59
def prefixEnd_2640835 : Nat := 4983230072969 + 3 ^ 40 * 2640835 * 2
def baseEnd_2640835 : Nat := 904011789477520303078351

theorem tailTrace_2640835 : CollatzResearch.WordTrace tailWord_2640835 prefixEnd_2640835 904011789477520303078351 := by
  unfold tailWord_2640835
  simp only [CollatzResearch.WordTrace]
  refine ⟨96319165387713288555675959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64212776925142192370450639 96319165387713288555675959)
  ·
    refine ⟨144478748081569932833513939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96319165387713288555675959 144478748081569932833513939)
    ·
      refine ⟨216718122122354899250270909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144478748081569932833513939 216718122122354899250270909)
      ·
        refine ⟨81269295795883087218851591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216718122122354899250270909 81269295795883087218851591)
        ·
          refine ⟨121903943693824630828277387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81269295795883087218851591 121903943693824630828277387)
          ·
            refine ⟨182855915540736946242416081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121903943693824630828277387 182855915540736946242416081)
            ·
              refine ⟨137141936655552709681812061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182855915540736946242416081 137141936655552709681812061)
              ·
                refine ⟨51428226245832266130679523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137141936655552709681812061 51428226245832266130679523)
                ·
                  refine ⟨77142339368748399196019285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51428226245832266130679523 77142339368748399196019285)
                  ·
                    refine ⟨904011789477520303078351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77142339368748399196019285 904011789477520303078351)
                    ·
                      rfl

theorem cell22_2640835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 8].length) (baseStart_2640835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640835 prefixEnd_2640835 := by exact prefixLift 2640835
  have htrace : WordTrace (prefixWord ++ tailWord_2640835) baseStart_2640835 baseEnd_2640835 := by
    simpa [prefixWord, tailWord_2640835, baseEnd_2640835] using wordTrace_append hprefix tailTrace_2640835
  have hstable : (prefixWord ++ tailWord_2640835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640835).length < 2 ^ (prefixWord ++ tailWord_2640835).sum := by decide
  have hdescent : baseEnd_2640835 < baseStart_2640835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640931 : List Nat := [1, 1, 1, 4, 3, 2, 4, 1, 1, 4]
def baseStart_2640931 : Nat := 118140960795 + 2640931 * 2 ^ 59
def prefixEnd_2640931 : Nat := 4983230072969 + 3 ^ 40 * 2640931 * 2
def baseEnd_2640931 : Nat := 904044652239408052678057

theorem tailTrace_2640931 : CollatzResearch.WordTrace tailWord_2640931 prefixEnd_2640931 904044652239408052678057 := by
  unfold tailWord_2640931
  simp only [CollatzResearch.WordTrace]
  refine ⟨96322666795365496951170647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64215111196910331300780431 96322666795365496951170647)
  ·
    refine ⟨144484000193048245426755971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96322666795365496951170647 144484000193048245426755971)
    ·
      refine ⟨216726000289572368140133957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144484000193048245426755971 216726000289572368140133957)
      ·
        refine ⟨40636125054294819026275117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216726000289572368140133957 40636125054294819026275117)
        ·
          refine ⟨15238546895360557134853169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40636125054294819026275117 15238546895360557134853169)
          ·
            refine ⟨11428910171520417851139877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15238546895360557134853169 11428910171520417851139877)
            ·
              refine ⟨2142920657160078347088727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11428910171520417851139877 2142920657160078347088727)
              ·
                refine ⟨3214380985740117520633091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2142920657160078347088727 3214380985740117520633091)
                ·
                  refine ⟨4821571478610176280949637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3214380985740117520633091 4821571478610176280949637)
                  ·
                    refine ⟨904044652239408052678057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4821571478610176280949637 904044652239408052678057)
                    ·
                      rfl

theorem cell22_2640931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 1, 4].length) (baseStart_2640931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640931 prefixEnd_2640931 := by exact prefixLift 2640931
  have htrace : WordTrace (prefixWord ++ tailWord_2640931) baseStart_2640931 baseEnd_2640931 := by
    simpa [prefixWord, tailWord_2640931, baseEnd_2640931] using wordTrace_append hprefix tailTrace_2640931
  have hstable : (prefixWord ++ tailWord_2640931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640931).length < 2 ^ (prefixWord ++ tailWord_2640931).sum := by decide
  have hdescent : baseEnd_2640931 < baseStart_2640931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640944 : List Nat := [2, 1, 1, 1, 2, 4, 3, 1, 4, 3]
def baseStart_2640944 : Nat := 118140960795 + 2640944 * 2 ^ 59
def prefixEnd_2640944 : Nat := 4983230072969 + 3 ^ 40 * 2640944 * 2
def baseEnd_2640944 : Nat := 904049102405080352103017

theorem tailTrace_2640944 : CollatzResearch.WordTrace tailWord_2640944 prefixEnd_2640944 904049102405080352103017 := by
  unfold tailWord_2640944
  simp only [CollatzResearch.WordTrace]
  refine ⟨48161570472159200085696943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64215427296212266780929257 48161570472159200085696943)
  ·
    refine ⟨72242355708238800128545415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48161570472159200085696943 72242355708238800128545415)
    ·
      refine ⟨108363533562358200192818123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72242355708238800128545415 108363533562358200192818123)
      ·
        refine ⟨162545300343537300289227185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108363533562358200192818123 162545300343537300289227185)
        ·
          refine ⟨121908975257652975216920389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162545300343537300289227185 121908975257652975216920389)
          ·
            refine ⟨22857932860809932853172573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121908975257652975216920389 22857932860809932853172573)
            ·
              refine ⟨8571724822803724819939715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22857932860809932853172573 8571724822803724819939715)
              ·
                refine ⟨12857587234205587229909573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8571724822803724819939715 12857587234205587229909573)
                ·
                  refine ⟨2410797606413547605608045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12857587234205587229909573 2410797606413547605608045)
                  ·
                    refine ⟨904049102405080352103017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2410797606413547605608045 904049102405080352103017)
                    ·
                      rfl

theorem cell22_2640944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 4, 3].length) (baseStart_2640944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640944 prefixEnd_2640944 := by exact prefixLift 2640944
  have htrace : WordTrace (prefixWord ++ tailWord_2640944) baseStart_2640944 baseEnd_2640944 := by
    simpa [prefixWord, tailWord_2640944, baseEnd_2640944] using wordTrace_append hprefix tailTrace_2640944
  have hstable : (prefixWord ++ tailWord_2640944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640944).length < 2 ^ (prefixWord ++ tailWord_2640944).sum := by decide
  have hdescent : baseEnd_2640944 < baseStart_2640944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640972 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 1, 9]
def baseStart_2640972 : Nat := 118140960795 + 2640972 * 2 ^ 59
def prefixEnd_2640972 : Nat := 4983230072969 + 3 ^ 40 * 2640972 * 2
def baseEnd_2640972 : Nat := 904058687377297612402931

theorem tailTrace_2640972 : CollatzResearch.WordTrace tailWord_2640972 prefixEnd_2640972 904058687377297612402931 := by
  unfold tailWord_2640972
  simp only [CollatzResearch.WordTrace]
  refine ⟨48162081094108480476706585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64216108125477973968942113 48162081094108480476706585)
  ·
    refine ⟨36121560820581360357529939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48162081094108480476706585 36121560820581360357529939)
    ·
      refine ⟨54182341230872040536294909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36121560820581360357529939 54182341230872040536294909)
      ·
        refine ⟨20318377961577015201110591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54182341230872040536294909 20318377961577015201110591)
        ·
          refine ⟨30477566942365522801665887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20318377961577015201110591 30477566942365522801665887)
          ·
            refine ⟨45716350413548284202498831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30477566942365522801665887 45716350413548284202498831)
            ·
              refine ⟨68574525620322426303748247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45716350413548284202498831 68574525620322426303748247)
              ·
                refine ⟨102861788430483639455622371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68574525620322426303748247 102861788430483639455622371)
                ·
                  refine ⟨154292682645725459183433557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102861788430483639455622371 154292682645725459183433557)
                  ·
                    refine ⟨904058687377297612402931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 154292682645725459183433557 904058687377297612402931)
                    ·
                      rfl

theorem cell22_2640972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_2640972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2640972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2640972 prefixEnd_2640972 := by exact prefixLift 2640972
  have htrace : WordTrace (prefixWord ++ tailWord_2640972) baseStart_2640972 baseEnd_2640972 := by
    simpa [prefixWord, tailWord_2640972, baseEnd_2640972] using wordTrace_append hprefix tailTrace_2640972
  have hstable : (prefixWord ++ tailWord_2640972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640972).length < 2 ^ (prefixWord ++ tailWord_2640972).sum := by decide
  have hdescent : baseEnd_2640972 < baseStart_2640972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641098 : List Nat := [3, 1, 2, 1, 3, 3, 2, 3, 4]
def baseStart_2641098 : Nat := 118140960795 + 2641098 * 2 ^ 59
def prefixEnd_2641098 : Nat := 4983230072969 + 3 ^ 40 * 2641098 * 2
def baseEnd_2641098 : Nat := 301367273250758427917515

theorem tailTrace_2641098 : CollatzResearch.WordTrace tailWord_2641098 prefixEnd_2641098 301367273250758427917515 := by
  unfold tailWord_2641098
  simp only [CollatzResearch.WordTrace]
  refine ⟨24082189446440121118124987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64219171857173656314999965 24082189446440121118124987)
  ·
    refine ⟨36123284169660181677187481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24082189446440121118124987 36123284169660181677187481)
    ·
      refine ⟨27092463127245136257890611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36123284169660181677187481 27092463127245136257890611)
      ·
        refine ⟨40638694690867704386835917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27092463127245136257890611 40638694690867704386835917)
        ·
          refine ⟨15239510509075389145063469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40638694690867704386835917 15239510509075389145063469)
          ·
            refine ⟨5714816440903270929398801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15239510509075389145063469 5714816440903270929398801)
            ·
              refine ⟨4286112330677453197049101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5714816440903270929398801 4286112330677453197049101)
              ·
                refine ⟨1607292124004044948893413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4286112330677453197049101 1607292124004044948893413)
                ·
                  refine ⟨301367273250758427917515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1607292124004044948893413 301367273250758427917515)
                  ·
                    rfl

theorem cell22_2641098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3, 4].length) (baseStart_2641098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2641098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2641098 prefixEnd_2641098 := by exact prefixLift 2641098
  have htrace : WordTrace (prefixWord ++ tailWord_2641098) baseStart_2641098 baseEnd_2641098 := by
    simpa [prefixWord, tailWord_2641098, baseEnd_2641098] using wordTrace_append hprefix tailTrace_2641098
  have hstable : (prefixWord ++ tailWord_2641098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641098).length < 2 ^ (prefixWord ++ tailWord_2641098).sum := by decide
  have hdescent : baseEnd_2641098 < baseStart_2641098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641130 : List Nat := [3, 1, 3, 1, 1, 4, 3, 1, 2, 3]
def baseStart_2641130 : Nat := 118140960795 + 2641130 * 2 ^ 59
def prefixEnd_2641130 : Nat := 4983230072969 + 3 ^ 40 * 2641130 * 2
def baseEnd_2641130 : Nat := 904112774006237866952447

theorem tailTrace_2641130 : CollatzResearch.WordTrace tailWord_2641130 prefixEnd_2641130 904112774006237866952447 := by
  unfold tailWord_2641130
  simp only [CollatzResearch.WordTrace]
  refine ⟨24082481230411138484416211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64219949947763035958443229 24082481230411138484416211)
  ·
    refine ⟨36123721845616707726624317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24082481230411138484416211 36123721845616707726624317)
    ·
      refine ⟨13546395692106265397484119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36123721845616707726624317 13546395692106265397484119)
      ·
        refine ⟨20319593538159398096226179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13546395692106265397484119 20319593538159398096226179)
        ·
          refine ⟨30479390307239097144339269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20319593538159398096226179 30479390307239097144339269)
          ·
            refine ⟨5714885682607330714563613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30479390307239097144339269 5714885682607330714563613)
            ·
              refine ⟨2143082130977749017961355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5714885682607330714563613 2143082130977749017961355)
              ·
                refine ⟨3214623196466623526942033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2143082130977749017961355 3214623196466623526942033)
                ·
                  refine ⟨2410967397349967645206525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3214623196466623526942033 2410967397349967645206525)
                  ·
                    refine ⟨904112774006237866952447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2410967397349967645206525 904112774006237866952447)
                    ·
                      rfl

theorem cell22_2641130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_2641130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2641130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2641130 prefixEnd_2641130 := by exact prefixLift 2641130
  have htrace : WordTrace (prefixWord ++ tailWord_2641130) baseStart_2641130 baseEnd_2641130 := by
    simpa [prefixWord, tailWord_2641130, baseEnd_2641130] using wordTrace_append hprefix tailTrace_2641130
  have hstable : (prefixWord ++ tailWord_2641130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641130).length < 2 ^ (prefixWord ++ tailWord_2641130).sum := by decide
  have hdescent : baseEnd_2641130 < baseStart_2641130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641199 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 8]
def baseStart_2641199 : Nat := 118140960795 + 2641199 * 2 ^ 59
def prefixEnd_2641199 : Nat := 4983230072969 + 3 ^ 40 * 2641199 * 2
def baseEnd_2641199 : Nat := 301378798038781562325745

theorem tailTrace_2641199 : CollatzResearch.WordTrace tailWord_2641199 prefixEnd_2641199 301378798038781562325745 := by
  unfold tailWord_2641199
  simp only [CollatzResearch.WordTrace]
  refine ⟨96332441558394578721926651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64221627705596385814617767 96332441558394578721926651)
  ·
    refine ⟨144498662337591868082889977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96332441558394578721926651 144498662337591868082889977)
    ·
      refine ⟨108373996753193901062167483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144498662337591868082889977 108373996753193901062167483)
      ·
        refine ⟨162560995129790851593251225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108373996753193901062167483 162560995129790851593251225)
        ·
          refine ⟨121920746347343138694938419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162560995129790851593251225 121920746347343138694938419)
          ·
            refine ⟨182881119521014708042407629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121920746347343138694938419 182881119521014708042407629)
            ·
              refine ⟨68580419820380515515902861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182881119521014708042407629 68580419820380515515902861)
              ·
                refine ⟨25717657432642693318463573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68580419820380515515902861 25717657432642693318463573)
                ·
                  refine ⟨301378798038781562325745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25717657432642693318463573 301378798038781562325745)
                  ·
                    rfl

theorem cell22_2641199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 8].length) (baseStart_2641199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2641199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2641199 prefixEnd_2641199 := by exact prefixLift 2641199
  have htrace : WordTrace (prefixWord ++ tailWord_2641199) baseStart_2641199 baseEnd_2641199 := by
    simpa [prefixWord, tailWord_2641199, baseEnd_2641199] using wordTrace_append hprefix tailTrace_2641199
  have hstable : (prefixWord ++ tailWord_2641199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641199).length < 2 ^ (prefixWord ++ tailWord_2641199).sum := by decide
  have hdescent : baseEnd_2641199 < baseStart_2641199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641231 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 8, 3]
def baseStart_2641231 : Nat := 118140960795 + 2641231 * 2 ^ 59
def prefixEnd_2641231 : Nat := 4983230072969 + 3 ^ 40 * 2641231 * 2
def baseEnd_2641231 : Nat := 904147348370307270177137

theorem tailTrace_2641231 : CollatzResearch.WordTrace tailWord_2641231 prefixEnd_2641231 904147348370307270177137 := by
  unfold tailWord_2641231
  simp only [CollatzResearch.WordTrace]
  refine ⟨96333608694278648187091547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64222405796185765458061031 96333608694278648187091547)
  ·
    refine ⟨144500413041417972280637321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96333608694278648187091547 144500413041417972280637321)
    ·
      refine ⟨108375309781063479210477991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144500413041417972280637321 108375309781063479210477991)
      ·
        refine ⟨162562964671595218815716987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108375309781063479210477991 162562964671595218815716987)
        ·
          refine ⟨243844447007392828223575481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162562964671595218815716987 243844447007392828223575481)
          ·
            refine ⟨182883335255544621167681611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243844447007392828223575481 182883335255544621167681611)
            ·
              refine ⟨274325002883316931751522417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182883335255544621167681611 274325002883316931751522417)
              ·
                refine ⟨205743752162487698813641813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 274325002883316931751522417 205743752162487698813641813)
                ·
                  refine ⟨2411059595654152720472365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 205743752162487698813641813 2411059595654152720472365)
                  ·
                    refine ⟨904147348370307270177137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2411059595654152720472365 904147348370307270177137)
                    ·
                      rfl

theorem cell22_2641231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8, 3].length) (baseStart_2641231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2641231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2641231 prefixEnd_2641231 := by exact prefixLift 2641231
  have htrace : WordTrace (prefixWord ++ tailWord_2641231) baseStart_2641231 baseEnd_2641231 := by
    simpa [prefixWord, tailWord_2641231, baseEnd_2641231] using wordTrace_append hprefix tailTrace_2641231
  have hstable : (prefixWord ++ tailWord_2641231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641231).length < 2 ^ (prefixWord ++ tailWord_2641231).sum := by decide
  have hdescent : baseEnd_2641231 < baseStart_2641231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641233 : List Nat := [1, 2, 2, 1, 4, 1, 3, 4, 4]
def baseStart_2641233 : Nat := 118140960795 + 2641233 * 2 ^ 59
def prefixEnd_2641233 : Nat := 4983230072969 + 3 ^ 40 * 2641233 * 2
def baseEnd_2641233 : Nat := 301382677670393310542377

theorem tailTrace_2641233 : CollatzResearch.WordTrace tailWord_2641233 prefixEnd_2641233 301382677670393310542377 := by
  unfold tailWord_2641233
  simp only [CollatzResearch.WordTrace]
  refine ⟨96333681640271402528664353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64222454426847601685776235 96333681640271402528664353)
  ·
    refine ⟨72250261230203551896498265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96333681640271402528664353 72250261230203551896498265)
    ·
      refine ⟨54187695922652663922373699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72250261230203551896498265 54187695922652663922373699)
      ·
        refine ⟨81281543883978995883560549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54187695922652663922373699 81281543883978995883560549)
        ·
          refine ⟨15240289478246061728167603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81281543883978995883560549 15240289478246061728167603)
          ·
            refine ⟨22860434217369092592251405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15240289478246061728167603 22860434217369092592251405)
            ·
              refine ⟨8572662831513409722094277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22860434217369092592251405 8572662831513409722094277)
              ·
                refine ⟨1607374280908764322892677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8572662831513409722094277 1607374280908764322892677)
                ·
                  refine ⟨301382677670393310542377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1607374280908764322892677 301382677670393310542377)
                  ·
                    rfl

theorem cell22_2641233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4, 4].length) (baseStart_2641233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2641233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2641233 prefixEnd_2641233 := by exact prefixLift 2641233
  have htrace : WordTrace (prefixWord ++ tailWord_2641233) baseStart_2641233 baseEnd_2641233 := by
    simpa [prefixWord, tailWord_2641233, baseEnd_2641233] using wordTrace_append hprefix tailTrace_2641233
  have hstable : (prefixWord ++ tailWord_2641233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641233).length < 2 ^ (prefixWord ++ tailWord_2641233).sum := by decide
  have hdescent : baseEnd_2641233 < baseStart_2641233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641248 : List Nat := [2, 1, 1, 3, 4, 2, 2, 1, 1, 5]
def baseStart_2641248 : Nat := 118140960795 + 2641248 * 2 ^ 59
def prefixEnd_2641248 : Nat := 4983230072969 + 3 ^ 40 * 2641248 * 2
def baseEnd_2641248 : Nat := 904153167817724892502085

theorem tailTrace_2641248 : CollatzResearch.WordTrace tailWord_2641248 prefixEnd_2641248 904153167817724892502085 := by
  unfold tailWord_2641248
  simp only [CollatzResearch.WordTrace]
  refine ⟨48167114367608530045230199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64222819156811373393640265 48167114367608530045230199)
  ·
    refine ⟨72250671551412795067845299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48167114367608530045230199 72250671551412795067845299)
    ·
      refine ⟨108376007327119192601767949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72250671551412795067845299 108376007327119192601767949)
      ·
        refine ⟨40641002747669697225662981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108376007327119192601767949 40641002747669697225662981)
        ·
          refine ⟨7620188015188068229811809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40641002747669697225662981 7620188015188068229811809)
          ·
            refine ⟨5715141011391051172358857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7620188015188068229811809 5715141011391051172358857)
            ·
              refine ⟨4286355758543288379269143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5715141011391051172358857 4286355758543288379269143)
              ·
                refine ⟨6429533637814932568903715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4286355758543288379269143 6429533637814932568903715)
                ·
                  refine ⟨9644300456722398853355573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6429533637814932568903715 9644300456722398853355573)
                  ·
                    refine ⟨904153167817724892502085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9644300456722398853355573 904153167817724892502085)
                    ·
                      rfl

theorem cell22_2641248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 1, 5].length) (baseStart_2641248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2641248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2641248 prefixEnd_2641248 := by exact prefixLift 2641248
  have htrace : WordTrace (prefixWord ++ tailWord_2641248) baseStart_2641248 baseEnd_2641248 := by
    simpa [prefixWord, tailWord_2641248, baseEnd_2641248] using wordTrace_append hprefix tailTrace_2641248
  have hstable : (prefixWord ++ tailWord_2641248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641248).length < 2 ^ (prefixWord ++ tailWord_2641248).sum := by decide
  have hdescent : baseEnd_2641248 < baseStart_2641248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641269 : List Nat := [1, 3, 4, 1, 4, 1, 2, 1, 1, 4]
def baseStart_2641269 : Nat := 118140960795 + 2641269 * 2 ^ 59
def prefixEnd_2641269 : Nat := 4983230072969 + 3 ^ 40 * 2641269 * 2
def baseEnd_2641269 : Nat := 904160356546887837727021

theorem tailTrace_2641269 : CollatzResearch.WordTrace tailWord_2641269 prefixEnd_2641269 904160356546887837727021 := by
  unfold tailWord_2641269
  simp only [CollatzResearch.WordTrace]
  refine ⟨96334994668140980676974861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64223329778760653784649907 96334994668140980676974861)
  ·
    refine ⟨36125623000552867753865573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96334994668140980676974861 36125623000552867753865573)
    ·
      refine ⟨6773554312603662703849795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36125623000552867753865573 6773554312603662703849795)
      ·
        refine ⟨10160331468905494055774693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6773554312603662703849795 10160331468905494055774693)
        ·
          refine ⟨1905062150419780135457755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10160331468905494055774693 1905062150419780135457755)
          ·
            refine ⟨2857593225629670203186633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1905062150419780135457755 2857593225629670203186633)
            ·
              refine ⟨2143194919222252652389975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2857593225629670203186633 2143194919222252652389975)
              ·
                refine ⟨3214792378833378978584963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2143194919222252652389975 3214792378833378978584963)
                ·
                  refine ⟨4822188568250068467877445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3214792378833378978584963 4822188568250068467877445)
                  ·
                    refine ⟨904160356546887837727021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4822188568250068467877445 904160356546887837727021)
                    ·
                      rfl

theorem cell22_2641269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_2641269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2641269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2641269 prefixEnd_2641269 := by exact prefixLift 2641269
  have htrace : WordTrace (prefixWord ++ tailWord_2641269) baseStart_2641269 baseEnd_2641269 := by
    simpa [prefixWord, tailWord_2641269, baseEnd_2641269] using wordTrace_append hprefix tailTrace_2641269
  have hstable : (prefixWord ++ tailWord_2641269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641269).length < 2 ^ (prefixWord ++ tailWord_2641269).sum := by decide
  have hdescent : baseEnd_2641269 < baseStart_2641269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641282 : List Nat := [3, 4, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_2641282 : Nat := 118140960795 + 2641282 * 2 ^ 59
def prefixEnd_2641282 : Nat := 4983230072969 + 3 ^ 40 * 2641282 * 2
def baseEnd_2641282 : Nat := 904164806712560137151981

theorem tailTrace_2641282 : CollatzResearch.WordTrace tailWord_2641282 prefixEnd_2641282 904164806712560137151981 := by
  unfold tailWord_2641282
  simp only [CollatzResearch.WordTrace]
  refine ⟨24083867204273470974299525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64223645878062589264798733 24083867204273470974299525)
  ·
    refine ⟨4515725100801275807681161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24083867204273470974299525 4515725100801275807681161)
    ·
      refine ⟨3386793825600956855760871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4515725100801275807681161 3386793825600956855760871)
      ·
        refine ⟨5080190738401435283641307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3386793825600956855760871 5080190738401435283641307)
        ·
          refine ⟨7620286107602152925461961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5080190738401435283641307 7620286107602152925461961)
          ·
            refine ⟨5715214580701614694096471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7620286107602152925461961 5715214580701614694096471)
            ·
              refine ⟨8572821871052422041144707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5715214580701614694096471 8572821871052422041144707)
              ·
                refine ⟨12859232806578633061717061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8572821871052422041144707 12859232806578633061717061)
                ·
                  refine ⟨2411106151233493699071949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12859232806578633061717061 2411106151233493699071949)
                  ·
                    refine ⟨904164806712560137151981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2411106151233493699071949 904164806712560137151981)
                    ·
                      rfl

theorem cell22_2641282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_2641282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2641282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2641282 prefixEnd_2641282 := by exact prefixLift 2641282
  have htrace : WordTrace (prefixWord ++ tailWord_2641282) baseStart_2641282 baseEnd_2641282 := by
    simpa [prefixWord, tailWord_2641282, baseEnd_2641282] using wordTrace_append hprefix tailTrace_2641282
  have hstable : (prefixWord ++ tailWord_2641282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641282).length < 2 ^ (prefixWord ++ tailWord_2641282).sum := by decide
  have hdescent : baseEnd_2641282 < baseStart_2641282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641370 : List Nat := [3, 1, 1, 2, 3, 2, 3, 2, 1, 4]
def baseStart_2641370 : Nat := 118140960795 + 2641370 * 2 ^ 59
def prefixEnd_2641370 : Nat := 4983230072969 + 3 ^ 40 * 2641370 * 2
def baseEnd_2641370 : Nat := 904194930910957240951711

theorem tailTrace_2641370 : CollatzResearch.WordTrace tailWord_2641370 prefixEnd_2641370 904194930910957240951711 := by
  unfold tailWord_2641370
  simp only [CollatzResearch.WordTrace]
  refine ⟨24084669610193768731600391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64225785627183383284267709 24084669610193768731600391)
  ·
    refine ⟨36127004415290653097400587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24084669610193768731600391 36127004415290653097400587)
    ·
      refine ⟨54190506622935979646100881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36127004415290653097400587 54190506622935979646100881)
      ·
        refine ⟨40642879967201984734575661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54190506622935979646100881 40642879967201984734575661)
        ·
          refine ⟨15241079987700744275465873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40642879967201984734575661 15241079987700744275465873)
          ·
            refine ⟨11430809990775558206599405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15241079987700744275465873 11430809990775558206599405)
            ·
              refine ⟨4286553746540834327474777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11430809990775558206599405 4286553746540834327474777)
              ·
                refine ⟨3214915309905625745606083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4286553746540834327474777 3214915309905625745606083)
                ·
                  refine ⟨4822372964858438618409125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3214915309905625745606083 4822372964858438618409125)
                  ·
                    refine ⟨904194930910957240951711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4822372964858438618409125 904194930910957240951711)
                    ·
                      rfl

theorem cell22_2641370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_2641370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2641370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2641370 prefixEnd_2641370 := by exact prefixLift 2641370
  have htrace : WordTrace (prefixWord ++ tailWord_2641370) baseStart_2641370 baseEnd_2641370 := by
    simpa [prefixWord, tailWord_2641370, baseEnd_2641370] using wordTrace_append hprefix tailTrace_2641370
  have hstable : (prefixWord ++ tailWord_2641370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641370).length < 2 ^ (prefixWord ++ tailWord_2641370).sum := by decide
  have hdescent : baseEnd_2641370 < baseStart_2641370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641383 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 3, 5]
def baseStart_2641383 : Nat := 118140960795 + 2641383 * 2 ^ 59
def prefixEnd_2641383 : Nat := 4983230072969 + 3 ^ 40 * 2641383 * 2
def baseEnd_2641383 : Nat := 904199381076629540376671

theorem tailTrace_2641383 : CollatzResearch.WordTrace tailWord_2641383 prefixEnd_2641383 904199381076629540376671 := by
  unfold tailWord_2641383
  simp only [CollatzResearch.WordTrace]
  refine ⟨96339152589727978146624803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64226101726485318764416535 96339152589727978146624803)
  ·
    refine ⟨144508728884591967219937205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96339152589727978146624803 144508728884591967219937205)
    ·
      refine ⟨13547693332930496926869113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144508728884591967219937205 13547693332930496926869113)
      ·
        refine ⟨10160769999697872695151835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13547693332930496926869113 10160769999697872695151835)
        ·
          refine ⟨15241154999546809042727753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10160769999697872695151835 15241154999546809042727753)
          ·
            refine ⟨11430866249660106782045815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15241154999546809042727753 11430866249660106782045815)
            ·
              refine ⟨17146299374490160173068723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11430866249660106782045815 17146299374490160173068723)
              ·
                refine ⟨25719449061735240259603085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17146299374490160173068723 25719449061735240259603085)
                ·
                  refine ⟨9644793398150715097351157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25719449061735240259603085 9644793398150715097351157)
                  ·
                    refine ⟨904199381076629540376671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9644793398150715097351157 904199381076629540376671)
                    ·
                      rfl

theorem cell22_2641383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_2641383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2641383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2641383 prefixEnd_2641383 := by exact prefixLift 2641383
  have htrace : WordTrace (prefixWord ++ tailWord_2641383) baseStart_2641383 baseEnd_2641383 := by
    simpa [prefixWord, tailWord_2641383, baseEnd_2641383] using wordTrace_append hprefix tailTrace_2641383
  have hstable : (prefixWord ++ tailWord_2641383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641383).length < 2 ^ (prefixWord ++ tailWord_2641383).sum := by decide
  have hdescent : baseEnd_2641383 < baseStart_2641383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641400 : List Nat := [2, 1, 2, 1, 1, 5, 1, 4, 2, 3]
def baseStart_2641400 : Nat := 118140960795 + 2641400 * 2 ^ 59
def prefixEnd_2641400 : Nat := 4983230072969 + 3 ^ 40 * 2641400 * 2
def baseEnd_2641400 : Nat := 904205200524047162701619

theorem tailTrace_2641400 : CollatzResearch.WordTrace tailWord_2641400 prefixEnd_2641400 904205200524047162701619 := by
  unfold tailWord_2641400
  simp only [CollatzResearch.WordTrace]
  refine ⟨48169886315333195024996827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64226515087110926699995769 48169886315333195024996827)
  ·
    refine ⟨72254829472999792537495241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48169886315333195024996827 72254829472999792537495241)
    ·
      refine ⟨54191122104749844403121431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72254829472999792537495241 54191122104749844403121431)
      ·
        refine ⟨81286683157124766604682147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54191122104749844403121431 81286683157124766604682147)
        ·
          refine ⟨121930024735687149907023221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81286683157124766604682147 121930024735687149907023221)
          ·
            refine ⟨11430939818970670303783427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121930024735687149907023221 11430939818970670303783427)
            ·
              refine ⟨17146409728456005455675141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11430939818970670303783427 17146409728456005455675141)
              ·
                refine ⟨3214951824085501022939089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17146409728456005455675141 3214951824085501022939089)
                ·
                  refine ⟨2411213868064125767204317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3214951824085501022939089 2411213868064125767204317)
                  ·
                    refine ⟨904205200524047162701619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2411213868064125767204317 904205200524047162701619)
                    ·
                      rfl

theorem cell22_2641400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 2, 3].length) (baseStart_2641400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2641400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2641400 prefixEnd_2641400 := by exact prefixLift 2641400
  have htrace : WordTrace (prefixWord ++ tailWord_2641400) baseStart_2641400 baseEnd_2641400 := by
    simpa [prefixWord, tailWord_2641400, baseEnd_2641400] using wordTrace_append hprefix tailTrace_2641400
  have hstable : (prefixWord ++ tailWord_2641400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641400).length < 2 ^ (prefixWord ++ tailWord_2641400).sum := by decide
  have hdescent : baseEnd_2641400 < baseStart_2641400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641432 : List Nat := [2, 1, 2, 3, 4, 2, 1, 1, 2, 4]
def baseStart_2641432 : Nat := 118140960795 + 2641432 * 2 ^ 59
def prefixEnd_2641432 : Nat := 4983230072969 + 3 ^ 40 * 2641432 * 2
def baseEnd_2641432 : Nat := 904216154778009745901521

theorem tailTrace_2641432 : CollatzResearch.WordTrace tailWord_2641432 prefixEnd_2641432 904216154778009745901521 := by
  unfold tailWord_2641432
  simp only [CollatzResearch.WordTrace]
  refine ⟨48170469883275229757579275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64227293177700306343439033 48170469883275229757579275)
  ·
    refine ⟨72255704824912844636368913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48170469883275229757579275 72255704824912844636368913)
    ·
      refine ⟨54191778618684633477276685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72255704824912844636368913 54191778618684633477276685)
      ·
        refine ⟨20321916982006737553978757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54191778618684633477276685 20321916982006737553978757)
        ·
          refine ⟨3810359434126263291371017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20321916982006737553978757 3810359434126263291371017)
          ·
            refine ⟨2857769575594697468528263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3810359434126263291371017 2857769575594697468528263)
            ·
              refine ⟨4286654363392046202792395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2857769575594697468528263 4286654363392046202792395)
              ·
                refine ⟨6429981545088069304188593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4286654363392046202792395 6429981545088069304188593)
                ·
                  refine ⟨4822486158816051978141445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6429981545088069304188593 4822486158816051978141445)
                  ·
                    refine ⟨904216154778009745901521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4822486158816051978141445 904216154778009745901521)
                    ·
                      rfl

theorem cell22_2641432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 2, 4].length) (baseStart_2641432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2641432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2641432 prefixEnd_2641432 := by exact prefixLift 2641432
  have htrace : WordTrace (prefixWord ++ tailWord_2641432) baseStart_2641432 baseEnd_2641432 := by
    simpa [prefixWord, tailWord_2641432, baseEnd_2641432] using wordTrace_append hprefix tailTrace_2641432
  have hstable : (prefixWord ++ tailWord_2641432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641432).length < 2 ^ (prefixWord ++ tailWord_2641432).sum := by decide
  have hdescent : baseEnd_2641432 < baseStart_2641432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641505 : List Nat := [1, 2, 3, 1, 1, 3, 1, 5, 1, 4]
def baseStart_2641505 : Nat := 118140960795 + 2641505 * 2 ^ 59
def prefixEnd_2641505 : Nat := 4983230072969 + 3 ^ 40 * 2641505 * 2
def baseEnd_2641505 : Nat := 904241144169861888826297

theorem tailTrace_2641505 : CollatzResearch.WordTrace tailWord_2641505 prefixEnd_2641505 904241144169861888826297 := by
  unfold tailWord_2641505
  simp only [CollatzResearch.WordTrace]
  refine ⟨96343602295285992982565969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64229068196857328655043979 96343602295285992982565969)
  ·
    refine ⟨72257701721464494736924477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96343602295285992982565969 72257701721464494736924477)
    ·
      refine ⟨27096638145549185526346679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72257701721464494736924477 27096638145549185526346679)
      ·
        refine ⟨40644957218323778289520019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27096638145549185526346679 40644957218323778289520019)
        ·
          refine ⟨60967435827485667434280029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40644957218323778289520019 60967435827485667434280029)
          ·
            refine ⟨22862788435307125287855011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60967435827485667434280029 22862788435307125287855011)
            ·
              refine ⟨34294182652960687931782517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22862788435307125287855011 34294182652960687931782517)
              ·
                refine ⟨3215079623715064493604611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34294182652960687931782517 3215079623715064493604611)
                ·
                  refine ⟨4822619435572596740406917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3215079623715064493604611 4822619435572596740406917)
                  ·
                    refine ⟨904241144169861888826297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4822619435572596740406917 904241144169861888826297)
                    ·
                      rfl

theorem cell22_2641505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_2641505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2641505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2641505 prefixEnd_2641505 := by exact prefixLift 2641505
  have htrace : WordTrace (prefixWord ++ tailWord_2641505) baseStart_2641505 baseEnd_2641505 := by
    simpa [prefixWord, tailWord_2641505, baseEnd_2641505] using wordTrace_append hprefix tailTrace_2641505
  have hstable : (prefixWord ++ tailWord_2641505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641505).length < 2 ^ (prefixWord ++ tailWord_2641505).sum := by decide
  have hdescent : baseEnd_2641505 < baseStart_2641505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641520 : List Nat := [2, 1, 1, 1, 6, 1, 3, 1, 6]
def baseStart_2641520 : Nat := 118140960795 + 2641520 * 2 ^ 59
def prefixEnd_2641520 : Nat := 4983230072969 + 3 ^ 40 * 2641520 * 2
def baseEnd_2641520 : Nat := 301415426325468949900417

theorem tailTrace_2641520 : CollatzResearch.WordTrace tailWord_2641520 prefixEnd_2641520 301415426325468949900417 := by
  unfold tailWord_2641520
  simp only [CollatzResearch.WordTrace]
  refine ⟨48172074695115825272181007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64229432926821100362908009 48172074695115825272181007)
  ·
    refine ⟨72258112042673737908271511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48172074695115825272181007 72258112042673737908271511)
    ·
      refine ⟨108387168064010606862407267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72258112042673737908271511 108387168064010606862407267)
      ·
        refine ⟨162580752096015910293610901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108387168064010606862407267 162580752096015910293610901)
        ·
          refine ⟨7620972754500745795013011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 162580752096015910293610901 7620972754500745795013011)
          ·
            refine ⟨11431459131751118692519517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7620972754500745795013011 11431459131751118692519517)
            ·
              refine ⟨4286797174406669509694819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11431459131751118692519517 4286797174406669509694819)
              ·
                refine ⟨6430195761610004264542229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4286797174406669509694819 6430195761610004264542229)
                ·
                  refine ⟨301415426325468949900417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6430195761610004264542229 301415426325468949900417)
                  ·
                    rfl

theorem cell22_2641520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 6].length) (baseStart_2641520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2641520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2641520 prefixEnd_2641520 := by exact prefixLift 2641520
  have htrace : WordTrace (prefixWord ++ tailWord_2641520) baseStart_2641520 baseEnd_2641520 := by
    simpa [prefixWord, tailWord_2641520, baseEnd_2641520] using wordTrace_append hprefix tailTrace_2641520
  have hstable : (prefixWord ++ tailWord_2641520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641520).length < 2 ^ (prefixWord ++ tailWord_2641520).sum := by decide
  have hdescent : baseEnd_2641520 < baseStart_2641520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641548 : List Nat := [2, 2, 1, 2, 1, 1, 3, 10]
def baseStart_2641548 : Nat := 118140960795 + 2641548 * 2 ^ 59
def prefixEnd_2641548 : Nat := 4983230072969 + 3 ^ 40 * 2641548 * 2
def baseEnd_2641548 : Nat := 100472873772069345555685

theorem tailTrace_2641548 : CollatzResearch.WordTrace tailWord_2641548 prefixEnd_2641548 100472873772069345555685 := by
  unfold tailWord_2641548
  simp only [CollatzResearch.WordTrace]
  refine ⟨48172585317065105663190649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64230113756086807550920865 48172585317065105663190649)
  ·
    refine ⟨36129438987798829247392987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48172585317065105663190649 36129438987798829247392987)
    ·
      refine ⟨54194158481698243871089481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36129438987798829247392987 54194158481698243871089481)
      ·
        refine ⟨40645618861273682903317111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54194158481698243871089481 40645618861273682903317111)
        ·
          refine ⟨60968428291910524354975667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40645618861273682903317111 60968428291910524354975667)
          ·
            refine ⟨91452642437865786532463501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60968428291910524354975667 91452642437865786532463501)
            ·
              refine ⟨34294740914199669949673813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91452642437865786532463501 34294740914199669949673813)
              ·
                refine ⟨100472873772069345555685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34294740914199669949673813 100472873772069345555685)
                ·
                  rfl

theorem cell22_2641548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 10].length) (baseStart_2641548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2641548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2641548 prefixEnd_2641548 := by exact prefixLift 2641548
  have htrace : WordTrace (prefixWord ++ tailWord_2641548) baseStart_2641548 baseEnd_2641548 := by
    simpa [prefixWord, tailWord_2641548, baseEnd_2641548] using wordTrace_append hprefix tailTrace_2641548
  have hstable : (prefixWord ++ tailWord_2641548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641548).length < 2 ^ (prefixWord ++ tailWord_2641548).sum := by decide
  have hdescent : baseEnd_2641548 < baseStart_2641548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641556 : List Nat := [2, 4, 2, 2, 2, 1, 3, 1, 1, 4]
def baseStart_2641556 : Nat := 118140960795 + 2641556 * 2 ^ 59
def prefixEnd_2641556 : Nat := 4983230072969 + 3 ^ 40 * 2641556 * 2
def baseEnd_2641556 : Nat := 904258602512114755801141

theorem tailTrace_2641556 : CollatzResearch.WordTrace tailWord_2641556 prefixEnd_2641556 904258602512114755801141 := by
  unfold tailWord_2641556
  simp only [CollatzResearch.WordTrace]
  refine ⟨48172731209050614346336261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64230308278734152461781681 48172731209050614346336261)
  ·
    refine ⟨9032387101696990189938049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48172731209050614346336261 9032387101696990189938049)
    ·
      refine ⟨6774290326272742642453537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9032387101696990189938049 6774290326272742642453537)
      ·
        refine ⟨5080717744704556981840153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6774290326272742642453537 5080717744704556981840153)
        ·
          refine ⟨3810538308528417736380115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5080717744704556981840153 3810538308528417736380115)
          ·
            refine ⟨5715807462792626604570173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3810538308528417736380115 5715807462792626604570173)
            ·
              refine ⟨2143427798547234976713815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5715807462792626604570173 2143427798547234976713815)
              ·
                refine ⟨3215141697820852465070723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2143427798547234976713815 3215141697820852465070723)
                ·
                  refine ⟨4822712546731278697606085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3215141697820852465070723 4822712546731278697606085)
                  ·
                    refine ⟨904258602512114755801141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4822712546731278697606085 904258602512114755801141)
                    ·
                      rfl

theorem cell22_2641556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_2641556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2641556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2641556 prefixEnd_2641556 := by exact prefixLift 2641556
  have htrace : WordTrace (prefixWord ++ tailWord_2641556) baseStart_2641556 baseEnd_2641556 := by
    simpa [prefixWord, tailWord_2641556, baseEnd_2641556] using wordTrace_append hprefix tailTrace_2641556
  have hstable : (prefixWord ++ tailWord_2641556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641556).length < 2 ^ (prefixWord ++ tailWord_2641556).sum := by decide
  have hdescent : baseEnd_2641556 < baseStart_2641556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641569 : List Nat := [1, 2, 3, 3, 2, 2, 2, 2, 2, 3]
def baseStart_2641569 : Nat := 118140960795 + 2641569 * 2 ^ 59
def prefixEnd_2641569 : Nat := 4983230072969 + 3 ^ 40 * 2641569 * 2
def baseEnd_2641569 : Nat := 904263052677787055226101

theorem tailTrace_2641569 : CollatzResearch.WordTrace tailWord_2641569 prefixEnd_2641569 904263052677787055226101 := by
  unfold tailWord_2641569
  simp only [CollatzResearch.WordTrace]
  refine ⟨96345936567054131912895761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64230624378036087941930507 96345936567054131912895761)
  ·
    refine ⟨72259452425290598934671821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96345936567054131912895761 72259452425290598934671821)
    ·
      refine ⟨27097294659483974600501933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72259452425290598934671821 27097294659483974600501933)
      ·
        refine ⟨10161485497306490475188225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27097294659483974600501933 10161485497306490475188225)
        ·
          refine ⟨7621114122979867856391169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10161485497306490475188225 7621114122979867856391169)
          ·
            refine ⟨5715835592234900892293377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7621114122979867856391169 5715835592234900892293377)
            ·
              refine ⟨4286876694176175669220033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5715835592234900892293377 4286876694176175669220033)
              ·
                refine ⟨3215157520632131751915025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4286876694176175669220033 3215157520632131751915025)
                ·
                  refine ⟨2411368140474098813936269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3215157520632131751915025 2411368140474098813936269)
                  ·
                    refine ⟨904263052677787055226101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2411368140474098813936269 904263052677787055226101)
                    ·
                      rfl

theorem cell22_2641569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_2641569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2641569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2641569 prefixEnd_2641569 := by exact prefixLift 2641569
  have htrace : WordTrace (prefixWord ++ tailWord_2641569) baseStart_2641569 baseEnd_2641569 := by
    simpa [prefixWord, tailWord_2641569, baseEnd_2641569] using wordTrace_append hprefix tailTrace_2641569
  have hstable : (prefixWord ++ tailWord_2641569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641569).length < 2 ^ (prefixWord ++ tailWord_2641569).sum := by decide
  have hdescent : baseEnd_2641569 < baseStart_2641569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641580 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 9, 3]
def baseStart_2641580 : Nat := 118140960795 + 2641580 * 2 ^ 59
def prefixEnd_2641580 : Nat := 4983230072969 + 3 ^ 40 * 2641580 * 2
def baseEnd_2641580 : Nat := 904266818202586693201067

theorem tailTrace_2641580 : CollatzResearch.WordTrace tailWord_2641580 prefixEnd_2641580 904266818202586693201067 := by
  unfold tailWord_2641580
  simp only [CollatzResearch.WordTrace]
  refine ⟨48173168885007140395773097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64230891846676187194364129 48173168885007140395773097)
  ·
    refine ⟨36129876663755355296829823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48173168885007140395773097 36129876663755355296829823)
    ·
      refine ⟨54194814995633032945244735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36129876663755355296829823 54194814995633032945244735)
      ·
        refine ⟨81292222493449549417867103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54194814995633032945244735 81292222493449549417867103)
        ·
          refine ⟨121938333740174324126800655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81292222493449549417867103 121938333740174324126800655)
          ·
            refine ⟨182907500610261486190200983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121938333740174324126800655 182907500610261486190200983)
            ·
              refine ⟨274361250915392229285301475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182907500610261486190200983 274361250915392229285301475)
              ·
                refine ⟨411541876373088343927952213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274361250915392229285301475 411541876373088343927952213)
                ·
                  refine ⟨2411378181873564515202845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 411541876373088343927952213 2411378181873564515202845)
                  ·
                    refine ⟨904266818202586693201067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2411378181873564515202845 904266818202586693201067)
                    ·
                      rfl

theorem cell22_2641580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 3].length) (baseStart_2641580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2641580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2641580 prefixEnd_2641580 := by exact prefixLift 2641580
  have htrace : WordTrace (prefixWord ++ tailWord_2641580) baseStart_2641580 baseEnd_2641580 := by
    simpa [prefixWord, tailWord_2641580, baseEnd_2641580] using wordTrace_append hprefix tailTrace_2641580
  have hstable : (prefixWord ++ tailWord_2641580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641580).length < 2 ^ (prefixWord ++ tailWord_2641580).sum := by decide
  have hdescent : baseEnd_2641580 < baseStart_2641580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641597 : List Nat := [1, 4, 1, 2, 1, 2, 3, 2, 3, 3]
def baseStart_2641597 : Nat := 118140960795 + 2641597 * 2 ^ 59
def prefixEnd_2641597 : Nat := 4983230072969 + 3 ^ 40 * 2641597 * 2
def baseEnd_2641597 : Nat := 904272637650004315526015

theorem tailTrace_2641597 : CollatzResearch.WordTrace tailWord_2641597 prefixEnd_2641597 904272637650004315526015 := by
  unfold tailWord_2641597
  simp only [CollatzResearch.WordTrace]
  refine ⟨96346957810952692694915045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64231305207301795129943363 96346957810952692694915045)
  ·
    refine ⟨18065054589553629880296571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96346957810952692694915045 18065054589553629880296571)
    ·
      refine ⟨27097581884330444820444857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18065054589553629880296571 27097581884330444820444857)
      ·
        refine ⟨20323186413247833615333643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27097581884330444820444857 20323186413247833615333643)
        ·
          refine ⟨30484779619871750423000465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20323186413247833615333643 30484779619871750423000465)
          ·
            refine ⟨22863584714903812817250349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30484779619871750423000465 22863584714903812817250349)
            ·
              refine ⟨8573844268088929806468881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22863584714903812817250349 8573844268088929806468881)
              ·
                refine ⟨6430383201066697354851661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8573844268088929806468881 6430383201066697354851661)
                ·
                  refine ⟨2411393700400011508069373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6430383201066697354851661 2411393700400011508069373)
                  ·
                    refine ⟨904272637650004315526015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2411393700400011508069373 904272637650004315526015)
                    ·
                      rfl

theorem cell22_2641597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_2641597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2641597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2641597 prefixEnd_2641597 := by exact prefixLift 2641597
  have htrace : WordTrace (prefixWord ++ tailWord_2641597) baseStart_2641597 baseEnd_2641597 := by
    simpa [prefixWord, tailWord_2641597, baseEnd_2641597] using wordTrace_append hprefix tailTrace_2641597
  have hstable : (prefixWord ++ tailWord_2641597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641597).length < 2 ^ (prefixWord ++ tailWord_2641597).sum := by decide
  have hdescent : baseEnd_2641597 < baseStart_2641597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641625 : List Nat := [1, 2, 1, 2, 3, 3, 1, 2, 2, 5]
def baseStart_2641625 : Nat := 118140960795 + 2641625 * 2 ^ 59
def prefixEnd_2641625 : Nat := 4983230072969 + 3 ^ 40 * 2641625 * 2
def baseEnd_2641625 : Nat := 904282222622221575825929

theorem tailTrace_2641625 : CollatzResearch.WordTrace tailWord_2641625 prefixEnd_2641625 904282222622221575825929 := by
  unfold tailWord_2641625
  simp only [CollatzResearch.WordTrace]
  refine ⟨96347979054851253476934329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64231986036567502317956219 96347979054851253476934329)
  ·
    refine ⟨72260984291138440107700747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96347979054851253476934329 72260984291138440107700747)
    ·
      refine ⟨108391476436707660161551121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72260984291138440107700747 108391476436707660161551121)
      ·
        refine ⟨81293607327530745121163341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108391476436707660161551121 81293607327530745121163341)
        ·
          refine ⟨30485102747824029420436253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81293607327530745121163341 30485102747824029420436253)
          ·
            refine ⟨11431913530434011032663595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30485102747824029420436253 11431913530434011032663595)
            ·
              refine ⟨17147870295651016548995393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11431913530434011032663595 17147870295651016548995393)
              ·
                refine ⟨12860902721738262411746545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17147870295651016548995393 12860902721738262411746545)
                ·
                  refine ⟨9645677041303696808809909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12860902721738262411746545 9645677041303696808809909)
                  ·
                    refine ⟨904282222622221575825929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9645677041303696808809909 904282222622221575825929)
                    ·
                      rfl

theorem cell22_2641625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 5].length) (baseStart_2641625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2641625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2641625 prefixEnd_2641625 := by exact prefixLift 2641625
  have htrace : WordTrace (prefixWord ++ tailWord_2641625) baseStart_2641625 baseEnd_2641625 := by
    simpa [prefixWord, tailWord_2641625, baseEnd_2641625] using wordTrace_append hprefix tailTrace_2641625
  have hstable : (prefixWord ++ tailWord_2641625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641625).length < 2 ^ (prefixWord ++ tailWord_2641625).sum := by decide
  have hdescent : baseEnd_2641625 < baseStart_2641625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641655 : List Nat := [1, 1, 3, 1, 1, 1, 6, 2, 6]
def baseStart_2641655 : Nat := 118140960795 + 2641655 * 2 ^ 59
def prefixEnd_2641655 : Nat := 4983230072969 + 3 ^ 40 * 2641655 * 2
def baseEnd_2641655 : Nat := 301430830745103832525279

theorem tailTrace_2641655 : CollatzResearch.WordTrace tailWord_2641655 prefixEnd_2641655 301430830745103832525279 := by
  unfold tailWord_2641655
  simp only [CollatzResearch.WordTrace]
  refine ⟨96349073244742568600526419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64232715496495045733684279 96349073244742568600526419)
  ·
    refine ⟨144523609867113852900789629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96349073244742568600526419 144523609867113852900789629)
    ·
      refine ⟨54196353700167694837796111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144523609867113852900789629 54196353700167694837796111)
      ·
        refine ⟨81294530550251542256694167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54196353700167694837796111 81294530550251542256694167)
        ·
          refine ⟨121941795825377313385041251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81294530550251542256694167 121941795825377313385041251)
          ·
            refine ⟨182912693738065970077561877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121941795825377313385041251 182912693738065970077561877)
            ·
              refine ⟨8574032518971842347385713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 182912693738065970077561877 8574032518971842347385713)
              ·
                refine ⟨6430524389228881760539285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8574032518971842347385713 6430524389228881760539285)
                ·
                  refine ⟨301430830745103832525279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6430524389228881760539285 301430830745103832525279)
                  ·
                    rfl

theorem cell22_2641655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 6].length) (baseStart_2641655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2641655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2641655 prefixEnd_2641655 := by exact prefixLift 2641655
  have htrace : WordTrace (prefixWord ++ tailWord_2641655) baseStart_2641655 baseEnd_2641655 := by
    simpa [prefixWord, tailWord_2641655, baseEnd_2641655] using wordTrace_append hprefix tailTrace_2641655
  have hstable : (prefixWord ++ tailWord_2641655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641655).length < 2 ^ (prefixWord ++ tailWord_2641655).sum := by decide
  have hdescent : baseEnd_2641655 < baseStart_2641655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641734 : List Nat := [6, 1, 1, 2, 1, 11]
def baseStart_2641734 : Nat := 118140960795 + 2641734 * 2 ^ 59
def prefixEnd_2641734 : Nat := 4983230072969 + 3 ^ 40 * 2641734 * 2
def baseEnd_2641734 : Nat := 11164438710491131170995

theorem tailTrace_2641734 : CollatzResearch.WordTrace tailWord_2641734 prefixEnd_2641734 11164438710491131170995 := by
  unfold tailWord_2641734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3010998581608011409145383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 64234636407637576728434837 3010998581608011409145383)
  ·
    refine ⟨4516497872412017113718075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3010998581608011409145383 4516497872412017113718075)
    ·
      refine ⟨6774746808618025670577113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4516497872412017113718075 6774746808618025670577113)
      ·
        refine ⟨5081060106463519252932835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6774746808618025670577113 5081060106463519252932835)
        ·
          refine ⟨7621590159695278879399253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5081060106463519252932835 7621590159695278879399253)
          ·
            refine ⟨11164438710491131170995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7621590159695278879399253 11164438710491131170995)
            ·
              rfl

theorem cell22_2641734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 11].length) (baseStart_2641734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2641734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2641734 prefixEnd_2641734 := by exact prefixLift 2641734
  have htrace : WordTrace (prefixWord ++ tailWord_2641734) baseStart_2641734 baseEnd_2641734 := by
    simpa [prefixWord, tailWord_2641734, baseEnd_2641734] using wordTrace_append hprefix tailTrace_2641734
  have hstable : (prefixWord ++ tailWord_2641734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641734).length < 2 ^ (prefixWord ++ tailWord_2641734).sum := by decide
  have hdescent : baseEnd_2641734 < baseStart_2641734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641841 : List Nat := [1, 2, 2, 4, 2, 1, 3, 3, 4]
def baseStart_2641841 : Nat := 118140960795 + 2641841 * 2 ^ 59
def prefixEnd_2641841 : Nat := 4983230072969 + 3 ^ 40 * 2641841 * 2
def baseEnd_2641841 : Nat := 301452054612156337475089

theorem tailTrace_2641841 : CollatzResearch.WordTrace tailWord_2641841 prefixEnd_2641841 301452054612156337475089 := by
  unfold tailWord_2641841
  simp only [CollatzResearch.WordTrace]
  refine ⟨96355857222068722366797377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64237238148045814911198251 96355857222068722366797377)
  ·
    refine ⟨72266892916551541775098033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96355857222068722366797377 72266892916551541775098033)
    ·
      refine ⟨54200169687413656331323525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72266892916551541775098033 54200169687413656331323525)
      ·
        refine ⟨10162531816390060562123161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54200169687413656331323525 10162531816390060562123161)
        ·
          refine ⟨7621898862292545421592371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10162531816390060562123161 7621898862292545421592371)
          ·
            refine ⟨11432848293438818132388557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7621898862292545421592371 11432848293438818132388557)
            ·
              refine ⟨4287318110039556799645709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11432848293438818132388557 4287318110039556799645709)
              ·
                refine ⟨1607744291264833799867141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4287318110039556799645709 1607744291264833799867141)
                ·
                  refine ⟨301452054612156337475089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1607744291264833799867141 301452054612156337475089)
                  ·
                    rfl

theorem cell22_2641841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3, 4].length) (baseStart_2641841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2641841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2641841 prefixEnd_2641841 := by exact prefixLift 2641841
  have htrace : WordTrace (prefixWord ++ tailWord_2641841) baseStart_2641841 baseEnd_2641841 := by
    simpa [prefixWord, tailWord_2641841, baseEnd_2641841] using wordTrace_append hprefix tailTrace_2641841
  have hstable : (prefixWord ++ tailWord_2641841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641841).length < 2 ^ (prefixWord ++ tailWord_2641841).sum := by decide
  have hdescent : baseEnd_2641841 < baseStart_2641841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641854 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_2641854 : Nat := 118140960795 + 2641854 * 2 ^ 59
def prefixEnd_2641854 : Nat := 4983230072969 + 3 ^ 40 * 2641854 * 2
def baseEnd_2641854 : Nat := 904360614002141311850227

theorem tailTrace_2641854 : CollatzResearch.WordTrace tailWord_2641854 prefixEnd_2641854 904360614002141311850227 := by
  unfold tailWord_2641854
  simp only [CollatzResearch.WordTrace]
  refine ⟨12044541421377703198377577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64237554247347750391347077 12044541421377703198377577)
  ·
    refine ⟨9033406066033277398783183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12044541421377703198377577 9033406066033277398783183)
    ·
      refine ⟨13550109099049916098174775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9033406066033277398783183 13550109099049916098174775)
      ·
        refine ⟨20325163648574874147262163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13550109099049916098174775 20325163648574874147262163)
        ·
          refine ⟨30487745472862311220893245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20325163648574874147262163 30487745472862311220893245)
          ·
            refine ⟨11432904552323366707834967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30487745472862311220893245 11432904552323366707834967)
            ·
              refine ⟨17149356828485050061752451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11432904552323366707834967 17149356828485050061752451)
              ·
                refine ⟨25724035242727575092628677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17149356828485050061752451 25724035242727575092628677)
                ·
                  refine ⟨4823256608011420329867877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25724035242727575092628677 4823256608011420329867877)
                  ·
                    refine ⟨904360614002141311850227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4823256608011420329867877 904360614002141311850227)
                    ·
                      rfl

theorem cell22_2641854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_2641854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2641854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2641854 prefixEnd_2641854 := by exact prefixLift 2641854
  have htrace : WordTrace (prefixWord ++ tailWord_2641854) baseStart_2641854 baseEnd_2641854 := by
    simpa [prefixWord, tailWord_2641854, baseEnd_2641854] using wordTrace_append hprefix tailTrace_2641854
  have hstable : (prefixWord ++ tailWord_2641854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641854).length < 2 ^ (prefixWord ++ tailWord_2641854).sum := by decide
  have hdescent : baseEnd_2641854 < baseStart_2641854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641944 : List Nat := [2, 1, 2, 3, 2, 1, 1, 3, 3, 4]
def baseStart_2641944 : Nat := 118140960795 + 2641944 * 2 ^ 59
def prefixEnd_2641944 : Nat := 4983230072969 + 3 ^ 40 * 2641944 * 2
def baseEnd_2641944 : Nat := 904391422841411077099951

theorem tailTrace_2641944 : CollatzResearch.WordTrace tailWord_2641944 prefixEnd_2641944 904391422841411077099951 := by
  unfold tailWord_2641944
  simp only [CollatzResearch.WordTrace]
  refine ⟨48179806970347785478898443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64239742627130380638531257 48179806970347785478898443)
  ·
    refine ⟨72269710455521678218347665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48179806970347785478898443 72269710455521678218347665)
    ·
      refine ⟨54202282841641258663760749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72269710455521678218347665 54202282841641258663760749)
      ·
        refine ⟨20325856065615471998910281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54202282841641258663760749 20325856065615471998910281)
        ·
          refine ⟨15244392049211603999182711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20325856065615471998910281 15244392049211603999182711)
          ·
            refine ⟨22866588073817405998774067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15244392049211603999182711 22866588073817405998774067)
            ·
              refine ⟨34299882110726108998161101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22866588073817405998774067 34299882110726108998161101)
              ·
                refine ⟨12862455791522290874310413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34299882110726108998161101 12862455791522290874310413)
                ·
                  refine ⟨4823420921820859077866405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12862455791522290874310413 4823420921820859077866405)
                  ·
                    refine ⟨904391422841411077099951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4823420921820859077866405 904391422841411077099951)
                    ·
                      rfl

theorem cell22_2641944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_2641944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2641944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2641944 prefixEnd_2641944 := by exact prefixLift 2641944
  have htrace : WordTrace (prefixWord ++ tailWord_2641944) baseStart_2641944 baseEnd_2641944 := by
    simpa [prefixWord, tailWord_2641944, baseEnd_2641944] using wordTrace_append hprefix tailTrace_2641944
  have hstable : (prefixWord ++ tailWord_2641944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641944).length < 2 ^ (prefixWord ++ tailWord_2641944).sum := by decide
  have hdescent : baseEnd_2641944 < baseStart_2641944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641976 : List Nat := [2, 1, 2, 1, 6, 1, 2, 1, 6]
def baseStart_2641976 : Nat := 118140960795 + 2641976 * 2 ^ 59
def prefixEnd_2641976 : Nat := 4983230072969 + 3 ^ 40 * 2641976 * 2
def baseEnd_2641976 : Nat := 301467459031791220099951

theorem tailTrace_2641976 : CollatzResearch.WordTrace tailWord_2641976 prefixEnd_2641976 301467459031791220099951 := by
  unfold tailWord_2641976
  simp only [CollatzResearch.WordTrace]
  refine ⟨48180390538289820211480891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64240520717719760281974521 48180390538289820211480891)
  ·
    refine ⟨72270585807434730317221337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48180390538289820211480891 72270585807434730317221337)
    ·
      refine ⟨54202939355576047737916003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72270585807434730317221337 54202939355576047737916003)
      ·
        refine ⟨81304409033364071606874005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54202939355576047737916003 81304409033364071606874005)
        ·
          refine ⟨3811144173438940856572219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 81304409033364071606874005 3811144173438940856572219)
          ·
            refine ⟨5716716260158411284858329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3811144173438940856572219 5716716260158411284858329)
            ·
              refine ⟨4287537195118808463643747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5716716260158411284858329 4287537195118808463643747)
              ·
                refine ⟨6431305792678212695465621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4287537195118808463643747 6431305792678212695465621)
                ·
                  refine ⟨301467459031791220099951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6431305792678212695465621 301467459031791220099951)
                  ·
                    rfl

theorem cell22_2641976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 6].length) (baseStart_2641976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2641976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2641976 prefixEnd_2641976 := by exact prefixLift 2641976
  have htrace : WordTrace (prefixWord ++ tailWord_2641976) baseStart_2641976 baseEnd_2641976 := by
    simpa [prefixWord, tailWord_2641976, baseEnd_2641976] using wordTrace_append hprefix tailTrace_2641976
  have hstable : (prefixWord ++ tailWord_2641976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641976).length < 2 ^ (prefixWord ++ tailWord_2641976).sum := by decide
  have hdescent : baseEnd_2641976 < baseStart_2641976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642087 : List Nat := [1, 1, 6, 2, 2, 1, 1, 4, 1, 3]
def baseStart_2642087 : Nat := 118140960795 + 2642087 * 2 ^ 59
def prefixEnd_2642087 : Nat := 4983230072969 + 3 ^ 40 * 2642087 * 2
def baseEnd_2642087 : Nat := 904440374663806370774513

theorem tailTrace_2642087 : CollatzResearch.WordTrace tailWord_2642087 prefixEnd_2642087 904440374663806370774513 := by
  unfold tailWord_2642087
  simp only [CollatzResearch.WordTrace]
  refine ⟨96364829579177506380252515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64243219719451670920168343 96364829579177506380252515)
  ·
    refine ⟨144547244368766259570378773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96364829579177506380252515 144547244368766259570378773)
    ·
      refine ⟨6775652079785918417361505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 144547244368766259570378773 6775652079785918417361505)
      ·
        refine ⟨5081739059839438813021129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6775652079785918417361505 5081739059839438813021129)
        ·
          refine ⟨3811304294879579109765847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5081739059839438813021129 3811304294879579109765847)
          ·
            refine ⟨5716956442319368664648771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3811304294879579109765847 5716956442319368664648771)
            ·
              refine ⟨8575434663479052996973157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5716956442319368664648771 8575434663479052996973157)
              ·
                refine ⟨1607893999402322436932467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8575434663479052996973157 1607893999402322436932467)
                ·
                  refine ⟨2411840999103483655398701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1607893999402322436932467 2411840999103483655398701)
                  ·
                    refine ⟨904440374663806370774513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2411840999103483655398701 904440374663806370774513)
                    ·
                      rfl

theorem cell22_2642087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_2642087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2642087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2642087 prefixEnd_2642087 := by exact prefixLift 2642087
  have htrace : WordTrace (prefixWord ++ tailWord_2642087) baseStart_2642087 baseEnd_2642087 := by
    simpa [prefixWord, tailWord_2642087, baseEnd_2642087] using wordTrace_append hprefix tailTrace_2642087
  have hstable : (prefixWord ++ tailWord_2642087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642087).length < 2 ^ (prefixWord ++ tailWord_2642087).sum := by decide
  have hdescent : baseEnd_2642087 < baseStart_2642087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642130 : List Nat := [3, 2, 2, 2, 1, 2, 4, 1, 1, 4]
def baseStart_2642130 : Nat := 118140960795 + 2642130 * 2 ^ 59
def prefixEnd_2642130 : Nat := 4983230072969 + 3 ^ 40 * 2642130 * 2
def baseEnd_2642130 : Nat := 904455094442568591949381

theorem tailTrace_2642130 : CollatzResearch.WordTrace tailWord_2642130 prefixEnd_2642130 904455094442568591949381 := by
  unfold tailWord_2642130
  simp only [CollatzResearch.WordTrace]
  refine ⟨24091599479505431181016961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64244265278681149816045229 24091599479505431181016961)
  ·
    refine ⟨18068699609629073385762721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24091599479505431181016961 18068699609629073385762721)
    ·
      refine ⟨13551524707221805039322041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18068699609629073385762721 13551524707221805039322041)
      ·
        refine ⟨10163643530416353779491531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13551524707221805039322041 10163643530416353779491531)
        ·
          refine ⟨15245465295624530669237297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10163643530416353779491531 15245465295624530669237297)
          ·
            refine ⟨11434098971718398001927973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15245465295624530669237297 11434098971718398001927973)
            ·
              refine ⟨2143893557197199625361495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11434098971718398001927973 2143893557197199625361495)
              ·
                refine ⟨3215840335795799438042243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2143893557197199625361495 3215840335795799438042243)
                ·
                  refine ⟨4823760503693699157063365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3215840335795799438042243 4823760503693699157063365)
                  ·
                    refine ⟨904455094442568591949381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4823760503693699157063365 904455094442568591949381)
                    ·
                      rfl

theorem cell22_2642130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_2642130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2642130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2642130 prefixEnd_2642130 := by exact prefixLift 2642130
  have htrace : WordTrace (prefixWord ++ tailWord_2642130) baseStart_2642130 baseEnd_2642130 := by
    simpa [prefixWord, tailWord_2642130, baseEnd_2642130] using wordTrace_append hprefix tailTrace_2642130
  have hstable : (prefixWord ++ tailWord_2642130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642130).length < 2 ^ (prefixWord ++ tailWord_2642130).sum := by decide
  have hdescent : baseEnd_2642130 < baseStart_2642130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642248 : List Nat := [2, 1, 3, 1, 1, 2, 2, 5, 1, 4]
def baseStart_2642248 : Nat := 118140960795 + 2642248 * 2 ^ 59
def prefixEnd_2642248 : Nat := 4983230072969 + 3 ^ 40 * 2642248 * 2
def baseEnd_2642248 : Nat := 904495488254055617499019

theorem tailTrace_2642248 : CollatzResearch.WordTrace tailWord_2642248 prefixEnd_2642248 904495488254055617499019 := by
  unfold tailWord_2642248
  simp only [CollatzResearch.WordTrace]
  refine ⟨48185350865797115438431699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64247134487729487251242265 48185350865797115438431699)
  ·
    refine ⟨72278026298695673157647549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48185350865797115438431699 72278026298695673157647549)
    ·
      refine ⟨27104259862010877434117831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72278026298695673157647549 27104259862010877434117831)
      ·
        refine ⟨40656389793016316151176747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27104259862010877434117831 40656389793016316151176747)
        ·
          refine ⟨60984584689524474226765121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40656389793016316151176747 60984584689524474226765121)
          ·
            refine ⟨45738438517143355670073841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60984584689524474226765121 45738438517143355670073841)
            ·
              refine ⟨34303828887857516752555381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45738438517143355670073841 34303828887857516752555381)
              ·
                refine ⟨3215983958236642195552067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34303828887857516752555381 3215983958236642195552067)
                ·
                  refine ⟨4823975937354963293328101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3215983958236642195552067 4823975937354963293328101)
                  ·
                    refine ⟨904495488254055617499019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4823975937354963293328101 904495488254055617499019)
                    ·
                      rfl

theorem cell22_2642248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_2642248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2642248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2642248 prefixEnd_2642248 := by exact prefixLift 2642248
  have htrace : WordTrace (prefixWord ++ tailWord_2642248) baseStart_2642248 baseEnd_2642248 := by
    simpa [prefixWord, tailWord_2642248, baseEnd_2642248] using wordTrace_append hprefix tailTrace_2642248
  have hstable : (prefixWord ++ tailWord_2642248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642248).length < 2 ^ (prefixWord ++ tailWord_2642248).sum := by decide
  have hdescent : baseEnd_2642248 < baseStart_2642248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642340 : List Nat := [2, 3, 1, 2, 1, 1, 4, 2, 3, 3]
def baseStart_2642340 : Nat := 118140960795 + 2642340 * 2 ^ 59
def prefixEnd_2642340 : Nat := 4983230072969 + 3 ^ 40 * 2642340 * 2
def baseEnd_2642340 : Nat := 904526981734198044198737

theorem tailTrace_2642340 : CollatzResearch.WordTrace tailWord_2642340 prefixEnd_2642340 904526981734198044198737 := by
  unfold tailWord_2642340
  simp only [CollatzResearch.WordTrace]
  refine ⟨48187028623630465294606237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64249371498173953726141649 48187028623630465294606237)
  ·
    refine ⟨18070135733861424485477339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48187028623630465294606237 18070135733861424485477339)
    ·
      refine ⟨27105203600792136728216009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18070135733861424485477339 27105203600792136728216009)
      ·
        refine ⟨20328902700594102546162007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27105203600792136728216009 20328902700594102546162007)
        ·
          refine ⟨30493354050891153819243011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20328902700594102546162007 30493354050891153819243011)
          ·
            refine ⟨45740031076336730728864517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30493354050891153819243011 45740031076336730728864517)
            ·
              refine ⟨8576255826813137011662097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45740031076336730728864517 8576255826813137011662097)
              ·
                refine ⟨6432191870109852758746573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8576255826813137011662097 6432191870109852758746573)
                ·
                  refine ⟨2412071951291194784529965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6432191870109852758746573 2412071951291194784529965)
                  ·
                    refine ⟨904526981734198044198737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2412071951291194784529965 904526981734198044198737)
                    ·
                      rfl

theorem cell22_2642340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_2642340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2642340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2642340 prefixEnd_2642340 := by exact prefixLift 2642340
  have htrace : WordTrace (prefixWord ++ tailWord_2642340) baseStart_2642340 baseEnd_2642340 := by
    simpa [prefixWord, tailWord_2642340, baseEnd_2642340] using wordTrace_append hprefix tailTrace_2642340
  have hstable : (prefixWord ++ tailWord_2642340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642340).length < 2 ^ (prefixWord ++ tailWord_2642340).sum := by decide
  have hdescent : baseEnd_2642340 < baseStart_2642340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642353 : List Nat := [1, 2, 2, 4, 1, 2, 1, 2, 7]
def baseStart_2642353 : Nat := 118140960795 + 2642353 * 2 ^ 59
def prefixEnd_2642353 : Nat := 4983230072969 + 3 ^ 40 * 2642353 * 2
def baseEnd_2642353 : Nat := 301510477299956781207899

theorem tailTrace_2642353 : CollatzResearch.WordTrace tailWord_2642353 prefixEnd_2642353 301510477299956781207899 := by
  unfold tailWord_2642353
  simp only [CollatzResearch.WordTrace]
  refine ⟨96374531396213833809435713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64249687597475889206290475 96374531396213833809435713)
  ·
    refine ⟨72280898547160375357076785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96374531396213833809435713 72280898547160375357076785)
    ·
      refine ⟨54210673910370281517807589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72280898547160375357076785 54210673910370281517807589)
      ·
        refine ⟨10164501358194427784588923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54210673910370281517807589 10164501358194427784588923)
        ·
          refine ⟨15246752037291641676883385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10164501358194427784588923 15246752037291641676883385)
          ·
            refine ⟨11435064027968731257662539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15246752037291641676883385 11435064027968731257662539)
            ·
              refine ⟨17152596041953096886493809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11435064027968731257662539 17152596041953096886493809)
              ·
                refine ⟨12864447031464822664870357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17152596041953096886493809 12864447031464822664870357)
                ·
                  refine ⟨301510477299956781207899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12864447031464822664870357 301510477299956781207899)
                  ·
                    rfl

theorem cell22_2642353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 7].length) (baseStart_2642353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2642353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2642353 prefixEnd_2642353 := by exact prefixLift 2642353
  have htrace : WordTrace (prefixWord ++ tailWord_2642353) baseStart_2642353 baseEnd_2642353 := by
    simpa [prefixWord, tailWord_2642353, baseEnd_2642353] using wordTrace_append hprefix tailTrace_2642353
  have hstable : (prefixWord ++ tailWord_2642353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642353).length < 2 ^ (prefixWord ++ tailWord_2642353).sum := by decide
  have hdescent : baseEnd_2642353 < baseStart_2642353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642383 : List Nat := [1, 1, 2, 1, 1, 4, 1, 4, 3, 4]
def baseStart_2642383 : Nat := 118140960795 + 2642383 * 2 ^ 59
def prefixEnd_2642383 : Nat := 4983230072969 + 3 ^ 40 * 2642383 * 2
def baseEnd_2642383 : Nat := 904541701512960265373605

theorem tailTrace_2642383 : CollatzResearch.WordTrace tailWord_2642383 prefixEnd_2642383 904541701512960265373605 := by
  unfold tailWord_2642383
  simp only [CollatzResearch.WordTrace]
  refine ⟨96375625586105148933027803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64250417057403432622018535 96375625586105148933027803)
  ·
    refine ⟨144563438379157723399541705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96375625586105148933027803 144563438379157723399541705)
    ·
      refine ⟨108422578784368292549656279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144563438379157723399541705 108422578784368292549656279)
      ·
        refine ⟨162633868176552438824484419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108422578784368292549656279 162633868176552438824484419)
        ·
          refine ⟨243950802264828658236726629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162633868176552438824484419 243950802264828658236726629)
          ·
            refine ⟨45740775424655373419386243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 243950802264828658236726629 45740775424655373419386243)
            ·
              refine ⟨68611163136983060129079365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45740775424655373419386243 68611163136983060129079365)
              ·
                refine ⟨12864593088184323774202381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68611163136983060129079365 12864593088184323774202381)
                ·
                  refine ⟨4824222408069121415325893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12864593088184323774202381 4824222408069121415325893)
                  ·
                    refine ⟨904541701512960265373605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4824222408069121415325893 904541701512960265373605)
                    ·
                      rfl

theorem cell22_2642383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 4].length) (baseStart_2642383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2642383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2642383 prefixEnd_2642383 := by exact prefixLift 2642383
  have htrace : WordTrace (prefixWord ++ tailWord_2642383) baseStart_2642383 baseEnd_2642383 := by
    simpa [prefixWord, tailWord_2642383, baseEnd_2642383] using wordTrace_append hprefix tailTrace_2642383
  have hstable : (prefixWord ++ tailWord_2642383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642383).length < 2 ^ (prefixWord ++ tailWord_2642383).sum := by decide
  have hdescent : baseEnd_2642383 < baseStart_2642383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642415 : List Nat := [1, 1, 2, 1, 4, 1, 1, 7, 4]
def baseStart_2642415 : Nat := 118140960795 + 2642415 * 2 ^ 59
def prefixEnd_2642415 : Nat := 4983230072969 + 3 ^ 40 * 2642415 * 2
def baseEnd_2642415 : Nat := 301517551922307616191169

theorem tailTrace_2642415 : CollatzResearch.WordTrace tailWord_2642415 prefixEnd_2642415 301517551922307616191169 := by
  unfold tailWord_2642415
  simp only [CollatzResearch.WordTrace]
  refine ⟨96376792721989218398192699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64251195147992812265461799 96376792721989218398192699)
  ·
    refine ⟨144565189082983827597289049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96376792721989218398192699 144565189082983827597289049)
    ·
      refine ⟨108423891812237870697966787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144565189082983827597289049 108423891812237870697966787)
      ·
        refine ⟨162635837718356806046950181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108423891812237870697966787 162635837718356806046950181)
        ·
          refine ⟨30494219572191901133803159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162635837718356806046950181 30494219572191901133803159)
          ·
            refine ⟨45741329358287851700704739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30494219572191901133803159 45741329358287851700704739)
            ·
              refine ⟨68611994037431777551057109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45741329358287851700704739 68611994037431777551057109)
              ·
                refine ⟨1608093610252307286352901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 68611994037431777551057109 1608093610252307286352901)
                ·
                  refine ⟨301517551922307616191169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1608093610252307286352901 301517551922307616191169)
                  ·
                    rfl

theorem cell22_2642415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7, 4].length) (baseStart_2642415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2642415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2642415 prefixEnd_2642415 := by exact prefixLift 2642415
  have htrace : WordTrace (prefixWord ++ tailWord_2642415) baseStart_2642415 baseEnd_2642415 := by
    simpa [prefixWord, tailWord_2642415, baseEnd_2642415] using wordTrace_append hprefix tailTrace_2642415
  have hstable : (prefixWord ++ tailWord_2642415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642415).length < 2 ^ (prefixWord ++ tailWord_2642415).sum := by decide
  have hdescent : baseEnd_2642415 < baseStart_2642415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642417 : List Nat := [1, 2, 2, 2, 3, 1, 5, 1, 1, 4]
def baseStart_2642417 : Nat := 118140960795 + 2642417 * 2 ^ 59
def prefixEnd_2642417 : Nat := 4983230072969 + 3 ^ 40 * 2642417 * 2
def baseEnd_2642417 : Nat := 904553340407795510023501

theorem tailTrace_2642417 : CollatzResearch.WordTrace tailWord_2642417 prefixEnd_2642417 904553340407795510023501 := by
  unfold tailWord_2642417
  simp only [CollatzResearch.WordTrace]
  refine ⟨96376865667981972739765505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64251243778654648493177003 96376865667981972739765505)
  ·
    refine ⟨72282649250986479554824129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96376865667981972739765505 72282649250986479554824129)
    ·
      refine ⟨54211986938239859666118097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72282649250986479554824129 54211986938239859666118097)
      ·
        refine ⟨40658990203679894749588573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54211986938239859666118097 40658990203679894749588573)
        ·
          refine ⟨15247121326379960531095715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40658990203679894749588573 15247121326379960531095715)
          ·
            refine ⟨22870681989569940796643573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15247121326379960531095715 22870681989569940796643573)
            ·
              refine ⟨2144126436522181949685335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22870681989569940796643573 2144126436522181949685335)
              ·
                refine ⟨3216189654783272924528003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2144126436522181949685335 3216189654783272924528003)
                ·
                  refine ⟨4824284482174909386792005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3216189654783272924528003 4824284482174909386792005)
                  ·
                    refine ⟨904553340407795510023501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4824284482174909386792005 904553340407795510023501)
                    ·
                      rfl

theorem cell22_2642417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 1, 4].length) (baseStart_2642417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2642417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2642417 prefixEnd_2642417 := by exact prefixLift 2642417
  have htrace : WordTrace (prefixWord ++ tailWord_2642417) baseStart_2642417 baseEnd_2642417 := by
    simpa [prefixWord, tailWord_2642417, baseEnd_2642417] using wordTrace_append hprefix tailTrace_2642417
  have hstable : (prefixWord ++ tailWord_2642417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642417).length < 2 ^ (prefixWord ++ tailWord_2642417).sum := by decide
  have hdescent : baseEnd_2642417 < baseStart_2642417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642428 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 3, 6]
def baseStart_2642428 : Nat := 118140960795 + 2642428 * 2 ^ 59
def prefixEnd_2642428 : Nat := 4983230072969 + 3 ^ 40 * 2642428 * 2
def baseEnd_2642428 : Nat := 904557105932595147998467

theorem tailTrace_2642428 : CollatzResearch.WordTrace tailWord_2642428 prefixEnd_2642428 904557105932595147998467 := by
  unfold tailWord_2642428
  simp only [CollatzResearch.WordTrace]
  refine ⟨48188633435471060809207969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64251511247294747745610625 48188633435471060809207969)
  ·
    refine ⟨36141475076603295606905977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48188633435471060809207969 36141475076603295606905977)
    ·
      refine ⟨27106106307452471705179483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36141475076603295606905977 27106106307452471705179483)
      ·
        refine ⟨40659159461178707557769225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27106106307452471705179483 40659159461178707557769225)
        ·
          refine ⟨30494369595884030668326919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40659159461178707557769225 30494369595884030668326919)
          ·
            refine ⟨45741554393826046002490379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30494369595884030668326919 45741554393826046002490379)
            ·
              refine ⟨68612331590739069003735569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45741554393826046002490379 68612331590739069003735569)
              ·
                refine ⟨51459248693054301752801677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68612331590739069003735569 51459248693054301752801677)
                ·
                  refine ⟨19297218259895363157300629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51459248693054301752801677 19297218259895363157300629)
                  ·
                    refine ⟨904557105932595147998467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19297218259895363157300629 904557105932595147998467)
                    ·
                      rfl

theorem cell22_2642428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_2642428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2642428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2642428 prefixEnd_2642428 := by exact prefixLift 2642428
  have htrace : WordTrace (prefixWord ++ tailWord_2642428) baseStart_2642428 baseEnd_2642428 := by
    simpa [prefixWord, tailWord_2642428, baseEnd_2642428] using wordTrace_append hprefix tailTrace_2642428
  have hstable : (prefixWord ++ tailWord_2642428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642428).length < 2 ^ (prefixWord ++ tailWord_2642428).sum := by decide
  have hdescent : baseEnd_2642428 < baseStart_2642428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642468 : List Nat := [2, 3, 1, 5, 2, 1, 2, 1, 1, 4]
def baseStart_2642468 : Nat := 118140960795 + 2642468 * 2 ^ 59
def prefixEnd_2642468 : Nat := 4983230072969 + 3 ^ 40 * 2642468 * 2
def baseEnd_2642468 : Nat := 904570798750048376998345

theorem tailTrace_2642468 : CollatzResearch.WordTrace tailWord_2642468 prefixEnd_2642468 904570798750048376998345 := by
  unfold tailWord_2642468
  simp only [CollatzResearch.WordTrace]
  refine ⟨48189362895398604224936029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64252483860531472299914705 48189362895398604224936029)
  ·
    refine ⟨18071011085774476584351011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48189362895398604224936029 18071011085774476584351011)
    ·
      refine ⟨27106516628661714876526517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18071011085774476584351011 27106516628661714876526517)
      ·
        refine ⟨2541235933937035769674361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27106516628661714876526517 2541235933937035769674361)
        ·
          refine ⟨1905926950452776827255771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2541235933937035769674361 1905926950452776827255771)
          ·
            refine ⟨2858890425679165240883657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1905926950452776827255771 2858890425679165240883657)
            ·
              refine ⟨2144167819259373930662743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2858890425679165240883657 2144167819259373930662743)
              ·
                refine ⟨3216251728889060895994115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2144167819259373930662743 3216251728889060895994115)
                ·
                  refine ⟨4824377593333591343991173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3216251728889060895994115 4824377593333591343991173)
                  ·
                    refine ⟨904570798750048376998345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4824377593333591343991173 904570798750048376998345)
                    ·
                      rfl

theorem cell22_2642468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_2642468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2642468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2642468 prefixEnd_2642468 := by exact prefixLift 2642468
  have htrace : WordTrace (prefixWord ++ tailWord_2642468) baseStart_2642468 baseEnd_2642468 := by
    simpa [prefixWord, tailWord_2642468, baseEnd_2642468] using wordTrace_append hprefix tailTrace_2642468
  have hstable : (prefixWord ++ tailWord_2642468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642468).length < 2 ^ (prefixWord ++ tailWord_2642468).sum := by decide
  have hdescent : baseEnd_2642468 < baseStart_2642468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642492 : List Nat := [2, 2, 2, 2, 3, 1, 1, 3, 3, 3]
def baseStart_2642492 : Nat := 118140960795 + 2642492 * 2 ^ 59
def prefixEnd_2642492 : Nat := 4983230072969 + 3 ^ 40 * 2642492 * 2
def baseEnd_2642492 : Nat := 904579014440520314398271

theorem tailTrace_2642492 : CollatzResearch.WordTrace tailWord_2642492 prefixEnd_2642492 904579014440520314398271 := by
  unfold tailWord_2642492
  simp only [CollatzResearch.WordTrace]
  refine ⟨48189800571355130274372865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64253067428473507032497153 48189800571355130274372865)
  ·
    refine ⟨36142350428516347705779649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48189800571355130274372865 36142350428516347705779649)
    ·
      refine ⟨27106762821387260779334737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36142350428516347705779649 27106762821387260779334737)
      ·
        refine ⟨20330072116040445584501053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27106762821387260779334737 20330072116040445584501053)
        ·
          refine ⟨7623777043515167094187895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20330072116040445584501053 7623777043515167094187895)
          ·
            refine ⟨11435665565272750641281843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7623777043515167094187895 11435665565272750641281843)
            ·
              refine ⟨17153498347909125961922765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11435665565272750641281843 17153498347909125961922765)
              ·
                refine ⟨6432561880465922235721037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17153498347909125961922765 6432561880465922235721037)
                ·
                  refine ⟨2412210705174720838395389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6432561880465922235721037 2412210705174720838395389)
                  ·
                    refine ⟨904579014440520314398271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2412210705174720838395389 904579014440520314398271)
                    ·
                      rfl

theorem cell22_2642492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_2642492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2642492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2642492 prefixEnd_2642492 := by exact prefixLift 2642492
  have htrace : WordTrace (prefixWord ++ tailWord_2642492) baseStart_2642492 baseEnd_2642492 := by
    simpa [prefixWord, tailWord_2642492, baseEnd_2642492] using wordTrace_append hprefix tailTrace_2642492
  have hstable : (prefixWord ++ tailWord_2642492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642492).length < 2 ^ (prefixWord ++ tailWord_2642492).sum := by decide
  have hdescent : baseEnd_2642492 < baseStart_2642492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642509 : List Nat := [1, 6, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_2642509 : Nat := 118140960795 + 2642509 * 2 ^ 59
def prefixEnd_2642509 : Nat := 4983230072969 + 3 ^ 40 * 2642509 * 2
def baseEnd_2642509 : Nat := 904584833887937936723219

theorem tailTrace_2642509 : CollatzResearch.WordTrace tailWord_2642509 prefixEnd_2642509 904584833887937936723219 := by
  unfold tailWord_2642509
  simp only [CollatzResearch.WordTrace]
  refine ⟨96380221183648672452114581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64253480789099114968076387 96380221183648672452114581)
  ·
    refine ⟨4517822867983531521192871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 96380221183648672452114581 4517822867983531521192871)
    ·
      refine ⟨6776734301975297281789307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4517822867983531521192871 6776734301975297281789307)
      ·
        refine ⟨10165101452962945922683961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6776734301975297281789307 10165101452962945922683961)
        ·
          refine ⟨7623826089722209442012971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10165101452962945922683961 7623826089722209442012971)
          ·
            refine ⟨11435739134583314163019457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7623826089722209442012971 11435739134583314163019457)
            ·
              refine ⟨8576804350937485622264593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11435739134583314163019457 8576804350937485622264593)
              ·
                refine ⟨6432603263203114216698445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8576804350937485622264593 6432603263203114216698445)
                ·
                  refine ⟨2412226223701167831261917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6432603263203114216698445 2412226223701167831261917)
                  ·
                    refine ⟨904584833887937936723219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2412226223701167831261917 904584833887937936723219)
                    ·
                      rfl

theorem cell22_2642509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_2642509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2642509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2642509 prefixEnd_2642509 := by exact prefixLift 2642509
  have htrace : WordTrace (prefixWord ++ tailWord_2642509) baseStart_2642509 baseEnd_2642509 := by
    simpa [prefixWord, tailWord_2642509, baseEnd_2642509] using wordTrace_append hprefix tailTrace_2642509
  have hstable : (prefixWord ++ tailWord_2642509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642509).length < 2 ^ (prefixWord ++ tailWord_2642509).sum := by decide
  have hdescent : baseEnd_2642509 < baseStart_2642509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642535 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 5, 4]
def baseStart_2642535 : Nat := 118140960795 + 2642535 * 2 ^ 59
def prefixEnd_2642535 : Nat := 4983230072969 + 3 ^ 40 * 2642535 * 2
def baseEnd_2642535 : Nat := 904593734219282535573139

theorem tailTrace_2642535 : CollatzResearch.WordTrace tailWord_2642535 prefixEnd_2642535 904593734219282535573139 := by
  unfold tailWord_2642535
  simp only [CollatzResearch.WordTrace]
  refine ⟨96381169481554478892561059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64254112987702985928374039 96381169481554478892561059)
  ·
    refine ⟨144571754222331718338841589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96381169481554478892561059 144571754222331718338841589)
    ·
      refine ⟨13553601958343598594266399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144571754222331718338841589 13553601958343598594266399)
      ·
        refine ⟨20330402937515397891399599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13553601958343598594266399 20330402937515397891399599)
        ·
          refine ⟨30495604406273096837099399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20330402937515397891399599 30495604406273096837099399)
          ·
            refine ⟨45743406609409645255649099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30495604406273096837099399 45743406609409645255649099)
            ·
              refine ⟨68615109914114467883473649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45743406609409645255649099 68615109914114467883473649)
              ·
                refine ⟨51461332435585850912605237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68615109914114467883473649 51461332435585850912605237)
                ·
                  refine ⟨4824499915836173523056741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51461332435585850912605237 4824499915836173523056741)
                  ·
                    refine ⟨904593734219282535573139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4824499915836173523056741 904593734219282535573139)
                    ·
                      rfl

theorem cell22_2642535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_2642535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2642535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2642535 prefixEnd_2642535 := by exact prefixLift 2642535
  have htrace : WordTrace (prefixWord ++ tailWord_2642535) baseStart_2642535 baseEnd_2642535 := by
    simpa [prefixWord, tailWord_2642535, baseEnd_2642535] using wordTrace_append hprefix tailTrace_2642535
  have hstable : (prefixWord ++ tailWord_2642535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642535).length < 2 ^ (prefixWord ++ tailWord_2642535).sum := by decide
  have hdescent : baseEnd_2642535 < baseStart_2642535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642610 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 2, 7]
def baseStart_2642610 : Nat := 118140960795 + 2642610 * 2 ^ 59
def prefixEnd_2642610 : Nat := 4983230072969 + 3 ^ 40 * 2642610 * 2
def baseEnd_2642610 : Nat := 904619408252007339947909

theorem tailTrace_2642610 : CollatzResearch.WordTrace tailWord_2642610 prefixEnd_2642610 904619408252007339947909 := by
  unfold tailWord_2642610
  simp only [CollatzResearch.WordTrace]
  refine ⟨24095976239070691675385321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64255936637521844467694189 24095976239070691675385321)
  ·
    refine ⟨18071982179303018756538991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24095976239070691675385321 18071982179303018756538991)
    ·
      refine ⟨27107973268954528134808487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18071982179303018756538991 27107973268954528134808487)
      ·
        refine ⟨40661959903431792202212731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27107973268954528134808487 40661959903431792202212731)
        ·
          refine ⟨60992939855147688303319097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40661959903431792202212731 60992939855147688303319097)
          ·
            refine ⟨45744704891360766227489323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60992939855147688303319097 45744704891360766227489323)
            ·
              refine ⟨68617057337041149341233985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45744704891360766227489323 68617057337041149341233985)
              ·
                refine ⟨51462793002780862005925489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68617057337041149341233985 51462793002780862005925489)
                ·
                  refine ⟨38597094752085646504444117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51462793002780862005925489 38597094752085646504444117)
                  ·
                    refine ⟨904619408252007339947909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38597094752085646504444117 904619408252007339947909)
                    ·
                      rfl

theorem cell22_2642610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_2642610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2642610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2642610 prefixEnd_2642610 := by exact prefixLift 2642610
  have htrace : WordTrace (prefixWord ++ tailWord_2642610) baseStart_2642610 baseEnd_2642610 := by
    simpa [prefixWord, tailWord_2642610, baseEnd_2642610] using wordTrace_append hprefix tailTrace_2642610
  have hstable : (prefixWord ++ tailWord_2642610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642610).length < 2 ^ (prefixWord ++ tailWord_2642610).sum := by decide
  have hdescent : baseEnd_2642610 < baseStart_2642610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642657 : List Nat := [1, 2, 3, 1, 4, 2, 1, 1, 7]
def baseStart_2642657 : Nat := 118140960795 + 2642657 * 2 ^ 59
def prefixEnd_2642657 : Nat := 4983230072969 + 3 ^ 40 * 2642657 * 2
def baseEnd_2642657 : Nat := 301545165770838294674255

theorem tailTrace_2642657 : CollatzResearch.WordTrace tailWord_2642657 prefixEnd_2642657 301545165770838294674255 := by
  unfold tailWord_2642657
  simp only [CollatzResearch.WordTrace]
  refine ⟨96385619187112493728502225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64257079458074995819001483 96385619187112493728502225)
  ·
    refine ⟨72289214390334370296376669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96385619187112493728502225 72289214390334370296376669)
    ·
      refine ⟨27108455396375388861141251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72289214390334370296376669 27108455396375388861141251)
      ·
        refine ⟨40662683094563083291711877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27108455396375388861141251 40662683094563083291711877)
        ·
          refine ⟨7624253080230578117195977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40662683094563083291711877 7624253080230578117195977)
          ·
            refine ⟨5718189810172933587896983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7624253080230578117195977 5718189810172933587896983)
            ·
              refine ⟨8577284715259400381845475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5718189810172933587896983 8577284715259400381845475)
              ·
                refine ⟨12865927072889100572768213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8577284715259400381845475 12865927072889100572768213)
                ·
                  refine ⟨301545165770838294674255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12865927072889100572768213 301545165770838294674255)
                  ·
                    rfl

theorem cell22_2642657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 7].length) (baseStart_2642657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2642657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2642657 prefixEnd_2642657 := by exact prefixLift 2642657
  have htrace : WordTrace (prefixWord ++ tailWord_2642657) baseStart_2642657 baseEnd_2642657 := by
    simpa [prefixWord, tailWord_2642657, baseEnd_2642657] using wordTrace_append hprefix tailTrace_2642657
  have hstable : (prefixWord ++ tailWord_2642657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642657).length < 2 ^ (prefixWord ++ tailWord_2642657).sum := by decide
  have hdescent : baseEnd_2642657 < baseStart_2642657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642661 : List Nat := [1, 3, 1, 4, 1, 2, 2, 4, 1, 3]
def baseStart_2642661 : Nat := 118140960795 + 2642661 * 2 ^ 59
def prefixEnd_2642661 : Nat := 4983230072969 + 3 ^ 40 * 2642661 * 2
def baseEnd_2642661 : Nat := 904636866594260206922753

theorem tailTrace_2642661 : CollatzResearch.WordTrace tailWord_2642661 prefixEnd_2642661 904636866594260206922753 := by
  unfold tailWord_2642661
  simp only [CollatzResearch.WordTrace]
  refine ⟨96385765079098002411647837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64257176719398668274431891 96385765079098002411647837)
  ·
    refine ⟨36144661904661750904367939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96385765079098002411647837 36144661904661750904367939)
    ·
      refine ⟨54216992856992626356551909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36144661904661750904367939 54216992856992626356551909)
      ·
        refine ⟨10165686160686117441853483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54216992856992626356551909 10165686160686117441853483)
        ·
          refine ⟨15248529241029176162780225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10165686160686117441853483 15248529241029176162780225)
          ·
            refine ⟨11436396930771882122085169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15248529241029176162780225 11436396930771882122085169)
            ·
              refine ⟨8577297698078911591563877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11436396930771882122085169 8577297698078911591563877)
              ·
                refine ⟨1608243318389795923418227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8577297698078911591563877 1608243318389795923418227)
                ·
                  refine ⟨2412364977584693885127341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1608243318389795923418227 2412364977584693885127341)
                  ·
                    refine ⟨904636866594260206922753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2412364977584693885127341 904636866594260206922753)
                    ·
                      rfl

theorem cell22_2642661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4, 1, 3].length) (baseStart_2642661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2642661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2642661 prefixEnd_2642661 := by exact prefixLift 2642661
  have htrace : WordTrace (prefixWord ++ tailWord_2642661) baseStart_2642661 baseEnd_2642661 := by
    simpa [prefixWord, tailWord_2642661, baseEnd_2642661] using wordTrace_append hprefix tailTrace_2642661
  have hstable : (prefixWord ++ tailWord_2642661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642661).length < 2 ^ (prefixWord ++ tailWord_2642661).sum := by decide
  have hdescent : baseEnd_2642661 < baseStart_2642661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642719 : List Nat := [1, 1, 2, 4, 2, 4, 1, 1, 6]
def baseStart_2642719 : Nat := 118140960795 + 2642719 * 2 ^ 59
def prefixEnd_2642719 : Nat := 4983230072969 + 3 ^ 40 * 2642719 * 2
def baseEnd_2642719 : Nat := 301552240393189129657525

theorem tailTrace_2642719 : CollatzResearch.WordTrace tailWord_2642719 prefixEnd_2642719 301552240393189129657525 := by
  unfold tailWord_2642719
  simp only [CollatzResearch.WordTrace]
  refine ⟨96387880512887878317259211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64258587008591918878172807 96387880512887878317259211)
  ·
    refine ⟨144581820769331817475888817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96387880512887878317259211 144581820769331817475888817)
    ·
      refine ⟨108436365576998863106916613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144581820769331817475888817 108436365576998863106916613)
      ·
        refine ⟨20331818545687286832546865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108436365576998863106916613 20331818545687286832546865)
        ·
          refine ⟨15248863909265465124410149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20331818545687286832546865 15248863909265465124410149)
          ·
            refine ⟨2859161982987274710826903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15248863909265465124410149 2859161982987274710826903)
            ·
              refine ⟨4288742974480912066240355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2859161982987274710826903 4288742974480912066240355)
              ·
                refine ⟨6433114461721368099360533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4288742974480912066240355 6433114461721368099360533)
                ·
                  refine ⟨301552240393189129657525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6433114461721368099360533 301552240393189129657525)
                  ·
                    rfl

theorem cell22_2642719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 6].length) (baseStart_2642719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2642719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2642719 prefixEnd_2642719 := by exact prefixLift 2642719
  have htrace : WordTrace (prefixWord ++ tailWord_2642719) baseStart_2642719 baseEnd_2642719 := by
    simpa [prefixWord, tailWord_2642719, baseEnd_2642719] using wordTrace_append hprefix tailTrace_2642719
  have hstable : (prefixWord ++ tailWord_2642719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642719).length < 2 ^ (prefixWord ++ tailWord_2642719).sum := by decide
  have hdescent : baseEnd_2642719 < baseStart_2642719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642732 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 4, 4]
def baseStart_2642732 : Nat := 118140960795 + 2642732 * 2 ^ 59
def prefixEnd_2642732 : Nat := 4983230072969 + 3 ^ 40 * 2642732 * 2
def baseEnd_2642732 : Nat := 904661171345239688397535

theorem tailTrace_2642732 : CollatzResearch.WordTrace tailWord_2642732 prefixEnd_2642732 904661171345239688397535 := by
  unfold tailWord_2642732
  simp only [CollatzResearch.WordTrace]
  refine ⟨48194177330920390768741225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64258903107893854358321633 48194177330920390768741225)
  ·
    refine ⟨36145632998190293076555919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48194177330920390768741225 36145632998190293076555919)
    ·
      refine ⟨54218449497285439614833879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36145632998190293076555919 54218449497285439614833879)
      ·
        refine ⟨81327674245928159422250819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54218449497285439614833879 81327674245928159422250819)
        ·
          refine ⟨121991511368892239133376229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81327674245928159422250819 121991511368892239133376229)
          ·
            refine ⟨22873408381667294837508043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121991511368892239133376229 22873408381667294837508043)
            ·
              refine ⟨34310112572500942256262065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22873408381667294837508043 34310112572500942256262065)
              ·
                refine ⟨25732584429375706692196549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34310112572500942256262065 25732584429375706692196549)
                ·
                  refine ⟨4824859580507945004786853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25732584429375706692196549 4824859580507945004786853)
                  ·
                    refine ⟨904661171345239688397535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4824859580507945004786853 904661171345239688397535)
                    ·
                      rfl

theorem cell22_2642732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_2642732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2642732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2642732 prefixEnd_2642732 := by exact prefixLift 2642732
  have htrace : WordTrace (prefixWord ++ tailWord_2642732) baseStart_2642732 baseEnd_2642732 := by
    simpa [prefixWord, tailWord_2642732, baseEnd_2642732] using wordTrace_append hprefix tailTrace_2642732
  have hstable : (prefixWord ++ tailWord_2642732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642732).length < 2 ^ (prefixWord ++ tailWord_2642732).sum := by decide
  have hdescent : baseEnd_2642732 < baseStart_2642732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642777 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 2, 6]
def baseStart_2642777 : Nat := 118140960795 + 2642777 * 2 ^ 59
def prefixEnd_2642777 : Nat := 4983230072969 + 3 ^ 40 * 2642777 * 2
def baseEnd_2642777 : Nat := 904676575764874571022397

theorem tailTrace_2642777 : CollatzResearch.WordTrace tailWord_2642777 prefixEnd_2642777 904676575764874571022397 := by
  unfold tailWord_2642777
  simp only [CollatzResearch.WordTrace]
  refine ⟨96389995946677754222870585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64259997297785169481913723 96389995946677754222870585)
  ·
    refine ⟨72292496960008315667152939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96389995946677754222870585 72292496960008315667152939)
    ·
      refine ⟨108438745440012473500729409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72292496960008315667152939 108438745440012473500729409)
      ·
        refine ⟨81329059080009355125547057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108438745440012473500729409 81329059080009355125547057)
        ·
          refine ⟨60996794310007016344160293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81329059080009355125547057 60996794310007016344160293)
          ·
            refine ⟨11436898933126315564530055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60996794310007016344160293 11436898933126315564530055)
            ·
              refine ⟨17155348399689473346795083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11436898933126315564530055 17155348399689473346795083)
              ·
                refine ⟨25733022599534210020192625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17155348399689473346795083 25733022599534210020192625)
                ·
                  refine ⟨19299766949650657515144469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25733022599534210020192625 19299766949650657515144469)
                  ·
                    refine ⟨904676575764874571022397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19299766949650657515144469 904676575764874571022397)
                    ·
                      rfl

theorem cell22_2642777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 6].length) (baseStart_2642777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2642777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2642777 prefixEnd_2642777 := by exact prefixLift 2642777
  have htrace : WordTrace (prefixWord ++ tailWord_2642777) baseStart_2642777 baseEnd_2642777 := by
    simpa [prefixWord, tailWord_2642777, baseEnd_2642777] using wordTrace_append hprefix tailTrace_2642777
  have hstable : (prefixWord ++ tailWord_2642777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642777).length < 2 ^ (prefixWord ++ tailWord_2642777).sum := by decide
  have hdescent : baseEnd_2642777 < baseStart_2642777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642824 : List Nat := [2, 1, 3, 3, 2, 1, 1, 2, 2, 5]
def baseStart_2642824 : Nat := 118140960795 + 2642824 * 2 ^ 59
def prefixEnd_2642824 : Nat := 4983230072969 + 3 ^ 40 * 2642824 * 2
def baseEnd_2642824 : Nat := 904692664825382115097253

theorem tailTrace_2642824 : CollatzResearch.WordTrace tailWord_2642824 prefixEnd_2642824 904692664825382115097253 := by
  unfold tailWord_2642824
  simp only [CollatzResearch.WordTrace]
  refine ⟨48195855088753740624915763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64261140118338320833221017 48195855088753740624915763)
  ·
    refine ⟨72293782633130610937373645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48195855088753740624915763 72293782633130610937373645)
    ·
      refine ⟨27110168487423979101515117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72293782633130610937373645 27110168487423979101515117)
      ·
        refine ⟨10166313182783992163068169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27110168487423979101515117 10166313182783992163068169)
        ·
          refine ⟨7624734887087994122301127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10166313182783992163068169 7624734887087994122301127)
          ·
            refine ⟨11437102330631991183451691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7624734887087994122301127 11437102330631991183451691)
            ·
              refine ⟨17155653495947986775177537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11437102330631991183451691 17155653495947986775177537)
              ·
                refine ⟨12866740121960990081383153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17155653495947986775177537 12866740121960990081383153)
                ·
                  refine ⟨9650055091470742561037365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12866740121960990081383153 9650055091470742561037365)
                  ·
                    refine ⟨904692664825382115097253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9650055091470742561037365 904692664825382115097253)
                    ·
                      rfl

theorem cell22_2642824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_2642824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2642824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2642824 prefixEnd_2642824 := by exact prefixLift 2642824
  have htrace : WordTrace (prefixWord ++ tailWord_2642824) baseStart_2642824 baseEnd_2642824 := by
    simpa [prefixWord, tailWord_2642824, baseEnd_2642824] using wordTrace_append hprefix tailTrace_2642824
  have hstable : (prefixWord ++ tailWord_2642824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642824).length < 2 ^ (prefixWord ++ tailWord_2642824).sum := by decide
  have hdescent : baseEnd_2642824 < baseStart_2642824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642826 : List Nat := [3, 1, 2, 4, 1, 1, 3, 2, 5]
def baseStart_2642826 : Nat := 118140960795 + 2642826 * 2 ^ 59
def prefixEnd_2642826 : Nat := 4983230072969 + 3 ^ 40 * 2642826 * 2
def baseEnd_2642826 : Nat := 301564449822084925515749

theorem tailTrace_2642826 : CollatzResearch.WordTrace tailWord_2642826 prefixEnd_2642826 301564449822084925515749 := by
  unfold tailWord_2642826
  simp only [CollatzResearch.WordTrace]
  refine ⟨24097945780875058897851083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64261188749000157060936221 24097945780875058897851083)
  ·
    refine ⟨36146918671312588346776625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24097945780875058897851083 36146918671312588346776625)
    ·
      refine ⟨27110189003484441260082469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36146918671312588346776625 27110189003484441260082469)
      ·
        refine ⟨5083160438153332736265463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27110189003484441260082469 5083160438153332736265463)
        ·
          refine ⟨7624740657229999104398195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5083160438153332736265463 7624740657229999104398195)
          ·
            refine ⟨11437110985844998656597293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7624740657229999104398195 11437110985844998656597293)
            ·
              refine ⟨4288916619691874496223985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11437110985844998656597293 4288916619691874496223985)
              ·
                refine ⟨3216687464768905872167989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4288916619691874496223985 3216687464768905872167989)
                ·
                  refine ⟨301564449822084925515749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3216687464768905872167989 301564449822084925515749)
                  ·
                    rfl

theorem cell22_2642826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 5].length) (baseStart_2642826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2642826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2642826 prefixEnd_2642826 := by exact prefixLift 2642826
  have htrace : WordTrace (prefixWord ++ tailWord_2642826) baseStart_2642826 baseEnd_2642826 := by
    simpa [prefixWord, tailWord_2642826, baseEnd_2642826] using wordTrace_append hprefix tailTrace_2642826
  have hstable : (prefixWord ++ tailWord_2642826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642826).length < 2 ^ (prefixWord ++ tailWord_2642826).sum := by decide
  have hdescent : baseEnd_2642826 < baseStart_2642826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642869 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 3, 5]
def baseStart_2642869 : Nat := 118140960795 + 2642869 * 2 ^ 59
def prefixEnd_2642869 : Nat := 4983230072969 + 3 ^ 40 * 2642869 * 2
def baseEnd_2642869 : Nat := 904708069245016997722115

theorem tailTrace_2642869 : CollatzResearch.WordTrace tailWord_2642869 prefixEnd_2642869 904708069245016997722115 := by
  unfold tailWord_2642869
  simp only [CollatzResearch.WordTrace]
  refine ⟨96393351462344453935219661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64262234308229635956813107 96393351462344453935219661)
  ·
    refine ⟨36147506798379170225707373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96393351462344453935219661 36147506798379170225707373)
    ·
      refine ⟨13555315049392188834640265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36147506798379170225707373 13555315049392188834640265)
      ·
        refine ⟨10166486287044141625980199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13555315049392188834640265 10166486287044141625980199)
        ·
          refine ⟨15249729430566212438970299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10166486287044141625980199 15249729430566212438970299)
          ·
            refine ⟨22874594145849318658455449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15249729430566212438970299 22874594145849318658455449)
            ·
              refine ⟨17155945609386988993841587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22874594145849318658455449 17155945609386988993841587)
              ·
                refine ⟨25733918414080483490762381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17155945609386988993841587 25733918414080483490762381)
                ·
                  refine ⟨9650219405280181309035893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25733918414080483490762381 9650219405280181309035893)
                  ·
                    refine ⟨904708069245016997722115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9650219405280181309035893 904708069245016997722115)
                    ·
                      rfl

theorem cell22_2642869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_2642869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2642869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2642869 prefixEnd_2642869 := by exact prefixLift 2642869
  have htrace : WordTrace (prefixWord ++ tailWord_2642869) baseStart_2642869 baseEnd_2642869 := by
    simpa [prefixWord, tailWord_2642869, baseEnd_2642869] using wordTrace_append hprefix tailTrace_2642869
  have hstable : (prefixWord ++ tailWord_2642869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642869).length < 2 ^ (prefixWord ++ tailWord_2642869).sum := by decide
  have hdescent : baseEnd_2642869 < baseStart_2642869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642871 : List Nat := [1, 1, 3, 1, 3, 1, 5, 3, 4]
def baseStart_2642871 : Nat := 118140960795 + 2642871 * 2 ^ 59
def prefixEnd_2642871 : Nat := 4983230072969 + 3 ^ 40 * 2642871 * 2
def baseEnd_2642871 : Nat := 301569584628629886390703

theorem tailTrace_2642871 : CollatzResearch.WordTrace tailWord_2642871 prefixEnd_2642871 301569584628629886390703 := by
  unfold tailWord_2642871
  simp only [CollatzResearch.WordTrace]
  refine ⟨96393424408337208276792467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64262282938891472184528311 96393424408337208276792467)
  ·
    refine ⟨144590136612505812415188701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96393424408337208276792467 144590136612505812415188701)
    ·
      refine ⟨54221301229689679655695763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144590136612505812415188701 54221301229689679655695763)
      ·
        refine ⟨81331951844534519483543645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54221301229689679655695763 81331951844534519483543645)
        ·
          refine ⟨30499481941700444806328867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81331951844534519483543645 30499481941700444806328867)
          ·
            refine ⟨45749222912550667209493301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30499481941700444806328867 45749222912550667209493301)
            ·
              refine ⟨4288989648051625050889997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45749222912550667209493301 4288989648051625050889997)
              ·
                refine ⟨1608371118019359394083749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4288989648051625050889997 1608371118019359394083749)
                ·
                  refine ⟨301569584628629886390703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1608371118019359394083749 301569584628629886390703)
                  ·
                    rfl

theorem cell22_2642871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3, 4].length) (baseStart_2642871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2642871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2642871 prefixEnd_2642871 := by exact prefixLift 2642871
  have htrace : WordTrace (prefixWord ++ tailWord_2642871) baseStart_2642871 baseEnd_2642871 := by
    simpa [prefixWord, tailWord_2642871, baseEnd_2642871] using wordTrace_append hprefix tailTrace_2642871
  have hstable : (prefixWord ++ tailWord_2642871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642871).length < 2 ^ (prefixWord ++ tailWord_2642871).sum := by decide
  have hdescent : baseEnd_2642871 < baseStart_2642871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642888 : List Nat := [2, 1, 3, 1, 6, 1, 1, 1, 6]
def baseStart_2642888 : Nat := 118140960795 + 2642888 * 2 ^ 59
def prefixEnd_2642888 : Nat := 4983230072969 + 3 ^ 40 * 2642888 * 2
def baseEnd_2642888 : Nat := 301571524444435760499019

theorem tailTrace_2642888 : CollatzResearch.WordTrace tailWord_2642888 prefixEnd_2642888 301571524444435760499019 := by
  unfold tailWord_2642888
  simp only [CollatzResearch.WordTrace]
  refine ⟨48197022224637810090080659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64262696299517080120107545 48197022224637810090080659)
  ·
    refine ⟨72295533336956715135120989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48197022224637810090080659 72295533336956715135120989)
    ·
      refine ⟨27110825001358768175670371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72295533336956715135120989 27110825001358768175670371)
      ·
        refine ⟨40666237502038152263505557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27110825001358768175670371 40666237502038152263505557)
        ·
          refine ⟨1906229882908038387351823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40666237502038152263505557 1906229882908038387351823)
          ·
            refine ⟨2859344824362057581027735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1906229882908038387351823 2859344824362057581027735)
            ·
              refine ⟨4289017236543086371541603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2859344824362057581027735 4289017236543086371541603)
              ·
                refine ⟨6433525854814629557312405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4289017236543086371541603 6433525854814629557312405)
                ·
                  refine ⟨301571524444435760499019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6433525854814629557312405 301571524444435760499019)
                  ·
                    rfl

theorem cell22_2642888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 6].length) (baseStart_2642888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2642888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2642888 prefixEnd_2642888 := by exact prefixLift 2642888
  have htrace : WordTrace (prefixWord ++ tailWord_2642888) baseStart_2642888 baseEnd_2642888 := by
    simpa [prefixWord, tailWord_2642888, baseEnd_2642888] using wordTrace_append hprefix tailTrace_2642888
  have hstable : (prefixWord ++ tailWord_2642888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642888).length < 2 ^ (prefixWord ++ tailWord_2642888).sum := by decide
  have hdescent : baseEnd_2642888 < baseStart_2642888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642933 : List Nat := [1, 3, 5, 2, 2, 9]
def baseStart_2642933 : Nat := 118140960795 + 2642933 * 2 ^ 59
def prefixEnd_2642933 : Nat := 4983230072969 + 3 ^ 40 * 2642933 * 2
def baseEnd_2642933 : Nat := 11169505898184471161999

theorem tailTrace_2642933 : CollatzResearch.WordTrace tailWord_2642933 prefixEnd_2642933 11169505898184471161999 := by
  unfold tailWord_2642933
  simp only [CollatzResearch.WordTrace]
  refine ⟨96395685734112592865549453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64263790489408395243699635 96395685734112592865549453)
  ·
    refine ⟨36148382150292222324581045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96395685734112592865549453 36148382150292222324581045)
    ·
      refine ⟨3388910826589895842929473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36148382150292222324581045 3388910826589895842929473)
      ·
        refine ⟨2541683119942421882197105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3388910826589895842929473 2541683119942421882197105)
        ·
          refine ⟨1906262339956816411647829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2541683119942421882197105 1906262339956816411647829)
          ·
            refine ⟨11169505898184471161999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1906262339956816411647829 11169505898184471161999)
            ·
              rfl

theorem cell22_2642933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 9].length) (baseStart_2642933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2642933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2642933 prefixEnd_2642933 := by exact prefixLift 2642933
  have htrace : WordTrace (prefixWord ++ tailWord_2642933) baseStart_2642933 baseEnd_2642933 := by
    simpa [prefixWord, tailWord_2642933, baseEnd_2642933] using wordTrace_append hprefix tailTrace_2642933
  have hstable : (prefixWord ++ tailWord_2642933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642933).length < 2 ^ (prefixWord ++ tailWord_2642933).sum := by decide
  have hdescent : baseEnd_2642933 < baseStart_2642933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643036 : List Nat := [2, 2, 4, 1, 1, 1, 1, 3, 1, 6]
def baseStart_2643036 : Nat := 118140960795 + 2643036 * 2 ^ 59
def prefixEnd_2643036 : Nat := 4983230072969 + 3 ^ 40 * 2643036 * 2
def baseEnd_2643036 : Nat := 904765236757884228796603

theorem tailTrace_2643036 : CollatzResearch.WordTrace tailWord_2643036 prefixEnd_2643036 904765236757884228796603 := by
  unfold tailWord_2643036
  simp only [CollatzResearch.WordTrace]
  refine ⟨48199721226369720728274481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64266294968492960971032641 48199721226369720728274481)
  ·
    refine ⟨36149790919777290546205861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48199721226369720728274481 36149790919777290546205861)
    ·
      refine ⟨6778085797458241977413599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36149790919777290546205861 6778085797458241977413599)
      ·
        refine ⟨10167128696187362966120399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6778085797458241977413599 10167128696187362966120399)
        ·
          refine ⟨15250693044281044449180599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10167128696187362966120399 15250693044281044449180599)
          ·
            refine ⟨22876039566421566673770899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15250693044281044449180599 22876039566421566673770899)
            ·
              refine ⟨34314059349632350010656349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22876039566421566673770899 34314059349632350010656349)
              ·
                refine ⟨12867772256112131253996131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34314059349632350010656349 12867772256112131253996131)
                ·
                  refine ⟨19301658384168196880994197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12867772256112131253996131 19301658384168196880994197)
                  ·
                    refine ⟨904765236757884228796603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19301658384168196880994197 904765236757884228796603)
                    ·
                      rfl

theorem cell22_2643036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_2643036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643036 prefixEnd_2643036 := by exact prefixLift 2643036
  have htrace : WordTrace (prefixWord ++ tailWord_2643036) baseStart_2643036 baseEnd_2643036 := by
    simpa [prefixWord, tailWord_2643036, baseEnd_2643036] using wordTrace_append hprefix tailTrace_2643036
  have hstable : (prefixWord ++ tailWord_2643036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643036).length < 2 ^ (prefixWord ++ tailWord_2643036).sum := by decide
  have hdescent : baseEnd_2643036 < baseStart_2643036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643053 : List Nat := [1, 5, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_2643053 : Nat := 118140960795 + 2643053 * 2 ^ 59
def prefixEnd_2643053 : Nat := 4983230072969 + 3 ^ 40 * 2643053 * 2
def baseEnd_2643053 : Nat := 904771056205301851121551

theorem tailTrace_2643053 : CollatzResearch.WordTrace tailWord_2643053 prefixEnd_2643053 904771056205301851121551 := by
  unfold tailWord_2643053
  simp only [CollatzResearch.WordTrace]
  refine ⟨96400062493677853359917813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64266708329118568906611875 96400062493677853359917813)
  ·
    refine ⟨9037505858782298752492295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96400062493677853359917813 9037505858782298752492295)
    ·
      refine ⟨13556258788173448128738443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9037505858782298752492295 13556258788173448128738443)
      ·
        refine ⟨20334388182260172193107665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13556258788173448128738443 20334388182260172193107665)
        ·
          refine ⟨15250791136695129144830749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20334388182260172193107665 15250791136695129144830749)
          ·
            refine ⟨5719046676260673429311531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15250791136695129144830749 5719046676260673429311531)
            ·
              refine ⟨8578570014391010143967297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5719046676260673429311531 8578570014391010143967297)
              ·
                refine ⟨6433927510793257607975473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8578570014391010143967297 6433927510793257607975473)
                ·
                  refine ⟨4825445633094943205981605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6433927510793257607975473 4825445633094943205981605)
                  ·
                    refine ⟨904771056205301851121551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4825445633094943205981605 904771056205301851121551)
                    ·
                      rfl

theorem cell22_2643053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_2643053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643053 prefixEnd_2643053 := by exact prefixLift 2643053
  have htrace : WordTrace (prefixWord ++ tailWord_2643053) baseStart_2643053 baseEnd_2643053 := by
    simpa [prefixWord, tailWord_2643053, baseEnd_2643053] using wordTrace_append hprefix tailTrace_2643053
  have hstable : (prefixWord ++ tailWord_2643053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643053).length < 2 ^ (prefixWord ++ tailWord_2643053).sum := by decide
  have hdescent : baseEnd_2643053 < baseStart_2643053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643160 : List Nat := [2, 1, 2, 2, 5, 1, 1, 3, 1, 4]
def baseStart_2643160 : Nat := 118140960795 + 2643160 * 2 ^ 59
def prefixEnd_2643160 : Nat := 4983230072969 + 3 ^ 40 * 2643160 * 2
def baseEnd_2643160 : Nat := 904807684491989238696223

theorem tailTrace_2643160 : CollatzResearch.WordTrace tailWord_2643160 prefixEnd_2643160 904807684491989238696223 := by
  unfold tailWord_2643160
  simp only [CollatzResearch.WordTrace]
  refine ⟨48201982552145105317031467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64269310069526807089375289 48201982552145105317031467)
  ·
    refine ⟨72302973828217657975547201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48201982552145105317031467 72302973828217657975547201)
    ·
      refine ⟨54227230371163243481660401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72302973828217657975547201 54227230371163243481660401)
      ·
        refine ⟨40670422778372432611245301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54227230371163243481660401 40670422778372432611245301)
        ·
          refine ⟨3812852135472415557304247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40670422778372432611245301 3812852135472415557304247)
          ·
            refine ⟨5719278203208623335956371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3812852135472415557304247 5719278203208623335956371)
            ·
              refine ⟨8578917304812935003934557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5719278203208623335956371 8578917304812935003934557)
              ·
                refine ⟨3217093989304850626475459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8578917304812935003934557 3217093989304850626475459)
                ·
                  refine ⟨4825640983957275939713189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3217093989304850626475459 4825640983957275939713189)
                  ·
                    refine ⟨904807684491989238696223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4825640983957275939713189 904807684491989238696223)
                    ·
                      rfl

theorem cell22_2643160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_2643160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643160 prefixEnd_2643160 := by exact prefixLift 2643160
  have htrace : WordTrace (prefixWord ++ tailWord_2643160) baseStart_2643160 baseEnd_2643160 := by
    simpa [prefixWord, tailWord_2643160, baseEnd_2643160] using wordTrace_append hprefix tailTrace_2643160
  have hstable : (prefixWord ++ tailWord_2643160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643160).length < 2 ^ (prefixWord ++ tailWord_2643160).sum := by decide
  have hdescent : baseEnd_2643160 < baseStart_2643160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643175 : List Nat := [1, 1, 5, 3, 2, 1, 2, 1, 6]
def baseStart_2643175 : Nat := 118140960795 + 2643175 * 2 ^ 59
def prefixEnd_2643175 : Nat := 4983230072969 + 3 ^ 40 * 2643175 * 2
def baseEnd_2643175 : Nat := 301604273099511399857059

theorem tailTrace_2643175 : CollatzResearch.WordTrace tailWord_2643175 prefixEnd_2643175 301604273099511399857059 := by
  unfold tailWord_2643175
  simp only [CollatzResearch.WordTrace]
  refine ⟨96404512199235868195858979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64269674799490578797239319 96404512199235868195858979)
  ·
    refine ⟨144606768298853802293788469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96404512199235868195858979 144606768298853802293788469)
    ·
      refine ⟨13556884528017543965042669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144606768298853802293788469 13556884528017543965042669)
      ·
        refine ⟨5083831698006578986891001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13556884528017543965042669 5083831698006578986891001)
        ·
          refine ⟨3812873773504934240168251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5083831698006578986891001 3812873773504934240168251)
          ·
            refine ⟨5719310660257401360252377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3812873773504934240168251 5719310660257401360252377)
            ·
              refine ⟨4289482995193051020189283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5719310660257401360252377 4289482995193051020189283)
              ·
                refine ⟨6434224492789576530283925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4289482995193051020189283 6434224492789576530283925)
                ·
                  refine ⟨301604273099511399857059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6434224492789576530283925 301604273099511399857059)
                  ·
                    rfl

theorem cell22_2643175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 6].length) (baseStart_2643175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643175 prefixEnd_2643175 := by exact prefixLift 2643175
  have htrace : WordTrace (prefixWord ++ tailWord_2643175) baseStart_2643175 baseEnd_2643175 := by
    simpa [prefixWord, tailWord_2643175, baseEnd_2643175] using wordTrace_append hprefix tailTrace_2643175
  have hstable : (prefixWord ++ tailWord_2643175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643175).length < 2 ^ (prefixWord ++ tailWord_2643175).sum := by decide
  have hdescent : baseEnd_2643175 < baseStart_2643175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643203 : List Nat := [1, 1, 1, 3, 2, 4, 4, 6]
def baseStart_2643203 : Nat := 118140960795 + 2643203 * 2 ^ 59
def prefixEnd_2643203 : Nat := 4983230072969 + 3 ^ 40 * 2643203 * 2
def baseEnd_2643203 : Nat := 100535822696750162207899

theorem tailTrace_2643203 : CollatzResearch.WordTrace tailWord_2643203 prefixEnd_2643203 100535822696750162207899 := by
  unfold tailWord_2643203
  simp only [CollatzResearch.WordTrace]
  refine ⟨96405533443134428977878263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64270355628756285985252175 96405533443134428977878263)
  ·
    refine ⟨144608300164701643466817395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96405533443134428977878263 144608300164701643466817395)
    ·
      refine ⟨216912450247052465200226093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144608300164701643466817395 216912450247052465200226093)
      ·
        refine ⟨81342168842644674450084785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216912450247052465200226093 81342168842644674450084785)
        ·
          refine ⟨61006626631983505837563589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81342168842644674450084785 61006626631983505837563589)
          ·
            refine ⟨11438742493496907344543173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61006626631983505837563589 11438742493496907344543173)
            ·
              refine ⟨2144764217530670127101845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11438742493496907344543173 2144764217530670127101845)
              ·
                refine ⟨100535822696750162207899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2144764217530670127101845 100535822696750162207899)
                ·
                  rfl

theorem cell22_2643203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 6].length) (baseStart_2643203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643203 prefixEnd_2643203 := by exact prefixLift 2643203
  have htrace : WordTrace (prefixWord ++ tailWord_2643203) baseStart_2643203 baseEnd_2643203 := by
    simpa [prefixWord, tailWord_2643203, baseEnd_2643203] using wordTrace_append hprefix tailTrace_2643203
  have hstable : (prefixWord ++ tailWord_2643203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643203).length < 2 ^ (prefixWord ++ tailWord_2643203).sum := by decide
  have hdescent : baseEnd_2643203 < baseStart_2643203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643235 : List Nat := [1, 1, 1, 4, 2, 3, 3, 1, 3, 3]
def baseStart_2643235 : Nat := 118140960795 + 2643235 * 2 ^ 59
def prefixEnd_2643235 : Nat := 4983230072969 + 3 ^ 40 * 2643235 * 2
def baseEnd_2643235 : Nat := 904833358524714043070993

theorem tailTrace_2643235 : CollatzResearch.WordTrace tailWord_2643235 prefixEnd_2643235 904833358524714043070993 := by
  unfold tailWord_2643235
  simp only [CollatzResearch.WordTrace]
  refine ⟨96406700579018498443043159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64271133719345665628695439 96406700579018498443043159)
  ·
    refine ⟨144610050868527747664564739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96406700579018498443043159 144610050868527747664564739)
    ·
      refine ⟨216915076302791621496847109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144610050868527747664564739 216915076302791621496847109)
      ·
        refine ⟨40671576806773429030658833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216915076302791621496847109 40671576806773429030658833)
        ·
          refine ⟨30503682605080071772994125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40671576806773429030658833 30503682605080071772994125)
          ·
            refine ⟨11438880976905026914872797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30503682605080071772994125 11438880976905026914872797)
            ·
              refine ⟨4289580366339385093077299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11438880976905026914872797 4289580366339385093077299)
              ·
                refine ⟨6434370549509077639615949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4289580366339385093077299 6434370549509077639615949)
                ·
                  refine ⟨2412888956065904114855981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6434370549509077639615949 2412888956065904114855981)
                  ·
                    refine ⟨904833358524714043070993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2412888956065904114855981 904833358524714043070993)
                    ·
                      rfl

theorem cell22_2643235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3, 3].length) (baseStart_2643235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643235 prefixEnd_2643235 := by exact prefixLift 2643235
  have htrace : WordTrace (prefixWord ++ tailWord_2643235) baseStart_2643235 baseEnd_2643235 := by
    simpa [prefixWord, tailWord_2643235, baseEnd_2643235] using wordTrace_append hprefix tailTrace_2643235
  have hstable : (prefixWord ++ tailWord_2643235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643235).length < 2 ^ (prefixWord ++ tailWord_2643235).sum := by decide
  have hdescent : baseEnd_2643235 < baseStart_2643235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643248 : List Nat := [2, 1, 1, 1, 2, 2, 5, 3, 5]
def baseStart_2643248 : Nat := 118140960795 + 2643248 * 2 ^ 59
def prefixEnd_2643248 : Nat := 4983230072969 + 3 ^ 40 * 2643248 * 2
def baseEnd_2643248 : Nat := 301612602896795447498651

theorem tailTrace_2643248 : CollatzResearch.WordTrace tailWord_2643248 prefixEnd_2643248 301612602896795447498651 := by
  unfold tailWord_2643248
  simp only [CollatzResearch.WordTrace]
  refine ⟨48203587363985700831633199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64271449818647601108844265 48203587363985700831633199)
  ·
    refine ⟨72305381045978551247449799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48203587363985700831633199 72305381045978551247449799)
    ·
      refine ⟨108458071568967826871174699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72305381045978551247449799 108458071568967826871174699)
      ·
        refine ⟨162687107353451740306762049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108458071568967826871174699 162687107353451740306762049)
        ·
          refine ⟨122015330515088805230071537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162687107353451740306762049 122015330515088805230071537)
          ·
            refine ⟨91511497886316603922553653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122015330515088805230071537 91511497886316603922553653)
            ·
              refine ⟨8579202926842181617739405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91511497886316603922553653 8579202926842181617739405)
              ·
                refine ⟨3217201097565818106652277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8579202926842181617739405 3217201097565818106652277)
                ·
                  refine ⟨301612602896795447498651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3217201097565818106652277 301612602896795447498651)
                  ·
                    rfl

theorem cell22_2643248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 5].length) (baseStart_2643248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643248 prefixEnd_2643248 := by exact prefixLift 2643248
  have htrace : WordTrace (prefixWord ++ tailWord_2643248) baseStart_2643248 baseEnd_2643248 := by
    simpa [prefixWord, tailWord_2643248, baseEnd_2643248] using wordTrace_append hprefix tailTrace_2643248
  have hstable : (prefixWord ++ tailWord_2643248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643248).length < 2 ^ (prefixWord ++ tailWord_2643248).sum := by decide
  have hdescent : baseEnd_2643248 < baseStart_2643248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643323 : List Nat := [1, 1, 1, 1, 1, 6, 3, 1, 1, 6]
def baseStart_2643323 : Nat := 118140960795 + 2643323 * 2 ^ 59
def prefixEnd_2643323 : Nat := 4983230072969 + 3 ^ 40 * 2643323 * 2
def baseEnd_2643323 : Nat := 904863482723111146870723

theorem tailTrace_2643323 : CollatzResearch.WordTrace tailWord_2643323 prefixEnd_2643323 904863482723111146870723 := by
  unfold tailWord_2643323
  simp only [CollatzResearch.WordTrace]
  refine ⟨96409910202699689472246623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64273273468466459648164415 96409910202699689472246623)
  ·
    refine ⟨144614865304049534208369935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96409910202699689472246623 144614865304049534208369935)
    ·
      refine ⟨216922297956074301312554903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144614865304049534208369935 216922297956074301312554903)
      ·
        refine ⟨325383446934111451968832355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216922297956074301312554903 325383446934111451968832355)
        ·
          refine ⟨488075170401167177953248533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325383446934111451968832355 488075170401167177953248533)
          ·
            refine ⟨22878523612554711466558525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 488075170401167177953248533 22878523612554711466558525)
            ·
              refine ⟨8579446354708016799959447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22878523612554711466558525 8579446354708016799959447)
              ·
                refine ⟨12869169532062025199939171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8579446354708016799959447 12869169532062025199939171)
                ·
                  refine ⟨19303754298093037799908757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12869169532062025199939171 19303754298093037799908757)
                  ·
                    refine ⟨904863482723111146870723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19303754298093037799908757 904863482723111146870723)
                    ·
                      rfl

theorem cell22_2643323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 6].length) (baseStart_2643323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643323 prefixEnd_2643323 := by exact prefixLift 2643323
  have htrace : WordTrace (prefixWord ++ tailWord_2643323) baseStart_2643323 baseEnd_2643323 := by
    simpa [prefixWord, tailWord_2643323, baseEnd_2643323] using wordTrace_append hprefix tailTrace_2643323
  have hstable : (prefixWord ++ tailWord_2643323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643323).length < 2 ^ (prefixWord ++ tailWord_2643323).sum := by decide
  have hdescent : baseEnd_2643323 < baseStart_2643323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643325 : List Nat := [1, 4, 1, 1, 2, 2, 2, 2, 4, 3]
def baseStart_2643325 : Nat := 118140960795 + 2643325 * 2 ^ 59
def prefixEnd_2643325 : Nat := 4983230072969 + 3 ^ 40 * 2643325 * 2
def baseEnd_2643325 : Nat := 904864167363983808320717

theorem tailTrace_2643325 : CollatzResearch.WordTrace tailWord_2643325 prefixEnd_2643325 904864167363983808320717 := by
  unfold tailWord_2643325
  simp only [CollatzResearch.WordTrace]
  refine ⟨96409983148692443813819429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64273322099128295875879619 96409983148692443813819429)
  ·
    refine ⟨18076871840379833215091143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96409983148692443813819429 18076871840379833215091143)
    ·
      refine ⟨27115307760569749822636715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18076871840379833215091143 27115307760569749822636715)
      ·
        refine ⟨40672961640854624733955073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27115307760569749822636715 40672961640854624733955073)
        ·
          refine ⟨30504721230640968550466305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40672961640854624733955073 30504721230640968550466305)
          ·
            refine ⟨22878540922980726412849729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30504721230640968550466305 22878540922980726412849729)
            ·
              refine ⟨17158905692235544809637297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22878540922980726412849729 17158905692235544809637297)
              ·
                refine ⟨12869179269176658607227973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17158905692235544809637297 12869179269176658607227973)
                ·
                  refine ⟨2412971112970623488855245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12869179269176658607227973 2412971112970623488855245)
                  ·
                    refine ⟨904864167363983808320717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2412971112970623488855245 904864167363983808320717)
                    ·
                      rfl

theorem cell22_2643325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_2643325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643325 prefixEnd_2643325 := by exact prefixLift 2643325
  have htrace : WordTrace (prefixWord ++ tailWord_2643325) baseStart_2643325 baseEnd_2643325 := by
    simpa [prefixWord, tailWord_2643325, baseEnd_2643325] using wordTrace_append hprefix tailTrace_2643325
  have hstable : (prefixWord ++ tailWord_2643325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643325).length < 2 ^ (prefixWord ++ tailWord_2643325).sum := by decide
  have hdescent : baseEnd_2643325 < baseStart_2643325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643359 : List Nat := [1, 1, 2, 5, 1, 3, 3, 1, 2, 3]
def baseStart_2643359 : Nat := 118140960795 + 2643359 * 2 ^ 59
def prefixEnd_2643359 : Nat := 4983230072969 + 3 ^ 40 * 2643359 * 2
def baseEnd_2643359 : Nat := 904875806258819052970613

theorem tailTrace_2643359 : CollatzResearch.WordTrace tailWord_2643359 prefixEnd_2643359 904875806258819052970613 := by
  unfold tailWord_2643359
  simp only [CollatzResearch.WordTrace]
  refine ⟨96411223230569267620557131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64274148820379511747038087 96411223230569267620557131)
  ·
    refine ⟨144616834845853901430835697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96411223230569267620557131 144616834845853901430835697)
    ·
      refine ⟨108462626134390426073126773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144616834845853901430835697 108462626134390426073126773)
      ·
        refine ⟨10168371200099102444355635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108462626134390426073126773 10168371200099102444355635)
        ·
          refine ⟨15252556800148653666533453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10168371200099102444355635 15252556800148653666533453)
          ·
            refine ⟨5719708800055745124950045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15252556800148653666533453 5719708800055745124950045)
            ·
              refine ⟨2144890800020904421856267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5719708800055745124950045 2144890800020904421856267)
              ·
                refine ⟨3217336200031356632784401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2144890800020904421856267 3217336200031356632784401)
                ·
                  refine ⟨2413002150023517474588301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3217336200031356632784401 2413002150023517474588301)
                  ·
                    refine ⟨904875806258819052970613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2413002150023517474588301 904875806258819052970613)
                    ·
                      rfl

theorem cell22_2643359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 2, 3].length) (baseStart_2643359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643359 prefixEnd_2643359 := by exact prefixLift 2643359
  have htrace : WordTrace (prefixWord ++ tailWord_2643359) baseStart_2643359 baseEnd_2643359 := by
    simpa [prefixWord, tailWord_2643359, baseEnd_2643359] using wordTrace_append hprefix tailTrace_2643359
  have hstable : (prefixWord ++ tailWord_2643359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643359).length < 2 ^ (prefixWord ++ tailWord_2643359).sum := by decide
  have hdescent : baseEnd_2643359 < baseStart_2643359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643383 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 9]
def baseStart_2643383 : Nat := 118140960795 + 2643383 * 2 ^ 59
def prefixEnd_2643383 : Nat := 4983230072969 + 3 ^ 40 * 2643383 * 2
def baseEnd_2643383 : Nat := 301628007316430330123513

theorem tailTrace_2643383 : CollatzResearch.WordTrace tailWord_2643383 prefixEnd_2643383 301628007316430330123513 := by
  unfold tailWord_2643383
  simp only [CollatzResearch.WordTrace]
  refine ⟨96412098582482319719430803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64274732388321546479620535 96412098582482319719430803)
  ·
    refine ⟨144618147873723479579146205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96412098582482319719430803 144618147873723479579146205)
    ·
      refine ⟨54231805452646304842179827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144618147873723479579146205 54231805452646304842179827)
      ·
        refine ⟨81347708178969457263269741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54231805452646304842179827 81347708178969457263269741)
        ·
          refine ⟨30505390567113546473726153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81347708178969457263269741 30505390567113546473726153)
          ·
            refine ⟨22879042925335159855294615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30505390567113546473726153 22879042925335159855294615)
            ·
              refine ⟨34318564388002739782941923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22879042925335159855294615 34318564388002739782941923)
              ·
                refine ⟨51477846582004109674412885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34318564388002739782941923 51477846582004109674412885)
                ·
                  refine ⟨301628007316430330123513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51477846582004109674412885 301628007316430330123513)
                  ·
                    rfl

theorem cell22_2643383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 9].length) (baseStart_2643383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643383 prefixEnd_2643383 := by exact prefixLift 2643383
  have htrace : WordTrace (prefixWord ++ tailWord_2643383) baseStart_2643383 baseEnd_2643383 := by
    simpa [prefixWord, tailWord_2643383, baseEnd_2643383] using wordTrace_append hprefix tailTrace_2643383
  have hstable : (prefixWord ++ tailWord_2643383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643383).length < 2 ^ (prefixWord ++ tailWord_2643383).sum := by decide
  have hdescent : baseEnd_2643383 < baseStart_2643383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643400 : List Nat := [2, 1, 3, 1, 3, 1, 2, 4, 5]
def baseStart_2643400 : Nat := 118140960795 + 2643400 * 2 ^ 59
def prefixEnd_2643400 : Nat := 4983230072969 + 3 ^ 40 * 2643400 * 2
def baseEnd_2643400 : Nat := 301629947132236204231829

theorem tailTrace_2643400 : CollatzResearch.WordTrace tailWord_2643400 prefixEnd_2643400 301629947132236204231829 := by
  unfold tailWord_2643400
  simp only [CollatzResearch.WordTrace]
  refine ⟨48206359311710365811399827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64275145748947154415199769 48206359311710365811399827)
  ·
    refine ⟨72309538967565548717099741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48206359311710365811399827 72309538967565548717099741)
    ·
      refine ⟨27116077112837080768912403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72309538967565548717099741 27116077112837080768912403)
      ·
        refine ⟨40674115669255621153368605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27116077112837080768912403 40674115669255621153368605)
        ·
          refine ⟨15252793375970857932513227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40674115669255621153368605 15252793375970857932513227)
          ·
            refine ⟨22879190063956286898769841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15252793375970857932513227 22879190063956286898769841)
            ·
              refine ⟨17159392547967215174077381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22879190063956286898769841 17159392547967215174077381)
              ·
                refine ⟨3217386102743852845139509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17159392547967215174077381 3217386102743852845139509)
                ·
                  refine ⟨301629947132236204231829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3217386102743852845139509 301629947132236204231829)
                  ·
                    rfl

theorem cell22_2643400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 5].length) (baseStart_2643400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643400 prefixEnd_2643400 := by exact prefixLift 2643400
  have htrace : WordTrace (prefixWord ++ tailWord_2643400) baseStart_2643400 baseEnd_2643400 := by
    simpa [prefixWord, tailWord_2643400, baseEnd_2643400] using wordTrace_append hprefix tailTrace_2643400
  have hstable : (prefixWord ++ tailWord_2643400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643400).length < 2 ^ (prefixWord ++ tailWord_2643400).sum := by decide
  have hdescent : baseEnd_2643400 < baseStart_2643400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643404 : List Nat := [2, 2, 1, 4, 2, 3, 1, 1, 3, 3]
def baseStart_2643404 : Nat := 118140960795 + 2643404 * 2 ^ 59
def prefixEnd_2643404 : Nat := 4983230072969 + 3 ^ 40 * 2643404 * 2
def baseEnd_2643404 : Nat := 904891210678453935595475

theorem tailTrace_2643404 : CollatzResearch.WordTrace tailWord_2643404 prefixEnd_2643404 904891210678453935595475 := by
  unfold tailWord_2643404
  simp only [CollatzResearch.WordTrace]
  refine ⟨48206432257703120152972633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64275243010270826870630177 48206432257703120152972633)
  ·
    refine ⟨36154824193277340114729475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48206432257703120152972633 36154824193277340114729475)
    ·
      refine ⟨54232236289916010172094213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36154824193277340114729475 54232236289916010172094213)
      ·
        refine ⟨10168544304359251907267665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54232236289916010172094213 10168544304359251907267665)
        ·
          refine ⟨7626408228269438930450749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10168544304359251907267665 7626408228269438930450749)
          ·
            refine ⟨2859903085601039598919031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7626408228269438930450749 2859903085601039598919031)
            ·
              refine ⟨4289854628401559398378547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2859903085601039598919031 4289854628401559398378547)
              ·
                refine ⟨6434781942602339097567821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4289854628401559398378547 6434781942602339097567821)
                ·
                  refine ⟨2413043228475877161587933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6434781942602339097567821 2413043228475877161587933)
                  ·
                    refine ⟨904891210678453935595475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2413043228475877161587933 904891210678453935595475)
                    ·
                      rfl

theorem cell22_2643404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 3, 3].length) (baseStart_2643404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643404 prefixEnd_2643404 := by exact prefixLift 2643404
  have htrace : WordTrace (prefixWord ++ tailWord_2643404) baseStart_2643404 baseEnd_2643404 := by
    simpa [prefixWord, tailWord_2643404, baseEnd_2643404] using wordTrace_append hprefix tailTrace_2643404
  have hstable : (prefixWord ++ tailWord_2643404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643404).length < 2 ^ (prefixWord ++ tailWord_2643404).sum := by decide
  have hdescent : baseEnd_2643404 < baseStart_2643404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643417 : List Nat := [1, 2, 1, 2, 4, 2, 4, 1, 5]
def baseStart_2643417 : Nat := 118140960795 + 2643417 * 2 ^ 59
def prefixEnd_2643417 : Nat := 4983230072969 + 3 ^ 40 * 2643417 * 2
def baseEnd_2643417 : Nat := 301631886948042078340145

theorem tailTrace_2643417 : CollatzResearch.WordTrace tailWord_2643417 prefixEnd_2643417 301631886948042078340145 := by
  unfold tailWord_2643417
  simp only [CollatzResearch.WordTrace]
  refine ⟨96413338664359143526168505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64275559109572762350779003 96413338664359143526168505)
  ·
    refine ⟨72310003998269357644626379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96413338664359143526168505 72310003998269357644626379)
    ·
      refine ⟨108465005997404036466939569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72310003998269357644626379 108465005997404036466939569)
      ·
        refine ⟨81348754498053027350204677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108465005997404036466939569 81348754498053027350204677)
        ·
          refine ⟨15252891468384942628163377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81348754498053027350204677 15252891468384942628163377)
          ·
            refine ⟨11439668601288706971122533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15252891468384942628163377 11439668601288706971122533)
            ·
              refine ⟨2144937862741632557085475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11439668601288706971122533 2144937862741632557085475)
              ·
                refine ⟨3217406794112448835628213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2144937862741632557085475 3217406794112448835628213)
                ·
                  refine ⟨301631886948042078340145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3217406794112448835628213 301631886948042078340145)
                  ·
                    rfl

theorem cell22_2643417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 5].length) (baseStart_2643417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643417 prefixEnd_2643417 := by exact prefixLift 2643417
  have htrace : WordTrace (prefixWord ++ tailWord_2643417) baseStart_2643417 baseEnd_2643417 := by
    simpa [prefixWord, tailWord_2643417, baseEnd_2643417] using wordTrace_append hprefix tailTrace_2643417
  have hstable : (prefixWord ++ tailWord_2643417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643417).length < 2 ^ (prefixWord ++ tailWord_2643417).sum := by decide
  have hdescent : baseEnd_2643417 < baseStart_2643417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643477 : List Nat := [1, 3, 2, 1, 3, 3, 2, 1, 1, 5]
def baseStart_2643477 : Nat := 118140960795 + 2643477 * 2 ^ 59
def prefixEnd_2643477 : Nat := 4983230072969 + 3 ^ 40 * 2643477 * 2
def baseEnd_2643477 : Nat := 904916200070306078520251

theorem tailTrace_2643477 : CollatzResearch.WordTrace tailWord_2643477 prefixEnd_2643477 904916200070306078520251 := by
  unfold tailWord_2643477
  simp only [CollatzResearch.WordTrace]
  refine ⟨96415527044141773773352685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64277018029427849182235123 96415527044141773773352685)
  ·
    refine ⟨36155822641553165165007257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96415527044141773773352685 36155822641553165165007257)
    ·
      refine ⟨27116866981164873873755443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36155822641553165165007257 27116866981164873873755443)
      ·
        refine ⟨40675300471747310810633165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27116866981164873873755443 40675300471747310810633165)
        ·
          refine ⟨15253237676905241553987437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40675300471747310810633165 15253237676905241553987437)
          ·
            refine ⟨5719964128839465582745289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15253237676905241553987437 5719964128839465582745289)
            ·
              refine ⟨4289973096629599187058967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5719964128839465582745289 4289973096629599187058967)
              ·
                refine ⟨6434959644944398780588451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4289973096629599187058967 6434959644944398780588451)
                ·
                  refine ⟨9652439467416598170882677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6434959644944398780588451 9652439467416598170882677)
                  ·
                    refine ⟨904916200070306078520251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9652439467416598170882677 904916200070306078520251)
                    ·
                      rfl

theorem cell22_2643477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_2643477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643477 prefixEnd_2643477 := by exact prefixLift 2643477
  have htrace : WordTrace (prefixWord ++ tailWord_2643477) baseStart_2643477 baseEnd_2643477 := by
    simpa [prefixWord, tailWord_2643477, baseEnd_2643477] using wordTrace_append hprefix tailTrace_2643477
  have hstable : (prefixWord ++ tailWord_2643477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643477).length < 2 ^ (prefixWord ++ tailWord_2643477).sum := by decide
  have hdescent : baseEnd_2643477 < baseStart_2643477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643490 : List Nat := [3, 3, 1, 1, 1, 1, 2, 10]
def baseStart_2643490 : Nat := 118140960795 + 2643490 * 2 ^ 59
def prefixEnd_2643490 : Nat := 4983230072969 + 3 ^ 40 * 2643490 * 2
def baseEnd_2643490 : Nat := 100546738915108708660579

theorem tailTrace_2643490 : CollatzResearch.WordTrace tailWord_2643490 prefixEnd_2643490 100546738915108708660579 := by
  unfold tailWord_2643490
  simp only [CollatzResearch.WordTrace]
  refine ⟨24104000298273669248393981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64277334128729784662383949 24104000298273669248393981)
  ·
    refine ⟨9039000111852625968147743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24104000298273669248393981 9039000111852625968147743)
    ·
      refine ⟨13558500167778938952221615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9039000111852625968147743 13558500167778938952221615)
      ·
        refine ⟨20337750251668408428332423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13558500167778938952221615 20337750251668408428332423)
        ·
          refine ⟨30506625377502612642498635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20337750251668408428332423 30506625377502612642498635)
          ·
            refine ⟨45759938066253918963747953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30506625377502612642498635 45759938066253918963747953)
            ·
              refine ⟨34319953549690439222810965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45759938066253918963747953 34319953549690439222810965)
              ·
                refine ⟨100546738915108708660579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34319953549690439222810965 100546738915108708660579)
                ·
                  rfl

theorem cell22_2643490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 10].length) (baseStart_2643490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643490 prefixEnd_2643490 := by exact prefixLift 2643490
  have htrace : WordTrace (prefixWord ++ tailWord_2643490) baseStart_2643490 baseEnd_2643490 := by
    simpa [prefixWord, tailWord_2643490, baseEnd_2643490] using wordTrace_append hprefix tailTrace_2643490
  have hstable : (prefixWord ++ tailWord_2643490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643490).length < 2 ^ (prefixWord ++ tailWord_2643490).sum := by decide
  have hdescent : baseEnd_2643490 < baseStart_2643490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643496 : List Nat := [2, 1, 5, 2, 2, 1, 2, 3, 4]
def baseStart_2643496 : Nat := 118140960795 + 2643496 * 2 ^ 59
def prefixEnd_2643496 : Nat := 4983230072969 + 3 ^ 40 * 2643496 * 2
def baseEnd_2643496 : Nat := 301640901386198787431731

theorem tailTrace_2643496 : CollatzResearch.WordTrace tailWord_2643496 prefixEnd_2643496 301640901386198787431731 := by
  unfold tailWord_2643496
  simp only [CollatzResearch.WordTrace]
  refine ⟨48208110015536470009147171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64277480020715293345529561 48208110015536470009147171)
  ·
    refine ⟨72312165023304705013720757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48208110015536470009147171 72312165023304705013720757)
    ·
      refine ⟨6779265470934816095036321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72312165023304705013720757 6779265470934816095036321)
      ·
        refine ⟨5084449103201112071277241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6779265470934816095036321 5084449103201112071277241)
        ·
          refine ⟨3813336827400834053457931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5084449103201112071277241 3813336827400834053457931)
          ·
            refine ⟨5720005241101251080186897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3813336827400834053457931 5720005241101251080186897)
            ·
              refine ⟨4290003930825938310140173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5720005241101251080186897 4290003930825938310140173)
              ·
                refine ⟨1608751474059726866302565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4290003930825938310140173 1608751474059726866302565)
                ·
                  refine ⟨301640901386198787431731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1608751474059726866302565 301640901386198787431731)
                  ·
                    rfl

theorem cell22_2643496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3, 4].length) (baseStart_2643496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643496 prefixEnd_2643496 := by exact prefixLift 2643496
  have htrace : WordTrace (prefixWord ++ tailWord_2643496) baseStart_2643496 baseEnd_2643496 := by
    simpa [prefixWord, tailWord_2643496, baseEnd_2643496] using wordTrace_append hprefix tailTrace_2643496
  have hstable : (prefixWord ++ tailWord_2643496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643496).length < 2 ^ (prefixWord ++ tailWord_2643496).sum := by decide
  have hdescent : baseEnd_2643496 < baseStart_2643496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643556 : List Nat := [2, 3, 1, 1, 2, 3, 3, 3, 1, 3]
def baseStart_2643556 : Nat := 118140960795 + 2643556 * 2 ^ 59
def prefixEnd_2643556 : Nat := 4983230072969 + 3 ^ 40 * 2643556 * 2
def baseEnd_2643556 : Nat := 904943243384776205795009

theorem tailTrace_2643556 : CollatzResearch.WordTrace tailWord_2643556 prefixEnd_2643556 904943243384776205795009 := by
  unfold tailWord_2643556
  simp only [CollatzResearch.WordTrace]
  refine ⟨48209204205427785132739261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64278938940570380176985681 48209204205427785132739261)
  ·
    refine ⟨18078451577035419424777223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48209204205427785132739261 18078451577035419424777223)
    ·
      refine ⟨27117677365553129137165835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18078451577035419424777223 27117677365553129137165835)
      ·
        refine ⟨40676516048329693705748753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27117677365553129137165835 40676516048329693705748753)
        ·
          refine ⟨30507387036247270279311565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40676516048329693705748753 30507387036247270279311565)
          ·
            refine ⟨11440270138592726354741837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30507387036247270279311565 11440270138592726354741837)
            ·
              refine ⟨4290101301972272383028189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11440270138592726354741837 4290101301972272383028189)
              ·
                refine ⟨1608787988239602143635571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4290101301972272383028189 1608787988239602143635571)
                ·
                  refine ⟨2413181982359403215453357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1608787988239602143635571 2413181982359403215453357)
                  ·
                    refine ⟨904943243384776205795009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2413181982359403215453357 904943243384776205795009)
                    ·
                      rfl

theorem cell22_2643556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_2643556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643556 prefixEnd_2643556 := by exact prefixLift 2643556
  have htrace : WordTrace (prefixWord ++ tailWord_2643556) baseStart_2643556 baseEnd_2643556 := by
    simpa [prefixWord, tailWord_2643556, baseEnd_2643556] using wordTrace_append hprefix tailTrace_2643556
  have hstable : (prefixWord ++ tailWord_2643556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643556).length < 2 ^ (prefixWord ++ tailWord_2643556).sum := by decide
  have hdescent : baseEnd_2643556 < baseStart_2643556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643616 : List Nat := [2, 1, 1, 4, 3, 2, 3, 1, 1, 4]
def baseStart_2643616 : Nat := 118140960795 + 2643616 * 2 ^ 59
def prefixEnd_2643616 : Nat := 4983230072969 + 3 ^ 40 * 2643616 * 2
def baseEnd_2643616 : Nat := 904963782610956049294825

theorem tailTrace_2643616 : CollatzResearch.WordTrace tailWord_2643616 prefixEnd_2643616 904963782610956049294825 := by
  unfold tailWord_2643616
  simp only [CollatzResearch.WordTrace]
  refine ⟨48210298395319100256331351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64280397860425467008441801 48210298395319100256331351)
  ·
    refine ⟨72315447592978650384497027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48210298395319100256331351 72315447592978650384497027)
    ·
      refine ⟨108473171389467975576745541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72315447592978650384497027 108473171389467975576745541)
      ·
        refine ⟨20338719635525245420639789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108473171389467975576745541 20338719635525245420639789)
        ·
          refine ⟨7627019863321967032739921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20338719635525245420639789 7627019863321967032739921)
          ·
            refine ⟨5720264897491475274554941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7627019863321967032739921 5720264897491475274554941)
            ·
              refine ⟨2145099336559303227958103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5720264897491475274554941 2145099336559303227958103)
              ·
                refine ⟨3217649004838954841937155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2145099336559303227958103 3217649004838954841937155)
                ·
                  refine ⟨4826473507258432262905733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3217649004838954841937155 4826473507258432262905733)
                  ·
                    refine ⟨904963782610956049294825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4826473507258432262905733 904963782610956049294825)
                    ·
                      rfl

theorem cell22_2643616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 1, 4].length) (baseStart_2643616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643616 prefixEnd_2643616 := by exact prefixLift 2643616
  have htrace : WordTrace (prefixWord ++ tailWord_2643616) baseStart_2643616 baseEnd_2643616 := by
    simpa [prefixWord, tailWord_2643616, baseEnd_2643616] using wordTrace_append hprefix tailTrace_2643616
  have hstable : (prefixWord ++ tailWord_2643616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643616).length < 2 ^ (prefixWord ++ tailWord_2643616).sum := by decide
  have hdescent : baseEnd_2643616 < baseStart_2643616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643624 : List Nat := [2, 1, 7, 1, 1, 2, 2, 2, 1, 3]
def baseStart_2643624 : Nat := 118140960795 + 2643624 * 2 ^ 59
def prefixEnd_2643624 : Nat := 4983230072969 + 3 ^ 40 * 2643624 * 2
def baseEnd_2643624 : Nat := 904966521174446695094801

theorem tailTrace_2643624 : CollatzResearch.WordTrace tailWord_2643624 prefixEnd_2643624 904966521174446695094801 := by
  unfold tailWord_2643624
  simp only [CollatzResearch.WordTrace]
  refine ⟨48210444287304608939476963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64280592383072811919302617 48210444287304608939476963)
  ·
    refine ⟨72315666430956913409215445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48210444287304608939476963 72315666430956913409215445)
    ·
      refine ⟨1694898431975552658028487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 72315666430956913409215445 1694898431975552658028487)
      ·
        refine ⟨2542347647963328987042731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1694898431975552658028487 2542347647963328987042731)
        ·
          refine ⟨3813521471944993480564097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2542347647963328987042731 3813521471944993480564097)
          ·
            refine ⟨2860141103958745110423073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3813521471944993480564097 2860141103958745110423073)
            ·
              refine ⟨2145105827969058832817305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2860141103958745110423073 2145105827969058832817305)
              ·
                refine ⟨1608829370976794124612979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2145105827969058832817305 1608829370976794124612979)
                ·
                  refine ⟨2413244056465191186919469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1608829370976794124612979 2413244056465191186919469)
                  ·
                    refine ⟨904966521174446695094801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2413244056465191186919469 904966521174446695094801)
                    ·
                      rfl

theorem cell22_2643624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_2643624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643624 prefixEnd_2643624 := by exact prefixLift 2643624
  have htrace : WordTrace (prefixWord ++ tailWord_2643624) baseStart_2643624 baseEnd_2643624 := by
    simpa [prefixWord, tailWord_2643624, baseEnd_2643624] using wordTrace_append hprefix tailTrace_2643624
  have hstable : (prefixWord ++ tailWord_2643624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643624).length < 2 ^ (prefixWord ++ tailWord_2643624).sum := by decide
  have hdescent : baseEnd_2643624 < baseStart_2643624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643642 : List Nat := [3, 1, 1, 1, 2, 4, 3, 7]
def baseStart_2643642 : Nat := 118140960795 + 2643642 * 2 ^ 59
def prefixEnd_2643642 : Nat := 4983230072969 + 3 ^ 40 * 2643642 * 2
def baseEnd_2643642 : Nat := 100552520326922294238305

theorem tailTrace_2643642 : CollatzResearch.WordTrace tailWord_2643642 prefixEnd_2643642 100552520326922294238305 := by
  unfold tailWord_2643642
  simp only [CollatzResearch.WordTrace]
  refine ⟨24105386272136001738277295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64281030059029337968739453 24105386272136001738277295)
  ·
    refine ⟨36158079408204002607415943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24105386272136001738277295 36158079408204002607415943)
    ·
      refine ⟨54237119112306003911123915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36158079408204002607415943 54237119112306003911123915)
      ·
        refine ⟨81355678668459005866685873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54237119112306003911123915 81355678668459005866685873)
        ·
          refine ⟨61016759001344254400014405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81355678668459005866685873 61016759001344254400014405)
          ·
            refine ⟨11440642312752047700002701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61016759001344254400014405 11440642312752047700002701)
            ·
              refine ⟨4290240867282017887501013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11440642312752047700002701 4290240867282017887501013)
              ·
                refine ⟨100552520326922294238305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4290240867282017887501013 100552520326922294238305)
                ·
                  rfl

theorem cell22_2643642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 7].length) (baseStart_2643642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643642 prefixEnd_2643642 := by exact prefixLift 2643642
  have htrace : WordTrace (prefixWord ++ tailWord_2643642) baseStart_2643642 baseEnd_2643642 := by
    simpa [prefixWord, tailWord_2643642, baseEnd_2643642] using wordTrace_append hprefix tailTrace_2643642
  have hstable : (prefixWord ++ tailWord_2643642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643642).length < 2 ^ (prefixWord ++ tailWord_2643642).sum := by decide
  have hdescent : baseEnd_2643642 < baseStart_2643642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643646 : List Nat := [4, 2, 1, 1, 2, 2, 2, 3, 2, 3]
def baseStart_2643646 : Nat := 118140960795 + 2643646 * 2 ^ 59
def prefixEnd_2643646 : Nat := 4983230072969 + 3 ^ 40 * 2643646 * 2
def baseEnd_2643646 : Nat := 904974052224045971044733

theorem tailTrace_2643646 : CollatzResearch.WordTrace tailWord_2643646 prefixEnd_2643646 904974052224045971044733 := by
  unfold tailWord_2643646
  simp only [CollatzResearch.WordTrace]
  refine ⟨12052711372566189454531849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64281127320353010424169861 12052711372566189454531849)
  ·
    refine ⟨9039533529424642090898887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12052711372566189454531849 9039533529424642090898887)
    ·
      refine ⟨13559300294136963136348331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9039533529424642090898887 13559300294136963136348331)
      ·
        refine ⟨20338950441205444704522497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13559300294136963136348331 20338950441205444704522497)
        ·
          refine ⟨15254212830904083528391873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20338950441205444704522497 15254212830904083528391873)
          ·
            refine ⟨11440659623178062646293905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15254212830904083528391873 11440659623178062646293905)
            ·
              refine ⟨8580494717383546984720429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11440659623178062646293905 8580494717383546984720429)
              ·
                refine ⟨3217685519018830119270161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8580494717383546984720429 3217685519018830119270161)
                ·
                  refine ⟨2413264139264122589452621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3217685519018830119270161 2413264139264122589452621)
                  ·
                    refine ⟨904974052224045971044733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2413264139264122589452621 904974052224045971044733)
                    ·
                      rfl

theorem cell22_2643646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_2643646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643646 prefixEnd_2643646 := by exact prefixLift 2643646
  have htrace : WordTrace (prefixWord ++ tailWord_2643646) baseStart_2643646 baseEnd_2643646 := by
    simpa [prefixWord, tailWord_2643646, baseEnd_2643646] using wordTrace_append hprefix tailTrace_2643646
  have hstable : (prefixWord ++ tailWord_2643646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643646).length < 2 ^ (prefixWord ++ tailWord_2643646).sum := by decide
  have hdescent : baseEnd_2643646 < baseStart_2643646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643661 : List Nat := [1, 6, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_2643661 : Nat := 118140960795 + 2643661 * 2 ^ 59
def prefixEnd_2643661 : Nat := 4983230072969 + 3 ^ 40 * 2643661 * 2
def baseEnd_2643661 : Nat := 904979187030590931919687

theorem tailTrace_2643661 : CollatzResearch.WordTrace tailWord_2643661 prefixEnd_2643661 904979187030590931919687 := by
  unfold tailWord_2643661
  simp only [CollatzResearch.WordTrace]
  refine ⟨96422238075475173198050837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64281492050316782132033891 96422238075475173198050837)
  ·
    refine ⟨4519792409787898743658633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 96422238075475173198050837 4519792409787898743658633)
    ·
      refine ⟨3389844307340924057743975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4519792409787898743658633 3389844307340924057743975)
      ·
        refine ⟨5084766461011386086615963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3389844307340924057743975 5084766461011386086615963)
        ·
          refine ⟨7627149691517079129923945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5084766461011386086615963 7627149691517079129923945)
          ·
            refine ⟨5720362268637809347442959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7627149691517079129923945 5720362268637809347442959)
            ·
              refine ⟨8580543402956714021164439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5720362268637809347442959 8580543402956714021164439)
              ·
                refine ⟨12870815104435071031746659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8580543402956714021164439 12870815104435071031746659)
                ·
                  refine ⟨19306222656652606547619989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12870815104435071031746659 19306222656652606547619989)
                  ·
                    refine ⟨904979187030590931919687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19306222656652606547619989 904979187030590931919687)
                    ·
                      rfl

theorem cell22_2643661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_2643661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643661 prefixEnd_2643661 := by exact prefixLift 2643661
  have htrace : WordTrace (prefixWord ++ tailWord_2643661) baseStart_2643661 baseEnd_2643661 := by
    simpa [prefixWord, tailWord_2643661, baseEnd_2643661] using wordTrace_append hprefix tailTrace_2643661
  have hstable : (prefixWord ++ tailWord_2643661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643661).length < 2 ^ (prefixWord ++ tailWord_2643661).sum := by decide
  have hdescent : baseEnd_2643661 < baseStart_2643661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643691 : List Nat := [1, 1, 1, 1, 2, 4, 4, 4, 1, 3]
def baseStart_2643691 : Nat := 118140960795 + 2643691 * 2 ^ 59
def prefixEnd_2643691 : Nat := 4983230072969 + 3 ^ 40 * 2643691 * 2
def baseEnd_2643691 : Nat := 904989456643680853669595

theorem tailTrace_2643691 : CollatzResearch.WordTrace tailWord_2643691 prefixEnd_2643691 904989456643680853669595 := by
  unfold tailWord_2643691
  simp only [CollatzResearch.WordTrace]
  refine ⟨96423332265366488321642927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64282221510244325547761951 96423332265366488321642927)
  ·
    refine ⟨144634998398049732482464391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96423332265366488321642927 144634998398049732482464391)
    ·
      refine ⟨216952497597074598723696587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144634998398049732482464391 216952497597074598723696587)
      ·
        refine ⟨325428746395611898085544881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216952497597074598723696587 325428746395611898085544881)
        ·
          refine ⟨244071559796708923564158661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325428746395611898085544881 244071559796708923564158661)
          ·
            refine ⟨45763417461882923168279749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 244071559796708923564158661 45763417461882923168279749)
            ·
              refine ⟨8580640774103048094052453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45763417461882923168279749 8580640774103048094052453)
              ·
                refine ⟨1608870145144321517634835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8580640774103048094052453 1608870145144321517634835)
                ·
                  refine ⟨2413305217716482276452253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1608870145144321517634835 2413305217716482276452253)
                  ·
                    refine ⟨904989456643680853669595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2413305217716482276452253 904989456643680853669595)
                    ·
                      rfl

theorem cell22_2643691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4, 1, 3].length) (baseStart_2643691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643691 prefixEnd_2643691 := by exact prefixLift 2643691
  have htrace : WordTrace (prefixWord ++ tailWord_2643691) baseStart_2643691 baseEnd_2643691 := by
    simpa [prefixWord, tailWord_2643691, baseEnd_2643691] using wordTrace_append hprefix tailTrace_2643691
  have hstable : (prefixWord ++ tailWord_2643691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643691).length < 2 ^ (prefixWord ++ tailWord_2643691).sum := by decide
  have hdescent : baseEnd_2643691 < baseStart_2643691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643742 : List Nat := [4, 3, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_2643742 : Nat := 118140960795 + 2643742 * 2 ^ 59
def prefixEnd_2643742 : Nat := 4983230072969 + 3 ^ 40 * 2643742 * 2
def baseEnd_2643742 : Nat := 905006914985933720644439

theorem tailTrace_2643742 : CollatzResearch.WordTrace tailWord_2643742 prefixEnd_2643742 905006914985933720644439 := by
  unfold tailWord_2643742
  simp only [CollatzResearch.WordTrace]
  refine ⟨12053149048522715503968685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64283461592121149354499653 12053149048522715503968685)
  ·
    refine ⟨4519930893196018313988257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12053149048522715503968685 4519930893196018313988257)
    ·
      refine ⟨3389948169897013735491193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4519930893196018313988257 3389948169897013735491193)
      ·
        refine ⟨2542461127422760301618395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3389948169897013735491193 2542461127422760301618395)
        ·
          refine ⟨3813691691134140452427593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2542461127422760301618395 3813691691134140452427593)
          ·
            refine ⟨2860268768350605339320695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3813691691134140452427593 2860268768350605339320695)
            ·
              refine ⟨4290403152525908008981043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2860268768350605339320695 4290403152525908008981043)
              ·
                refine ⟨6435604728788862013471565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4290403152525908008981043 6435604728788862013471565)
                ·
                  refine ⟨2413351773295823255051837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6435604728788862013471565 2413351773295823255051837)
                  ·
                    refine ⟨905006914985933720644439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2413351773295823255051837 905006914985933720644439)
                    ·
                      rfl

theorem cell22_2643742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_2643742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643742 prefixEnd_2643742 := by exact prefixLift 2643742
  have htrace : WordTrace (prefixWord ++ tailWord_2643742) baseStart_2643742 baseEnd_2643742 := by
    simpa [prefixWord, tailWord_2643742, baseEnd_2643742] using wordTrace_append hprefix tailTrace_2643742
  have hstable : (prefixWord ++ tailWord_2643742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643742).length < 2 ^ (prefixWord ++ tailWord_2643742).sum := by decide
  have hdescent : baseEnd_2643742 < baseStart_2643742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643749 : List Nat := [1, 3, 1, 2, 3, 2, 3, 1, 6]
def baseStart_2643749 : Nat := 118140960795 + 2643749 * 2 ^ 59
def prefixEnd_2643749 : Nat := 4983230072969 + 3 ^ 40 * 2643749 * 2
def baseEnd_2643749 : Nat := 301669770409662678573139

theorem tailTrace_2643749 : CollatzResearch.WordTrace tailWord_2643749 prefixEnd_2643749 301669770409662678573139 := by
  unfold tailWord_2643749
  simp only [CollatzResearch.WordTrace]
  refine ⟨96425447699156364227254301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64283631799437576151502867 96425447699156364227254301)
  ·
    refine ⟨36159542887183636585220363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96425447699156364227254301 36159542887183636585220363)
    ·
      refine ⟨54239314330775454877830545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36159542887183636585220363 54239314330775454877830545)
      ·
        refine ⟨40679485748081591158372909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54239314330775454877830545 40679485748081591158372909)
        ·
          refine ⟨15254807155530596684389841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40679485748081591158372909 15254807155530596684389841)
          ·
            refine ⟨11441105366647947513292381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15254807155530596684389841 11441105366647947513292381)
            ·
              refine ⟨4290414512492980317484643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11441105366647947513292381 4290414512492980317484643)
              ·
                refine ⟨6435621768739470476226965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4290414512492980317484643 6435621768739470476226965)
                ·
                  refine ⟨301669770409662678573139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6435621768739470476226965 301669770409662678573139)
                  ·
                    rfl

theorem cell22_2643749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 6].length) (baseStart_2643749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643749 prefixEnd_2643749 := by exact prefixLift 2643749
  have htrace : WordTrace (prefixWord ++ tailWord_2643749) baseStart_2643749 baseEnd_2643749 := by
    simpa [prefixWord, tailWord_2643749, baseEnd_2643749] using wordTrace_append hprefix tailTrace_2643749
  have hstable : (prefixWord ++ tailWord_2643749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643749).length < 2 ^ (prefixWord ++ tailWord_2643749).sum := by decide
  have hdescent : baseEnd_2643749 < baseStart_2643749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643779 : List Nat := [1, 1, 1, 3, 1, 5, 1, 3, 2, 4]
def baseStart_2643779 : Nat := 118140960795 + 2643779 * 2 ^ 59
def prefixEnd_2643779 : Nat := 4983230072969 + 3 ^ 40 * 2643779 * 2
def baseEnd_2643779 : Nat := 905019580842077957469325

theorem tailTrace_2643779 : CollatzResearch.WordTrace tailWord_2643779 prefixEnd_2643779 905019580842077957469325 := by
  unfold tailWord_2643779
  simp only [CollatzResearch.WordTrace]
  refine ⟨96426541889047679350846391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64284361259365119567230927 96426541889047679350846391)
  ·
    refine ⟨144639812833571519026269587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96426541889047679350846391 144639812833571519026269587)
    ·
      refine ⟨216959719250357278539404381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144639812833571519026269587 216959719250357278539404381)
      ·
        refine ⟨81359894718883979452276643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216959719250357278539404381 81359894718883979452276643)
        ·
          refine ⟨122039842078325969178414965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81359894718883979452276643 122039842078325969178414965)
          ·
            refine ⟨11441235194843059610476403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122039842078325969178414965 11441235194843059610476403)
            ·
              refine ⟨17161852792264589415714605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11441235194843059610476403 17161852792264589415714605)
              ·
                refine ⟨6435694797099221030892977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17161852792264589415714605 6435694797099221030892977)
                ·
                  refine ⟨4826771097824415773169733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6435694797099221030892977 4826771097824415773169733)
                  ·
                    refine ⟨905019580842077957469325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4826771097824415773169733 905019580842077957469325)
                    ·
                      rfl

theorem cell22_2643779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 4].length) (baseStart_2643779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643779 prefixEnd_2643779 := by exact prefixLift 2643779
  have htrace : WordTrace (prefixWord ++ tailWord_2643779) baseStart_2643779 baseEnd_2643779 := by
    simpa [prefixWord, tailWord_2643779, baseEnd_2643779] using wordTrace_append hprefix tailTrace_2643779
  have hstable : (prefixWord ++ tailWord_2643779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643779).length < 2 ^ (prefixWord ++ tailWord_2643779).sum := by decide
  have hdescent : baseEnd_2643779 < baseStart_2643779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643796 : List Nat := [2, 4, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_2643796 : Nat := 118140960795 + 2643796 * 2 ^ 59
def prefixEnd_2643796 : Nat := 4983230072969 + 3 ^ 40 * 2643796 * 2
def baseEnd_2643796 : Nat := 905025400289495579794273

theorem tailTrace_2643796 : CollatzResearch.WordTrace tailWord_2643796 prefixEnd_2643796 905025400289495579794273 := by
  unfold tailWord_2643796
  simp only [CollatzResearch.WordTrace]
  refine ⟨48213580964993045627107621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64284774619990727502810161 48213580964993045627107621)
  ·
    refine ⟨9040046430936196055082679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48213580964993045627107621 9040046430936196055082679)
    ·
      refine ⟨13560069646404294082624019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9040046430936196055082679 13560069646404294082624019)
      ·
        refine ⟨20340104469606441123936029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13560069646404294082624019 20340104469606441123936029)
        ·
          refine ⟨7627539176102415421476011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20340104469606441123936029 7627539176102415421476011)
          ·
            refine ⟨11441308764153623132214017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7627539176102415421476011 11441308764153623132214017)
            ·
              refine ⟨8580981573115217349160513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11441308764153623132214017 8580981573115217349160513)
              ·
                refine ⟨6435736179836413011870385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8580981573115217349160513 6435736179836413011870385)
                ·
                  refine ⟨4826802134877309758902789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6435736179836413011870385 4826802134877309758902789)
                  ·
                    refine ⟨905025400289495579794273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4826802134877309758902789 905025400289495579794273)
                    ·
                      rfl

theorem cell22_2643796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_2643796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643796 prefixEnd_2643796 := by exact prefixLift 2643796
  have htrace : WordTrace (prefixWord ++ tailWord_2643796) baseStart_2643796 baseEnd_2643796 := by
    simpa [prefixWord, tailWord_2643796, baseEnd_2643796] using wordTrace_append hprefix tailTrace_2643796
  have hstable : (prefixWord ++ tailWord_2643796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643796).length < 2 ^ (prefixWord ++ tailWord_2643796).sum := by decide
  have hdescent : baseEnd_2643796 < baseStart_2643796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643811 : List Nat := [1, 1, 1, 5, 4, 2, 1, 7]
def baseStart_2643811 : Nat := 118140960795 + 2643811 * 2 ^ 59
def prefixEnd_2643811 : Nat := 4983230072969 + 3 ^ 40 * 2643811 * 2
def baseEnd_2643811 : Nat := 100558948344004504518803

theorem tailTrace_2643811 : CollatzResearch.WordTrace tailWord_2643811 prefixEnd_2643811 100558948344004504518803 := by
  unfold tailWord_2643811
  simp only [CollatzResearch.WordTrace]
  refine ⟨96427709024931748816011287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64285139349954499210674191 96427709024931748816011287)
  ·
    refine ⟨144641563537397623224016931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96427709024931748816011287 144641563537397623224016931)
    ·
      refine ⟨216962345306096434836025397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144641563537397623224016931 216962345306096434836025397)
      ·
        refine ⟨20340219872446540765877381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 216962345306096434836025397 20340219872446540765877381)
        ·
          refine ⟨3813791226083726393602009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20340219872446540765877381 3813791226083726393602009)
          ·
            refine ⟨2860343419562794795201507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3813791226083726393602009 2860343419562794795201507)
            ·
              refine ⟨4290515129344192192802261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2860343419562794795201507 4290515129344192192802261)
              ·
                refine ⟨100558948344004504518803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4290515129344192192802261 100558948344004504518803)
                ·
                  rfl

theorem cell22_2643811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 7].length) (baseStart_2643811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643811 prefixEnd_2643811 := by exact prefixLift 2643811
  have htrace : WordTrace (prefixWord ++ tailWord_2643811) baseStart_2643811 baseEnd_2643811 := by
    simpa [prefixWord, tailWord_2643811, baseEnd_2643811] using wordTrace_append hprefix tailTrace_2643811
  have hstable : (prefixWord ++ tailWord_2643811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643811).length < 2 ^ (prefixWord ++ tailWord_2643811).sum := by decide
  have hdescent : baseEnd_2643811 < baseStart_2643811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643830 : List Nat := [5, 1, 1, 3, 2, 2, 1, 1, 2, 4]
def baseStart_2643830 : Nat := 118140960795 + 2643830 * 2 ^ 59
def prefixEnd_2643830 : Nat := 4983230072969 + 3 ^ 40 * 2643830 * 2
def baseEnd_2643830 : Nat := 905037039184330824444169

theorem tailTrace_2643830 : CollatzResearch.WordTrace tailWord_2643830 prefixEnd_2643830 905037039184330824444169 := by
  unfold tailWord_2643830
  simp only [CollatzResearch.WordTrace]
  refine ⟨6026775125741432191309559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64285601341241943373968629 6026775125741432191309559)
  ·
    refine ⟨9040162688612148286964339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6026775125741432191309559 9040162688612148286964339)
    ·
      refine ⟨13560244032918222430446509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9040162688612148286964339 13560244032918222430446509)
      ·
        refine ⟨5085091512344333411417441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13560244032918222430446509 5085091512344333411417441)
        ·
          refine ⟨3813818634258250058563081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5085091512344333411417441 3813818634258250058563081)
          ·
            refine ⟨2860363975693687543922311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3813818634258250058563081 2860363975693687543922311)
            ·
              refine ⟨4290545963540531315883467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2860363975693687543922311 4290545963540531315883467)
              ·
                refine ⟨6435818945310796973825201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4290545963540531315883467 6435818945310796973825201)
                ·
                  refine ⟨4826864208983097730368901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6435818945310796973825201 4826864208983097730368901)
                  ·
                    refine ⟨905037039184330824444169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4826864208983097730368901 905037039184330824444169)
                    ·
                      rfl

theorem cell22_2643830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_2643830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643830 prefixEnd_2643830 := by exact prefixLift 2643830
  have htrace : WordTrace (prefixWord ++ tailWord_2643830) baseStart_2643830 baseEnd_2643830 := by
    simpa [prefixWord, tailWord_2643830, baseEnd_2643830] using wordTrace_append hprefix tailTrace_2643830
  have hstable : (prefixWord ++ tailWord_2643830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643830).length < 2 ^ (prefixWord ++ tailWord_2643830).sum := by decide
  have hdescent : baseEnd_2643830 < baseStart_2643830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643843 : List Nat := [1, 1, 1, 3, 4, 2, 1, 5, 1, 3]
def baseStart_2643843 : Nat := 118140960795 + 2643843 * 2 ^ 59
def prefixEnd_2643843 : Nat := 4983230072969 + 3 ^ 40 * 2643843 * 2
def baseEnd_2643843 : Nat := 905041489350003123869129

theorem tailTrace_2643843 : CollatzResearch.WordTrace tailWord_2643843 prefixEnd_2643843 905041489350003123869129 := by
  unfold tailWord_2643843
  simp only [CollatzResearch.WordTrace]
  refine ⟨96428876160815818281176183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64285917440543878854117455 96428876160815818281176183)
  ·
    refine ⟨144643314241223727421764275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96428876160815818281176183 144643314241223727421764275)
    ·
      refine ⟨216964971361835591132646413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144643314241223727421764275 216964971361835591132646413)
      ·
        refine ⟨81361864260688346674742405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216964971361835591132646413 81361864260688346674742405)
        ·
          refine ⟨15255349548879065001514201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81361864260688346674742405 15255349548879065001514201)
          ·
            refine ⟨11441512161659298751135651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15255349548879065001514201 11441512161659298751135651)
            ·
              refine ⟨17162268242488948126703477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11441512161659298751135651 17162268242488948126703477)
              ·
                refine ⟨1608962647733338886878451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17162268242488948126703477 1608962647733338886878451)
                ·
                  refine ⟨2413443971600008330317677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1608962647733338886878451 2413443971600008330317677)
                  ·
                    refine ⟨905041489350003123869129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2413443971600008330317677 905041489350003123869129)
                    ·
                      rfl

theorem cell22_2643843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5, 1, 3].length) (baseStart_2643843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643843 prefixEnd_2643843 := by exact prefixLift 2643843
  have htrace : WordTrace (prefixWord ++ tailWord_2643843) baseStart_2643843 baseEnd_2643843 := by
    simpa [prefixWord, tailWord_2643843, baseEnd_2643843] using wordTrace_append hprefix tailTrace_2643843
  have hstable : (prefixWord ++ tailWord_2643843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643843).length < 2 ^ (prefixWord ++ tailWord_2643843).sum := by decide
  have hdescent : baseEnd_2643843 < baseStart_2643843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643860 : List Nat := [2, 4, 2, 1, 1, 2, 2, 4, 1, 3]
def baseStart_2643860 : Nat := 118140960795 + 2643860 * 2 ^ 59
def prefixEnd_2643860 : Nat := 4983230072969 + 3 ^ 40 * 2643860 * 2
def baseEnd_2643860 : Nat := 905047308797420746194077

theorem tailTrace_2643860 : CollatzResearch.WordTrace tailWord_2643860 prefixEnd_2643860 905047308797420746194077 := by
  unfold tailWord_2643860
  simp only [CollatzResearch.WordTrace]
  refine ⟨48214748100877115092272517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64286330801169486789696689 48214748100877115092272517)
  ·
    refine ⟨9040265268914459079801097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48214748100877115092272517 9040265268914459079801097)
    ·
      refine ⟨6780198951685844309850823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9040265268914459079801097 6780198951685844309850823)
      ·
        refine ⟨10170298427528766464776235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6780198951685844309850823 10170298427528766464776235)
        ·
          refine ⟨15255447641293149697164353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10170298427528766464776235 15255447641293149697164353)
          ·
            refine ⟨11441585730969862272873265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15255447641293149697164353 11441585730969862272873265)
            ·
              refine ⟨8581189298227396704654949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11441585730969862272873265 8581189298227396704654949)
              ·
                refine ⟨1608972993417636882122803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8581189298227396704654949 1608972993417636882122803)
                ·
                  refine ⟨2413459490126455323184205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1608972993417636882122803 2413459490126455323184205)
                  ·
                    refine ⟨905047308797420746194077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2413459490126455323184205 905047308797420746194077)
                    ·
                      rfl

theorem cell22_2643860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_2643860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643860 prefixEnd_2643860 := by exact prefixLift 2643860
  have htrace : WordTrace (prefixWord ++ tailWord_2643860) baseStart_2643860 baseEnd_2643860 := by
    simpa [prefixWord, tailWord_2643860, baseEnd_2643860] using wordTrace_append hprefix tailTrace_2643860
  have hstable : (prefixWord ++ tailWord_2643860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643860).length < 2 ^ (prefixWord ++ tailWord_2643860).sum := by decide
  have hdescent : baseEnd_2643860 < baseStart_2643860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643959 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 6, 6]
def baseStart_2643959 : Nat := 118140960795 + 2643959 * 2 ^ 59
def prefixEnd_2643959 : Nat := 4983230072969 + 3 ^ 40 * 2643959 * 2
def baseEnd_2643959 : Nat := 905081198520617487968773

theorem tailTrace_2643959 : CollatzResearch.WordTrace tailWord_2643959 prefixEnd_2643959 905081198520617487968773 := by
  unfold tailWord_2643959
  simp only [CollatzResearch.WordTrace]
  refine ⟨96433107028395570092398931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64288738018930380061599287 96433107028395570092398931)
  ·
    refine ⟨144649660542593355138598397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96433107028395570092398931 144649660542593355138598397)
    ·
      refine ⟨54243622703472508176974399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144649660542593355138598397 54243622703472508176974399)
      ·
        refine ⟨81365434055208762265461599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54243622703472508176974399 81365434055208762265461599)
        ·
          refine ⟨122048151082813143398192399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81365434055208762265461599 122048151082813143398192399)
          ·
            refine ⟨183072226624219715097288599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122048151082813143398192399 183072226624219715097288599)
            ·
              refine ⟨274608339936329572645932899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183072226624219715097288599 274608339936329572645932899)
              ·
                refine ⟨411912509904494358968899349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274608339936329572645932899 411912509904494358968899349)
                ·
                  refine ⟨19308398901773173076667157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 411912509904494358968899349 19308398901773173076667157)
                  ·
                    refine ⟨905081198520617487968773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19308398901773173076667157 905081198520617487968773)
                    ·
                      rfl

theorem cell22_2643959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_2643959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2643959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2643959 prefixEnd_2643959 := by exact prefixLift 2643959
  have htrace : WordTrace (prefixWord ++ tailWord_2643959) baseStart_2643959 baseEnd_2643959 := by
    simpa [prefixWord, tailWord_2643959, baseEnd_2643959] using wordTrace_append hprefix tailTrace_2643959
  have hstable : (prefixWord ++ tailWord_2643959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643959).length < 2 ^ (prefixWord ++ tailWord_2643959).sum := by decide
  have hdescent : baseEnd_2643959 < baseStart_2643959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644025 : List Nat := [1, 2, 1, 5, 3, 2, 1, 2, 5]
def baseStart_2644025 : Nat := 118140960795 + 2644025 * 2 ^ 59
def prefixEnd_2644025 : Nat := 4983230072969 + 3 ^ 40 * 2644025 * 2
def baseEnd_2644025 : Nat := 301701263889805105272857

theorem tailTrace_2644025 : CollatzResearch.WordTrace tailWord_2644025 prefixEnd_2644025 301701263889805105272857 := by
  unfold tailWord_2644025
  simp only [CollatzResearch.WordTrace]
  refine ⟨96435514246156463364301529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64290342830770975576201019 96435514246156463364301529)
  ·
    refine ⟨72326635684617347523226147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96435514246156463364301529 72326635684617347523226147)
    ·
      refine ⟨108489953526926021284839221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72326635684617347523226147 108489953526926021284839221)
      ·
        refine ⟨10170933143149314495453677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108489953526926021284839221 10170933143149314495453677)
        ·
          refine ⟨3814099928680992935795129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10170933143149314495453677 3814099928680992935795129)
          ·
            refine ⟨2860574946510744701846347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3814099928680992935795129 2860574946510744701846347)
            ·
              refine ⟨4290862419766117052769521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2860574946510744701846347 4290862419766117052769521)
              ·
                refine ⟨3218146814824587789577141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4290862419766117052769521 3218146814824587789577141)
                ·
                  refine ⟨301701263889805105272857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3218146814824587789577141 301701263889805105272857)
                  ·
                    rfl

theorem cell22_2644025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 5].length) (baseStart_2644025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2644025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2644025 prefixEnd_2644025 := by exact prefixLift 2644025
  have htrace : WordTrace (prefixWord ++ tailWord_2644025) baseStart_2644025 baseEnd_2644025 := by
    simpa [prefixWord, tailWord_2644025, baseEnd_2644025] using wordTrace_append hprefix tailTrace_2644025
  have hstable : (prefixWord ++ tailWord_2644025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644025).length < 2 ^ (prefixWord ++ tailWord_2644025).sum := by decide
  have hdescent : baseEnd_2644025 < baseStart_2644025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644068 : List Nat := [2, 3, 1, 1, 2, 1, 3, 2, 4, 3]
def baseStart_2644068 : Nat := 118140960795 + 2644068 * 2 ^ 59
def prefixEnd_2644068 : Nat := 4983230072969 + 3 ^ 40 * 2644068 * 2
def baseEnd_2644068 : Nat := 905118511448177536993439

theorem tailTrace_2644068 : CollatzResearch.WordTrace tailWord_2644068 prefixEnd_2644068 905118511448177536993439 := by
  unfold tailWord_2644068
  simp only [CollatzResearch.WordTrace]
  refine ⟨48218541292500340854058429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64291388390000454472077905 48218541292500340854058429)
  ·
    refine ⟨18081952984687627820271911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48218541292500340854058429 18081952984687627820271911)
    ·
      refine ⟨27122929477031441730407867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18081952984687627820271911 27122929477031441730407867)
      ·
        refine ⟨40684394215547162595611801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27122929477031441730407867 40684394215547162595611801)
        ·
          refine ⟨30513295661660371946708851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40684394215547162595611801 30513295661660371946708851)
          ·
            refine ⟨45769943492490557920063277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30513295661660371946708851 45769943492490557920063277)
            ·
              refine ⟨17163728809683959220023729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45769943492490557920063277 17163728809683959220023729)
              ·
                refine ⟨12872796607262969415017797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17163728809683959220023729 12872796607262969415017797)
                ·
                  refine ⟨2413649363861806765315837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12872796607262969415017797 2413649363861806765315837)
                  ·
                    refine ⟨905118511448177536993439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2413649363861806765315837 905118511448177536993439)
                    ·
                      rfl

theorem cell22_2644068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_2644068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2644068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2644068 prefixEnd_2644068 := by exact prefixLift 2644068
  have htrace : WordTrace (prefixWord ++ tailWord_2644068) baseStart_2644068 baseEnd_2644068 := by
    simpa [prefixWord, tailWord_2644068, baseEnd_2644068] using wordTrace_append hprefix tailTrace_2644068
  have hstable : (prefixWord ++ tailWord_2644068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644068).length < 2 ^ (prefixWord ++ tailWord_2644068).sum := by decide
  have hdescent : baseEnd_2644068 < baseStart_2644068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644194 : List Nat := [3, 3, 4, 1, 1, 1, 1, 1, 7]
def baseStart_2644194 : Nat := 118140960795 + 2644194 * 2 ^ 59
def prefixEnd_2644194 : Nat := 4983230072969 + 3 ^ 40 * 2644194 * 2
def baseEnd_2644194 : Nat := 301720547941051736114351

theorem tailTrace_2644194 : CollatzResearch.WordTrace tailWord_2644194 prefixEnd_2644194 301720547941051736114351 := by
  unfold tailWord_2644194
  simp only [CollatzResearch.WordTrace]
  refine ⟨24110419545636051306800909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64294452121696136818135757 24110419545636051306800909)
  ·
    refine ⟨9041407329613519240050341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24110419545636051306800909 9041407329613519240050341)
    ·
      refine ⟨1695263874302534857509439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9041407329613519240050341 1695263874302534857509439)
      ·
        refine ⟨2542895811453802286264159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1695263874302534857509439 2542895811453802286264159)
        ·
          refine ⟨3814343717180703429396239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2542895811453802286264159 3814343717180703429396239)
          ·
            refine ⟨5721515575771055144094359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3814343717180703429396239 5721515575771055144094359)
            ·
              refine ⟨8582273363656582716141539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5721515575771055144094359 8582273363656582716141539)
              ·
                refine ⟨12873410045484874074212309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8582273363656582716141539 12873410045484874074212309)
                ·
                  refine ⟨301720547941051736114351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12873410045484874074212309 301720547941051736114351)
                  ·
                    rfl

theorem cell22_2644194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_2644194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2644194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2644194 prefixEnd_2644194 := by exact prefixLift 2644194
  have htrace : WordTrace (prefixWord ++ tailWord_2644194) baseStart_2644194 baseEnd_2644194 := by
    simpa [prefixWord, tailWord_2644194, baseEnd_2644194] using wordTrace_append hprefix tailTrace_2644194
  have hstable : (prefixWord ++ tailWord_2644194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644194).length < 2 ^ (prefixWord ++ tailWord_2644194).sum := by decide
  have hdescent : baseEnd_2644194 < baseStart_2644194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644218 : List Nat := [3, 1, 1, 1, 1, 5, 1, 2, 1, 6]
def baseStart_2644218 : Nat := 118140960795 + 2644218 * 2 ^ 59
def prefixEnd_2644218 : Nat := 4983230072969 + 3 ^ 40 * 2644218 * 2
def baseEnd_2644218 : Nat := 905169859513627145742979

theorem tailTrace_2644218 : CollatzResearch.WordTrace tailWord_2644218 prefixEnd_2644218 905169859513627145742979 := by
  unfold tailWord_2644218
  simp only [CollatzResearch.WordTrace]
  refine ⟨24110638383614314331519327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64295035689638171550718205 24110638383614314331519327)
  ·
    refine ⟨36165957575421471497278991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24110638383614314331519327 36165957575421471497278991)
    ·
      refine ⟨54248936363132207245918487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36165957575421471497278991 54248936363132207245918487)
      ·
        refine ⟨81373404544698310868877731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54248936363132207245918487 81373404544698310868877731)
        ·
          refine ⟨122060106817047466303316597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81373404544698310868877731 122060106817047466303316597)
          ·
            refine ⟨11443135014098199965935931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122060106817047466303316597 11443135014098199965935931)
            ·
              refine ⟨17164702521147299948903897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11443135014098199965935931 17164702521147299948903897)
              ·
                refine ⟨12873526890860474961677923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17164702521147299948903897 12873526890860474961677923)
                ·
                  refine ⟨19310290336290712442516885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12873526890860474961677923 19310290336290712442516885)
                  ·
                    refine ⟨905169859513627145742979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19310290336290712442516885 905169859513627145742979)
                    ·
                      rfl

theorem cell22_2644218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_2644218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2644218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2644218 prefixEnd_2644218 := by exact prefixLift 2644218
  have htrace : WordTrace (prefixWord ++ tailWord_2644218) baseStart_2644218 baseEnd_2644218 := by
    simpa [prefixWord, tailWord_2644218, baseEnd_2644218] using wordTrace_append hprefix tailTrace_2644218
  have hstable : (prefixWord ++ tailWord_2644218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644218).length < 2 ^ (prefixWord ++ tailWord_2644218).sum := by decide
  have hdescent : baseEnd_2644218 < baseStart_2644218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644220 : List Nat := [2, 2, 2, 1, 4, 1, 3, 1, 1, 5]
def baseStart_2644220 : Nat := 118140960795 + 2644220 * 2 ^ 59
def prefixEnd_2644220 : Nat := 4983230072969 + 3 ^ 40 * 2644220 * 2
def baseEnd_2644220 : Nat := 905170544154499807192973

theorem tailTrace_2644220 : CollatzResearch.WordTrace tailWord_2644220 prefixEnd_2644220 905170544154499807192973 := by
  unfold tailWord_2644220
  simp only [CollatzResearch.WordTrace]
  refine ⟨48221313240225005833825057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64295084320300007778433409 48221313240225005833825057)
  ·
    refine ⟨36165984930168754375368793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48221313240225005833825057 36165984930168754375368793)
    ·
      refine ⟨27124488697626565781526595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36165984930168754375368793 27124488697626565781526595)
      ·
        refine ⟨40686733046439848672289893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27124488697626565781526595 40686733046439848672289893)
        ·
          refine ⟨7628762446207471626054355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40686733046439848672289893 7628762446207471626054355)
          ·
            refine ⟨11443143669311207439081533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7628762446207471626054355 11443143669311207439081533)
            ·
              refine ⟨4291178875991702789655575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11443143669311207439081533 4291178875991702789655575)
              ·
                refine ⟨6436768313987554184483363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4291178875991702789655575 6436768313987554184483363)
                ·
                  refine ⟨9655152470981331276725045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6436768313987554184483363 9655152470981331276725045)
                  ·
                    refine ⟨905170544154499807192973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9655152470981331276725045 905170544154499807192973)
                    ·
                      rfl

theorem cell22_2644220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_2644220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2644220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2644220 prefixEnd_2644220 := by exact prefixLift 2644220
  have htrace : WordTrace (prefixWord ++ tailWord_2644220) baseStart_2644220 baseEnd_2644220 := by
    simpa [prefixWord, tailWord_2644220, baseEnd_2644220] using wordTrace_append hprefix tailTrace_2644220
  have hstable : (prefixWord ++ tailWord_2644220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644220).length < 2 ^ (prefixWord ++ tailWord_2644220).sum := by decide
  have hdescent : baseEnd_2644220 < baseStart_2644220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644233 : List Nat := [1, 2, 1, 1, 3, 5, 1, 8]
def baseStart_2644233 : Nat := 118140960795 + 2644233 * 2 ^ 59
def prefixEnd_2644233 : Nat := 4983230072969 + 3 ^ 40 * 2644233 * 2
def baseEnd_2644233 : Nat := 100574999368908011846437

theorem tailTrace_2644233 : CollatzResearch.WordTrace tailWord_2644233 prefixEnd_2644233 100574999368908011846437 := by
  unfold tailWord_2644233
  simp only [CollatzResearch.WordTrace]
  refine ⟨96443100629402914887873353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64295400419601943258582235 96443100629402914887873353)
  ·
    refine ⟨72332325472052186165905015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96443100629402914887873353 72332325472052186165905015)
    ·
      refine ⟨108498488208078279248857523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72332325472052186165905015 108498488208078279248857523)
      ·
        refine ⟨162747732312117418873286285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108498488208078279248857523 162747732312117418873286285)
        ·
          refine ⟨61030399617044032077482357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162747732312117418873286285 61030399617044032077482357)
          ·
            refine ⟨5721599964097878007263971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61030399617044032077482357 5721599964097878007263971)
            ·
              refine ⟨8582399946146817010895957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5721599964097878007263971 8582399946146817010895957)
              ·
                refine ⟨100574999368908011846437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8582399946146817010895957 100574999368908011846437)
                ·
                  rfl

theorem cell22_2644233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 8].length) (baseStart_2644233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2644233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2644233 prefixEnd_2644233 := by exact prefixLift 2644233
  have htrace : WordTrace (prefixWord ++ tailWord_2644233) baseStart_2644233 baseEnd_2644233 := by
    simpa [prefixWord, tailWord_2644233, baseEnd_2644233] using wordTrace_append hprefix tailTrace_2644233
  have hstable : (prefixWord ++ tailWord_2644233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644233).length < 2 ^ (prefixWord ++ tailWord_2644233).sum := by decide
  have hdescent : baseEnd_2644233 < baseStart_2644233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644250 : List Nat := [3, 1, 1, 3, 4, 2, 8]
def baseStart_2644250 : Nat := 118140960795 + 2644250 * 2 ^ 59
def prefixEnd_2644250 : Nat := 4983230072969 + 3 ^ 40 * 2644250 * 2
def baseEnd_2644250 : Nat := 33525215324725545516403

theorem tailTrace_2644250 : CollatzResearch.WordTrace tailWord_2644250 prefixEnd_2644250 33525215324725545516403 := by
  unfold tailWord_2644250
  simp only [CollatzResearch.WordTrace]
  refine ⟨24110930167585331697810551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64295813780227551194161469 24110930167585331697810551)
  ·
    refine ⟨36166395251377997546715827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24110930167585331697810551 36166395251377997546715827)
    ·
      refine ⟨54249592877066996320073741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36166395251377997546715827 54249592877066996320073741)
      ·
        refine ⟨20343597328900123620027653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54249592877066996320073741 20343597328900123620027653)
        ·
          refine ⟨3814424499168773178755185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20343597328900123620027653 3814424499168773178755185)
          ·
            refine ⟨2860818374376579884066389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3814424499168773178755185 2860818374376579884066389)
            ·
              refine ⟨33525215324725545516403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2860818374376579884066389 33525215324725545516403)
              ·
                rfl

theorem cell22_2644250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 8].length) (baseStart_2644250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2644250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2644250 prefixEnd_2644250 := by exact prefixLift 2644250
  have htrace : WordTrace (prefixWord ++ tailWord_2644250) baseStart_2644250 baseEnd_2644250 := by
    simpa [prefixWord, tailWord_2644250, baseEnd_2644250] using wordTrace_append hprefix tailTrace_2644250
  have hstable : (prefixWord ++ tailWord_2644250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644250).length < 2 ^ (prefixWord ++ tailWord_2644250).sum := by decide
  have hdescent : baseEnd_2644250 < baseStart_2644250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644254 : List Nat := [4, 3, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_2644254 : Nat := 118140960795 + 2644254 * 2 ^ 59
def prefixEnd_2644254 : Nat := 4983230072969 + 3 ^ 40 * 2644254 * 2
def baseEnd_2644254 : Nat := 905182183049335051842869

theorem tailTrace_2644254 : CollatzResearch.WordTrace tailWord_2644254 prefixEnd_2644254 905182183049335051842869 := by
  unfold tailWord_2644254
  simp only [CollatzResearch.WordTrace]
  refine ⟨12055483320290854434298477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64295911041551223649591877 12055483320290854434298477)
  ·
    refine ⟨4520806245109070412861929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12055483320290854434298477 4520806245109070412861929)
    ·
      refine ⟨3390604683831802809646447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4520806245109070412861929 3390604683831802809646447)
      ·
        refine ⟨5085907025747704214469671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3390604683831802809646447 5085907025747704214469671)
        ·
          refine ⟨7628860538621556321704507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5085907025747704214469671 7628860538621556321704507)
          ·
            refine ⟨11443290807932334482556761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7628860538621556321704507 11443290807932334482556761)
            ·
              refine ⟨8582468105949250861917571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11443290807932334482556761 8582468105949250861917571)
              ·
                refine ⟨12873702158923876292876357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8582468105949250861917571 12873702158923876292876357)
                ·
                  refine ⟨2413819154798226804914317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12873702158923876292876357 2413819154798226804914317)
                  ·
                    refine ⟨905182183049335051842869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2413819154798226804914317 905182183049335051842869)
                    ·
                      rfl

theorem cell22_2644254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_2644254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2644254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2644254 prefixEnd_2644254 := by exact prefixLift 2644254
  have htrace : WordTrace (prefixWord ++ tailWord_2644254) baseStart_2644254 baseEnd_2644254 := by
    simpa [prefixWord, tailWord_2644254, baseEnd_2644254] using wordTrace_append hprefix tailTrace_2644254
  have hstable : (prefixWord ++ tailWord_2644254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644254).length < 2 ^ (prefixWord ++ tailWord_2644254).sum := by decide
  have hdescent : baseEnd_2644254 < baseStart_2644254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644293 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 6, 5]
def baseStart_2644293 : Nat := 118140960795 + 2644293 * 2 ^ 59
def prefixEnd_2644293 : Nat := 4983230072969 + 3 ^ 40 * 2644293 * 2
def baseEnd_2644293 : Nat := 905195533546351950117749

theorem tailTrace_2644293 : CollatzResearch.WordTrace tailWord_2644293 prefixEnd_2644293 905195533546351950117749 := by
  unfold tailWord_2644293
  simp only [CollatzResearch.WordTrace]
  refine ⟨96445289009185545135057533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64296859339457030090038355 96445289009185545135057533)
  ·
    refine ⟨36166983378444579425646575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96445289009185545135057533 36166983378444579425646575)
    ·
      refine ⟨54250475067666869138469863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36166983378444579425646575 54250475067666869138469863)
      ·
        refine ⟨81375712601500303707704795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54250475067666869138469863 81375712601500303707704795)
        ·
          refine ⟨122063568902250455561557193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81375712601500303707704795 122063568902250455561557193)
          ·
            refine ⟨91547676676687841671167895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122063568902250455561557193 91547676676687841671167895)
            ·
              refine ⟨137321515015031762506751843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91547676676687841671167895 137321515015031762506751843)
              ·
                refine ⟨205982272522547643760127765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137321515015031762506751843 205982272522547643760127765)
                ·
                  refine ⟨9655419024494420801255989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 205982272522547643760127765 9655419024494420801255989)
                  ·
                    refine ⟨905195533546351950117749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9655419024494420801255989 905195533546351950117749)
                    ·
                      rfl

theorem cell22_2644293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_2644293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2644293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2644293 prefixEnd_2644293 := by exact prefixLift 2644293
  have htrace : WordTrace (prefixWord ++ tailWord_2644293) baseStart_2644293 baseEnd_2644293 := by
    simpa [prefixWord, tailWord_2644293, baseEnd_2644293] using wordTrace_append hprefix tailTrace_2644293
  have hstable : (prefixWord ++ tailWord_2644293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644293).length < 2 ^ (prefixWord ++ tailWord_2644293).sum := by decide
  have hdescent : baseEnd_2644293 < baseStart_2644293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644318 : List Nat := [4, 4, 2, 1, 1, 2, 1, 7]
def baseStart_2644318 : Nat := 118140960795 + 2644318 * 2 ^ 59
def prefixEnd_2644318 : Nat := 4983230072969 + 3 ^ 40 * 2644318 * 2
def baseEnd_2644318 : Nat := 100578232395251135360297

theorem tailTrace_2644318 : CollatzResearch.WordTrace tailWord_2644318 prefixEnd_2644318 100578232395251135360297 := by
  unfold tailWord_2644318
  simp only [CollatzResearch.WordTrace]
  refine ⟨12055775104261871800589701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64297467222729982936478405 12055775104261871800589701)
  ·
    refine ⟨2260457832049100962610569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12055775104261871800589701 2260457832049100962610569)
    ·
      refine ⟨1695343374036825721957927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2260457832049100962610569 1695343374036825721957927)
      ·
        refine ⟨2543015061055238582936891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1695343374036825721957927 2543015061055238582936891)
        ·
          refine ⟨3814522591582857874405337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2543015061055238582936891 3814522591582857874405337)
          ·
            refine ⟨2860891943687143405804003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3814522591582857874405337 2860891943687143405804003)
            ·
              refine ⟨4291337915530715108706005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2860891943687143405804003 4291337915530715108706005)
              ·
                refine ⟨100578232395251135360297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4291337915530715108706005 100578232395251135360297)
                ·
                  rfl

theorem cell22_2644318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 7].length) (baseStart_2644318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2644318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2644318 prefixEnd_2644318 := by exact prefixLift 2644318
  have htrace : WordTrace (prefixWord ++ tailWord_2644318) baseStart_2644318 baseEnd_2644318 := by
    simpa [prefixWord, tailWord_2644318, baseEnd_2644318] using wordTrace_append hprefix tailTrace_2644318
  have hstable : (prefixWord ++ tailWord_2644318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644318).length < 2 ^ (prefixWord ++ tailWord_2644318).sum := by decide
  have hdescent : baseEnd_2644318 < baseStart_2644318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644325 : List Nat := [1, 3, 1, 3, 1, 3, 1, 2, 3, 4]
def baseStart_2644325 : Nat := 118140960795 + 2644325 * 2 ^ 59
def prefixEnd_2644325 : Nat := 4983230072969 + 3 ^ 40 * 2644325 * 2
def baseEnd_2644325 : Nat := 905206487800314533317651

theorem tailTrace_2644325 : CollatzResearch.WordTrace tailWord_2644325 prefixEnd_2644325 905206487800314533317651 := by
  unfold tailWord_2644325
  simp only [CollatzResearch.WordTrace]
  refine ⟨96446456145069614600222429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64297637430046409733481619 96446456145069614600222429)
  ·
    refine ⟨36167421054401105475083411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96446456145069614600222429 36167421054401105475083411)
    ·
      refine ⟨54251131581601658212625117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36167421054401105475083411 54251131581601658212625117)
      ·
        refine ⟨20344174343100621829734419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54251131581601658212625117 20344174343100621829734419)
        ·
          refine ⟨30516261514650932744601629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20344174343100621829734419 30516261514650932744601629)
          ·
            refine ⟨11443598067994099779225611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30516261514650932744601629 11443598067994099779225611)
            ·
              refine ⟨17165397101991149668838417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11443598067994099779225611 17165397101991149668838417)
              ·
                refine ⟨12874047826493362251628813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17165397101991149668838417 12874047826493362251628813)
                ·
                  refine ⟨4827767934935010844360805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12874047826493362251628813 4827767934935010844360805)
                  ·
                    refine ⟨905206487800314533317651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4827767934935010844360805 905206487800314533317651)
                    ·
                      rfl

theorem cell22_2644325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_2644325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2644325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2644325 prefixEnd_2644325 := by exact prefixLift 2644325
  have htrace : WordTrace (prefixWord ++ tailWord_2644325) baseStart_2644325 baseEnd_2644325 := by
    simpa [prefixWord, tailWord_2644325, baseEnd_2644325] using wordTrace_append hprefix tailTrace_2644325
  have hstable : (prefixWord ++ tailWord_2644325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644325).length < 2 ^ (prefixWord ++ tailWord_2644325).sum := by decide
  have hdescent : baseEnd_2644325 < baseStart_2644325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644389 : List Nat := [1, 3, 1, 2, 1, 1, 7, 1, 2, 3]
def baseStart_2644389 : Nat := 118140960795 + 2644389 * 2 ^ 59
def prefixEnd_2644389 : Nat := 4983230072969 + 3 ^ 40 * 2644389 * 2
def baseEnd_2644389 : Nat := 905228396308239699717455

theorem tailTrace_2644389 : CollatzResearch.WordTrace tailWord_2644389 prefixEnd_2644389 905228396308239699717455 := by
  unfold tailWord_2644389
  simp only [CollatzResearch.WordTrace]
  refine ⟨96448790416837753530552221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64299193611225169020368147 96448790416837753530552221)
  ·
    refine ⟨36168296406314157573957083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96448790416837753530552221 36168296406314157573957083)
    ·
      refine ⟨54252444609471236360935625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36168296406314157573957083 54252444609471236360935625)
      ·
        refine ⟨40689333457103427270701719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54252444609471236360935625 40689333457103427270701719)
        ·
          refine ⟨61034000185655140906052579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40689333457103427270701719 61034000185655140906052579)
          ·
            refine ⟨91551000278482711359078869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61034000185655140906052579 91551000278482711359078869)
            ·
              refine ⟨2145726569026938547478411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 91551000278482711359078869 2145726569026938547478411)
              ·
                refine ⟨3218589853540407821217617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2145726569026938547478411 3218589853540407821217617)
                ·
                  refine ⟨2413942390155305865913213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3218589853540407821217617 2413942390155305865913213)
                  ·
                    refine ⟨905228396308239699717455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2413942390155305865913213 905228396308239699717455)
                    ·
                      rfl

theorem cell22_2644389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 2, 3].length) (baseStart_2644389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2644389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2644389 prefixEnd_2644389 := by exact prefixLift 2644389
  have htrace : WordTrace (prefixWord ++ tailWord_2644389) baseStart_2644389 baseEnd_2644389 := by
    simpa [prefixWord, tailWord_2644389, baseEnd_2644389] using wordTrace_append hprefix tailTrace_2644389
  have hstable : (prefixWord ++ tailWord_2644389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644389).length < 2 ^ (prefixWord ++ tailWord_2644389).sum := by decide
  have hdescent : baseEnd_2644389 < baseStart_2644389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644447 : List Nat := [1, 1, 2, 3, 3, 3, 1, 3, 5]
def baseStart_2644447 : Nat := 118140960795 + 2644447 * 2 ^ 59
def prefixEnd_2644447 : Nat := 4983230072969 + 3 ^ 40 * 2644447 * 2
def baseEnd_2644447 : Nat := 301749416964515627255759

theorem tailTrace_2644447 : CollatzResearch.WordTrace tailWord_2644447 prefixEnd_2644447 301749416964515627255759 := by
  unfold tailWord_2644447
  simp only [CollatzResearch.WordTrace]
  refine ⟨96450905850627629436163595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64300603900418419624109063 96450905850627629436163595)
  ·
    refine ⟨144676358775941444154245393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96450905850627629436163595 144676358775941444154245393)
    ·
      refine ⟨108507269081956083115684045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144676358775941444154245393 108507269081956083115684045)
      ·
        refine ⟨40690225905733531168381517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108507269081956083115684045 40690225905733531168381517)
        ·
          refine ⟨15258834714650074188143069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40690225905733531168381517 15258834714650074188143069)
          ·
            refine ⟨5722063017993777820553651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15258834714650074188143069 5722063017993777820553651)
            ·
              refine ⟨8583094526990666730830477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5722063017993777820553651 8583094526990666730830477)
              ·
                refine ⟨3218660447621500024061429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8583094526990666730830477 3218660447621500024061429)
                ·
                  refine ⟨301749416964515627255759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3218660447621500024061429 301749416964515627255759)
                  ·
                    rfl

theorem cell22_2644447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 5].length) (baseStart_2644447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2644447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2644447 prefixEnd_2644447 := by exact prefixLift 2644447
  have htrace : WordTrace (prefixWord ++ tailWord_2644447) baseStart_2644447 baseEnd_2644447 := by
    simpa [prefixWord, tailWord_2644447, baseEnd_2644447] using wordTrace_append hprefix tailTrace_2644447
  have hstable : (prefixWord ++ tailWord_2644447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644447).length < 2 ^ (prefixWord ++ tailWord_2644447).sum := by decide
  have hdescent : baseEnd_2644447 < baseStart_2644447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644505 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 3, 6]
def baseStart_2644505 : Nat := 118140960795 + 2644505 * 2 ^ 59
def prefixEnd_2644505 : Nat := 4983230072969 + 3 ^ 40 * 2644505 * 2
def baseEnd_2644505 : Nat := 905268105478854063817099

theorem tailTrace_2644505 : CollatzResearch.WordTrace tailWord_2644505 prefixEnd_2644505 905268105478854063817099 := by
  unfold tailWord_2644505
  simp only [CollatzResearch.WordTrace]
  refine ⟨96453021284417505341774969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64302014189611670227849979 96453021284417505341774969)
  ·
    refine ⟨72339765963313129006331227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96453021284417505341774969 72339765963313129006331227)
    ·
      refine ⟨108509648944969693509496841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72339765963313129006331227 108509648944969693509496841)
      ·
        refine ⟨81382236708727270132122631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108509648944969693509496841 81382236708727270132122631)
        ·
          refine ⟨122073355063090905198183947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81382236708727270132122631 122073355063090905198183947)
          ·
            refine ⟨183110032594636357797275921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122073355063090905198183947 183110032594636357797275921)
            ·
              refine ⟨137332524445977268347956941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183110032594636357797275921 137332524445977268347956941)
              ·
                refine ⟨51499696667241475630483853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137332524445977268347956941 51499696667241475630483853)
                ·
                  refine ⟨19312386250215553361431445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51499696667241475630483853 19312386250215553361431445)
                  ·
                    refine ⟨905268105478854063817099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19312386250215553361431445 905268105478854063817099)
                    ·
                      rfl

theorem cell22_2644505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 6].length) (baseStart_2644505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2644505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2644505 prefixEnd_2644505 := by exact prefixLift 2644505
  have htrace : WordTrace (prefixWord ++ tailWord_2644505) baseStart_2644505 baseEnd_2644505 := by
    simpa [prefixWord, tailWord_2644505, baseEnd_2644505] using wordTrace_append hprefix tailTrace_2644505
  have hstable : (prefixWord ++ tailWord_2644505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644505).length < 2 ^ (prefixWord ++ tailWord_2644505).sum := by decide
  have hdescent : baseEnd_2644505 < baseStart_2644505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644541 : List Nat := [1, 4, 1, 3, 2, 1, 3, 2, 2, 3]
def baseStart_2644541 : Nat := 118140960795 + 2644541 * 2 ^ 59
def prefixEnd_2644541 : Nat := 4983230072969 + 3 ^ 40 * 2644541 * 2
def baseEnd_2644541 : Nat := 905280429014561969916989

theorem tailTrace_2644541 : CollatzResearch.WordTrace tailWord_2644541 prefixEnd_2644541 905280429014561969916989 := by
  unfold tailWord_2644541
  simp only [CollatzResearch.WordTrace]
  refine ⟨96454334312287083490085477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64302889541524722326723651 96454334312287083490085477)
  ·
    refine ⟨18085187683553828154391027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96454334312287083490085477 18085187683553828154391027)
    ·
      refine ⟨27127781525330742231586541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18085187683553828154391027 27127781525330742231586541)
      ·
        refine ⟨10172918071999028336844953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27127781525330742231586541 10172918071999028336844953)
        ·
          refine ⟨7629688553999271252633715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10172918071999028336844953 7629688553999271252633715)
          ·
            refine ⟨11444532830998906878950573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7629688553999271252633715 11444532830998906878950573)
            ·
              refine ⟨4291699811624590079606465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11444532830998906878950573 4291699811624590079606465)
              ·
                refine ⟨3218774858718442559704849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4291699811624590079606465 3218774858718442559704849)
                ·
                  refine ⟨2414081144038831919778637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3218774858718442559704849 2414081144038831919778637)
                  ·
                    refine ⟨905280429014561969916989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2414081144038831919778637 905280429014561969916989)
                    ·
                      rfl

theorem cell22_2644541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_2644541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2644541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2644541 prefixEnd_2644541 := by exact prefixLift 2644541
  have htrace : WordTrace (prefixWord ++ tailWord_2644541) baseStart_2644541 baseEnd_2644541 := by
    simpa [prefixWord, tailWord_2644541, baseEnd_2644541] using wordTrace_append hprefix tailTrace_2644541
  have hstable : (prefixWord ++ tailWord_2644541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644541).length < 2 ^ (prefixWord ++ tailWord_2644541).sum := by decide
  have hdescent : baseEnd_2644541 < baseStart_2644541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644676 : List Nat := [2, 3, 3, 1, 1, 3, 2, 1, 1, 5]
def baseStart_2644676 : Nat := 118140960795 + 2644676 * 2 ^ 59
def prefixEnd_2644676 : Nat := 4983230072969 + 3 ^ 40 * 2644676 * 2
def baseEnd_2644676 : Nat := 905326642273466617791575

theorem tailTrace_2644676 : CollatzResearch.WordTrace tailWord_2644676 prefixEnd_2644676 905326642273466617791575 := by
  unfold tailWord_2644676
  simp only [CollatzResearch.WordTrace]
  refine ⟨48229629083399000773124941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64306172111198667697499921 48229629083399000773124941)
  ·
    refine ⟨18086110906274625289921853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48229629083399000773124941 18086110906274625289921853)
    ·
      refine ⟨6782291589852984483720695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18086110906274625289921853 6782291589852984483720695)
      ·
        refine ⟨10173437384779476725581043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6782291589852984483720695 10173437384779476725581043)
        ·
          refine ⟨15260156077169215088371565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10173437384779476725581043 15260156077169215088371565)
          ·
            refine ⟨5722558528938455658139337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15260156077169215088371565 5722558528938455658139337)
            ·
              refine ⟨4291918896703841743604503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5722558528938455658139337 4291918896703841743604503)
              ·
                refine ⟨6437878345055762615406755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4291918896703841743604503 6437878345055762615406755)
                ·
                  refine ⟨9656817517583643923110133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6437878345055762615406755 9656817517583643923110133)
                  ·
                    refine ⟨905326642273466617791575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9656817517583643923110133 905326642273466617791575)
                    ·
                      rfl

theorem cell22_2644676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_2644676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2644676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2644676 prefixEnd_2644676 := by exact prefixLift 2644676
  have htrace : WordTrace (prefixWord ++ tailWord_2644676) baseStart_2644676 baseEnd_2644676 := by
    simpa [prefixWord, tailWord_2644676, baseEnd_2644676] using wordTrace_append hprefix tailTrace_2644676
  have hstable : (prefixWord ++ tailWord_2644676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644676).length < 2 ^ (prefixWord ++ tailWord_2644676).sum := by decide
  have hdescent : baseEnd_2644676 < baseStart_2644676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644689 : List Nat := [1, 2, 2, 1, 2, 3, 5, 6]
def baseStart_2644689 : Nat := 118140960795 + 2644689 * 2 ^ 59
def prefixEnd_2644689 : Nat := 4983230072969 + 3 ^ 40 * 2644689 * 2
def baseEnd_2644689 : Nat := 100592343604348768579615

theorem tailTrace_2644689 : CollatzResearch.WordTrace tailWord_2644689 prefixEnd_2644689 100592343604348768579615 := by
  unfold tailWord_2644689
  simp only [CollatzResearch.WordTrace]
  refine ⟨96459732315750904766473121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64306488210500603177648747 96459732315750904766473121)
  ·
    refine ⟨72344799236813178574854841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96459732315750904766473121 72344799236813178574854841)
    ·
      refine ⟨54258599427609883931141131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72344799236813178574854841 54258599427609883931141131)
      ·
        refine ⟨81387899141414825896711697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54258599427609883931141131 81387899141414825896711697)
        ·
          refine ⟨61040924356061119422533773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81387899141414825896711697 61040924356061119422533773)
          ·
            refine ⟨22890346633522919783450165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61040924356061119422533773 22890346633522919783450165)
            ·
              refine ⟨2145969996892773729698453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22890346633522919783450165 2145969996892773729698453)
              ·
                refine ⟨100592343604348768579615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2145969996892773729698453 100592343604348768579615)
                ·
                  rfl

theorem cell22_2644689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 6].length) (baseStart_2644689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2644689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2644689 prefixEnd_2644689 := by exact prefixLift 2644689
  have htrace : WordTrace (prefixWord ++ tailWord_2644689) baseStart_2644689 baseEnd_2644689 := by
    simpa [prefixWord, tailWord_2644689, baseEnd_2644689] using wordTrace_append hprefix tailTrace_2644689
  have hstable : (prefixWord ++ tailWord_2644689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644689).length < 2 ^ (prefixWord ++ tailWord_2644689).sum := by decide
  have hdescent : baseEnd_2644689 < baseStart_2644689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644704 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 7, 3]
def baseStart_2644704 : Nat := 118140960795 + 2644704 * 2 ^ 59
def prefixEnd_2644704 : Nat := 4983230072969 + 3 ^ 40 * 2644704 * 2
def baseEnd_2644704 : Nat := 905336227245683878091489

theorem tailTrace_2644704 : CollatzResearch.WordTrace tailWord_2644704 prefixEnd_2644704 905336227245683878091489 := by
  unfold tailWord_2644704
  simp only [CollatzResearch.WordTrace]
  refine ⟨48230139705348281164134583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64306852940464374885512777 48230139705348281164134583)
  ·
    refine ⟨72345209558022421746201875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48230139705348281164134583 72345209558022421746201875)
    ·
      refine ⟨108517814337033632619302813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72345209558022421746201875 108517814337033632619302813)
      ·
        refine ⟨40694180376387612232238555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108517814337033632619302813 40694180376387612232238555)
        ·
          refine ⟨61041270564581418348357833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40694180376387612232238555 61041270564581418348357833)
          ·
            refine ⟨45780952923436063761268375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61041270564581418348357833 45780952923436063761268375)
            ·
              refine ⟨68671429385154095641902563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45780952923436063761268375 68671429385154095641902563)
              ·
                refine ⟨103007144077731143462853845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68671429385154095641902563 103007144077731143462853845)
                ·
                  refine ⟨2414229939321823674910637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 103007144077731143462853845 2414229939321823674910637)
                  ·
                    refine ⟨905336227245683878091489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2414229939321823674910637 905336227245683878091489)
                    ·
                      rfl

theorem cell22_2644704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 7, 3].length) (baseStart_2644704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2644704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2644704 prefixEnd_2644704 := by exact prefixLift 2644704
  have htrace : WordTrace (prefixWord ++ tailWord_2644704) baseStart_2644704 baseEnd_2644704 := by
    simpa [prefixWord, tailWord_2644704, baseEnd_2644704] using wordTrace_append hprefix tailTrace_2644704
  have hstable : (prefixWord ++ tailWord_2644704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644704).length < 2 ^ (prefixWord ++ tailWord_2644704).sum := by decide
  have hdescent : baseEnd_2644704 < baseStart_2644704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644721 : List Nat := [1, 2, 2, 2, 2, 2, 4, 1, 3, 3]
def baseStart_2644721 : Nat := 118140960795 + 2644721 * 2 ^ 59
def prefixEnd_2644721 : Nat := 4983230072969 + 3 ^ 40 * 2644721 * 2
def baseEnd_2644721 : Nat := 905342046693101500416437

theorem tailTrace_2644721 : CollatzResearch.WordTrace tailWord_2644721 prefixEnd_2644721 905342046693101500416437 := by
  unfold tailWord_2644721
  simp only [CollatzResearch.WordTrace]
  refine ⟨96460899451634974231638017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64307266301089982821092011 96460899451634974231638017)
  ·
    refine ⟨72345674588726230673728513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96460899451634974231638017 72345674588726230673728513)
    ·
      refine ⟨54259255941544673005296385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72345674588726230673728513 54259255941544673005296385)
      ·
        refine ⟨40694441956158504753972289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54259255941544673005296385 40694441956158504753972289)
        ·
          refine ⟨30520831467118878565479217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40694441956158504753972289 30520831467118878565479217)
          ·
            refine ⟨22890623600339158924109413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30520831467118878565479217 22890623600339158924109413)
            ·
              refine ⟨4291991925063592298270515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22890623600339158924109413 4291991925063592298270515)
              ·
                refine ⟨6437987887595388447405773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4291991925063592298270515 6437987887595388447405773)
                ·
                  refine ⟨2414245457848270667777165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6437987887595388447405773 2414245457848270667777165)
                  ·
                    refine ⟨905342046693101500416437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2414245457848270667777165 905342046693101500416437)
                    ·
                      rfl

theorem cell22_2644721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3, 3].length) (baseStart_2644721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2644721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2644721 prefixEnd_2644721 := by exact prefixLift 2644721
  have htrace : WordTrace (prefixWord ++ tailWord_2644721) baseStart_2644721 baseEnd_2644721 := by
    simpa [prefixWord, tailWord_2644721, baseEnd_2644721] using wordTrace_append hprefix tailTrace_2644721
  have hstable : (prefixWord ++ tailWord_2644721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644721).length < 2 ^ (prefixWord ++ tailWord_2644721).sum := by decide
  have hdescent : baseEnd_2644721 < baseStart_2644721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644738 : List Nat := [3, 4, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_2644738 : Nat := 118140960795 + 2644738 * 2 ^ 59
def prefixEnd_2644738 : Nat := 4983230072969 + 3 ^ 40 * 2644738 * 2
def baseEnd_2644738 : Nat := 905347866140519122741385

theorem tailTrace_2644738 : CollatzResearch.WordTrace tailWord_2644738 prefixEnd_2644738 905347866140519122741385 := by
  unfold tailWord_2644738
  simp only [CollatzResearch.WordTrace]
  refine ⟨24115379873143346533751717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64307679661715590756671245 24115379873143346533751717)
  ·
    refine ⟨4521633726214377475078447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24115379873143346533751717 4521633726214377475078447)
    ·
      refine ⟨6782450589321566212617671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4521633726214377475078447 6782450589321566212617671)
      ·
        refine ⟨10173675883982349318926507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6782450589321566212617671 10173675883982349318926507)
        ·
          refine ⟨15260513825973523978389761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10173675883982349318926507 15260513825973523978389761)
          ·
            refine ⟨11445385369480142983792321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15260513825973523978389761 11445385369480142983792321)
            ·
              refine ⟨8584039027110107237844241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11445385369480142983792321 8584039027110107237844241)
              ·
                refine ⟨6438029270332580428383181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8584039027110107237844241 6438029270332580428383181)
                ·
                  refine ⟨2414260976374717660643693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6438029270332580428383181 2414260976374717660643693)
                  ·
                    refine ⟨905347866140519122741385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2414260976374717660643693 905347866140519122741385)
                    ·
                      rfl

theorem cell22_2644738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_2644738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2644738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2644738 prefixEnd_2644738 := by exact prefixLift 2644738
  have htrace : WordTrace (prefixWord ++ tailWord_2644738) baseStart_2644738 baseEnd_2644738 := by
    simpa [prefixWord, tailWord_2644738, baseEnd_2644738] using wordTrace_append hprefix tailTrace_2644738
  have hstable : (prefixWord ++ tailWord_2644738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644738).length < 2 ^ (prefixWord ++ tailWord_2644738).sum := by decide
  have hdescent : baseEnd_2644738 < baseStart_2644738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644772 : List Nat := [2, 3, 1, 3, 3, 1, 3, 2, 1, 3]
def baseStart_2644772 : Nat := 118140960795 + 2644772 * 2 ^ 59
def prefixEnd_2644772 : Nat := 4983230072969 + 3 ^ 40 * 2644772 * 2
def baseEnd_2644772 : Nat := 905359505035354367391281

theorem tailTrace_2644772 : CollatzResearch.WordTrace tailWord_2644772 prefixEnd_2644772 905359505035354367391281 := by
  unfold tailWord_2644772
  simp only [CollatzResearch.WordTrace]
  refine ⟨48231379787225104970872285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64308506382966806627829713 48231379787225104970872285)
  ·
    refine ⟨18086767420209414364077107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48231379787225104970872285 18086767420209414364077107)
    ·
      refine ⟨27130151130314121546115661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18086767420209414364077107 27130151130314121546115661)
      ·
        refine ⟨10173806673867795579793373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27130151130314121546115661 10173806673867795579793373)
        ·
          refine ⟨3815177502700423342422515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10173806673867795579793373 3815177502700423342422515)
          ·
            refine ⟨5722766254050635013633773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3815177502700423342422515 5722766254050635013633773)
            ·
              refine ⟨2146037345268988130112665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5722766254050635013633773 2146037345268988130112665)
              ·
                refine ⟨1609528008951741097584499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2146037345268988130112665 1609528008951741097584499)
                ·
                  refine ⟨2414292013427611646376749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1609528008951741097584499 2414292013427611646376749)
                  ·
                    refine ⟨905359505035354367391281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2414292013427611646376749 905359505035354367391281)
                    ·
                      rfl

theorem cell22_2644772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_2644772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2644772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2644772 prefixEnd_2644772 := by exact prefixLift 2644772
  have htrace : WordTrace (prefixWord ++ tailWord_2644772) baseStart_2644772 baseEnd_2644772 := by
    simpa [prefixWord, tailWord_2644772, baseEnd_2644772] using wordTrace_append hprefix tailTrace_2644772
  have hstable : (prefixWord ++ tailWord_2644772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644772).length < 2 ^ (prefixWord ++ tailWord_2644772).sum := by decide
  have hdescent : baseEnd_2644772 < baseStart_2644772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644798 : List Nat := [4, 2, 1, 2, 3, 1, 1, 1, 3, 4]
def baseStart_2644798 : Nat := 118140960795 + 2644798 * 2 ^ 59
def prefixEnd_2644798 : Nat := 4983230072969 + 3 ^ 40 * 2644798 * 2
def baseEnd_2644798 : Nat := 905368405366698966241201

theorem tailTrace_2644798 : CollatzResearch.WordTrace tailWord_2644798 prefixEnd_2644798 905368405366698966241201 := by
  unfold tailWord_2644798
  simp only [CollatzResearch.WordTrace]
  refine ⟨12057963484044502047773881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64309138581570677588127365 12057963484044502047773881)
  ·
    refine ⟨9043472613033376535830411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12057963484044502047773881 9043472613033376535830411)
    ·
      refine ⟨13565208919550064803745617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9043472613033376535830411 13565208919550064803745617)
      ·
        refine ⟨10173906689662548602809213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13565208919550064803745617 10173906689662548602809213)
        ·
          refine ⟨3815215008623455726053455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10173906689662548602809213 3815215008623455726053455)
          ·
            refine ⟨5722822512935183589080183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3815215008623455726053455 5722822512935183589080183)
            ·
              refine ⟨8584233769402775383620275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5722822512935183589080183 8584233769402775383620275)
              ·
                refine ⟨12876350654104163075430413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8584233769402775383620275 12876350654104163075430413)
                ·
                  refine ⟨4828631495289061153286405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12876350654104163075430413 4828631495289061153286405)
                  ·
                    refine ⟨905368405366698966241201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4828631495289061153286405 905368405366698966241201)
                    ·
                      rfl

theorem cell22_2644798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_2644798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2644798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2644798 prefixEnd_2644798 := by exact prefixLift 2644798
  have htrace : WordTrace (prefixWord ++ tailWord_2644798) baseStart_2644798 baseEnd_2644798 := by
    simpa [prefixWord, tailWord_2644798, baseEnd_2644798] using wordTrace_append hprefix tailTrace_2644798
  have hstable : (prefixWord ++ tailWord_2644798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644798).length < 2 ^ (prefixWord ++ tailWord_2644798).sum := by decide
  have hdescent : baseEnd_2644798 < baseStart_2644798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644826 : List Nat := [3, 1, 1, 2, 1, 4, 2, 2, 2, 4]
def baseStart_2644826 : Nat := 118140960795 + 2644826 * 2 ^ 59
def prefixEnd_2644826 : Nat := 4983230072969 + 3 ^ 40 * 2644826 * 2
def baseEnd_2644826 : Nat := 905377990338916226541115

theorem tailTrace_2644826 : CollatzResearch.WordTrace tailWord_2644826 prefixEnd_2644826 905377990338916226541115 := by
  unfold tailWord_2644826
  simp only [CollatzResearch.WordTrace]
  refine ⟨24116182279063644291052583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64309819410836384776140221 24116182279063644291052583)
  ·
    refine ⟨36174273418595466436578875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24116182279063644291052583 36174273418595466436578875)
    ·
      refine ⟨54261410127893199654868313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36174273418595466436578875 54261410127893199654868313)
      ·
        refine ⟨40696057595919899741151235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54261410127893199654868313 40696057595919899741151235)
        ·
          refine ⟨61044086393879849611726853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40696057595919899741151235 61044086393879849611726853)
          ·
            refine ⟨11445766198852471802198785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61044086393879849611726853 11445766198852471802198785)
            ·
              refine ⟨8584324649139353851649089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11445766198852471802198785 8584324649139353851649089)
              ·
                refine ⟨6438243486854515388736817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8584324649139353851649089 6438243486854515388736817)
                ·
                  refine ⟨4828682615140886541552613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6438243486854515388736817 4828682615140886541552613)
                  ·
                    refine ⟨905377990338916226541115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4828682615140886541552613 905377990338916226541115)
                    ·
                      rfl

theorem cell22_2644826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_2644826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2644826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2644826 prefixEnd_2644826 := by exact prefixLift 2644826
  have htrace : WordTrace (prefixWord ++ tailWord_2644826) baseStart_2644826 baseEnd_2644826 := by
    simpa [prefixWord, tailWord_2644826, baseEnd_2644826] using wordTrace_append hprefix tailTrace_2644826
  have hstable : (prefixWord ++ tailWord_2644826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644826).length < 2 ^ (prefixWord ++ tailWord_2644826).sum := by decide
  have hdescent : baseEnd_2644826 < baseStart_2644826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644866 : List Nat := [3, 4, 2, 2, 2, 1, 2, 1, 1, 4]
def baseStart_2644866 : Nat := 118140960795 + 2644866 * 2 ^ 59
def prefixEnd_2644866 : Nat := 4983230072969 + 3 ^ 40 * 2644866 * 2
def baseEnd_2644866 : Nat := 905391683156369455540993

theorem tailTrace_2644866 : CollatzResearch.WordTrace tailWord_2644866 prefixEnd_2644866 905391683156369455540993 := by
  unfold tailWord_2644866
  simp only [CollatzResearch.WordTrace]
  refine ⟨24116547009027415998916613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64310792024073109330444301 24116547009027415998916613)
  ·
    refine ⟨4521852564192640499796865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24116547009027415998916613 4521852564192640499796865)
    ·
      refine ⟨3391389423144480374847649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4521852564192640499796865 3391389423144480374847649)
      ·
        refine ⟨2543542067358360281135737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3391389423144480374847649 2543542067358360281135737)
        ·
          refine ⟨1907656550518770210851803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2543542067358360281135737 1907656550518770210851803)
          ·
            refine ⟨2861484825778155316277705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1907656550518770210851803 2861484825778155316277705)
            ·
              refine ⟨2146113619333616487208279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2861484825778155316277705 2146113619333616487208279)
              ·
                refine ⟨3219170429000424730812419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2146113619333616487208279 3219170429000424730812419)
                ·
                  refine ⟨4828755643500637096218629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3219170429000424730812419 4828755643500637096218629)
                  ·
                    refine ⟨905391683156369455540993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4828755643500637096218629 905391683156369455540993)
                    ·
                      rfl

theorem cell22_2644866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_2644866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2644866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2644866 prefixEnd_2644866 := by exact prefixLift 2644866
  have htrace : WordTrace (prefixWord ++ tailWord_2644866) baseStart_2644866 baseEnd_2644866 := by
    simpa [prefixWord, tailWord_2644866, baseEnd_2644866] using wordTrace_append hprefix tailTrace_2644866
  have hstable : (prefixWord ++ tailWord_2644866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644866).length < 2 ^ (prefixWord ++ tailWord_2644866).sum := by decide
  have hdescent : baseEnd_2644866 < baseStart_2644866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644890 : List Nat := [3, 1, 1, 4, 3, 1, 2, 1, 3, 3]
def baseStart_2644890 : Nat := 118140960795 + 2644890 * 2 ^ 59
def prefixEnd_2644890 : Nat := 4983230072969 + 3 ^ 40 * 2644890 * 2
def baseEnd_2644890 : Nat := 905399898846841392940919

theorem tailTrace_2644890 : CollatzResearch.WordTrace tailWord_2644890 prefixEnd_2644890 905399898846841392940919 := by
  unfold tailWord_2644890
  simp only [CollatzResearch.WordTrace]
  refine ⟨24116765847005679023635031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64311375592015144063026749 24116765847005679023635031)
  ·
    refine ⟨36175148770508518535452547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24116765847005679023635031 36175148770508518535452547)
    ·
      refine ⟨54262723155762777803178821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36175148770508518535452547 54262723155762777803178821)
      ·
        refine ⟨10174260591705520838096029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54262723155762777803178821 10174260591705520838096029)
        ·
          refine ⟨3815347721889570314286011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10174260591705520838096029 3815347721889570314286011)
          ·
            refine ⟨5723021582834355471429017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3815347721889570314286011 5723021582834355471429017)
            ·
              refine ⟨4292266187125766603571763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5723021582834355471429017 4292266187125766603571763)
              ·
                refine ⟨6438399280688649905357645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4292266187125766603571763 6438399280688649905357645)
                ·
                  refine ⟨2414399730258243714509117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6438399280688649905357645 2414399730258243714509117)
                  ·
                    refine ⟨905399898846841392940919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2414399730258243714509117 905399898846841392940919)
                    ·
                      rfl

theorem cell22_2644890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 3, 3].length) (baseStart_2644890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2644890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2644890 prefixEnd_2644890 := by exact prefixLift 2644890
  have htrace : WordTrace (prefixWord ++ tailWord_2644890) baseStart_2644890 baseEnd_2644890 := by
    simpa [prefixWord, tailWord_2644890, baseEnd_2644890] using wordTrace_append hprefix tailTrace_2644890
  have hstable : (prefixWord ++ tailWord_2644890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644890).length < 2 ^ (prefixWord ++ tailWord_2644890).sum := by decide
  have hdescent : baseEnd_2644890 < baseStart_2644890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644941 : List Nat := [1, 6, 3, 1, 1, 2, 1, 1, 3, 3]
def baseStart_2644941 : Nat := 118140960795 + 2644941 * 2 ^ 59
def prefixEnd_2644941 : Nat := 4983230072969 + 3 ^ 40 * 2644941 * 2
def baseEnd_2644941 : Nat := 905417357189094259915763

theorem tailTrace_2644941 : CollatzResearch.WordTrace tailWord_2644941 prefixEnd_2644941 905417357189094259915763 := by
  unfold tailWord_2644941
  simp only [CollatzResearch.WordTrace]
  refine ⟨96468923510837951804646677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64312615673891967869764451 96468923510837951804646677)
  ·
    refine ⟨4521980789570528990842813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 96468923510837951804646677 4521980789570528990842813)
    ·
      refine ⟨1695742796088948371566055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4521980789570528990842813 1695742796088948371566055)
      ·
        refine ⟨2543614194133422557349083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1695742796088948371566055 2543614194133422557349083)
        ·
          refine ⟨3815421291200133836023625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2543614194133422557349083 3815421291200133836023625)
          ·
            refine ⟨2861565968400100377017719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3815421291200133836023625 2861565968400100377017719)
            ·
              refine ⟨4292348952600150565526579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2861565968400100377017719 4292348952600150565526579)
              ·
                refine ⟨6438523428900225848289869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4292348952600150565526579 6438523428900225848289869)
                ·
                  refine ⟨2414446285837584693108701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6438523428900225848289869 2414446285837584693108701)
                  ·
                    refine ⟨905417357189094259915763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2414446285837584693108701 905417357189094259915763)
                    ·
                      rfl

theorem cell22_2644941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_2644941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2644941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2644941 prefixEnd_2644941 := by exact prefixLift 2644941
  have htrace : WordTrace (prefixWord ++ tailWord_2644941) baseStart_2644941 baseEnd_2644941 := by
    simpa [prefixWord, tailWord_2644941, baseEnd_2644941] using wordTrace_append hprefix tailTrace_2644941
  have hstable : (prefixWord ++ tailWord_2644941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644941).length < 2 ^ (prefixWord ++ tailWord_2644941).sum := by decide
  have hdescent : baseEnd_2644941 < baseStart_2644941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644948 : List Nat := [2, 4, 1, 2, 1, 2, 3, 1, 6]
def baseStart_2644948 : Nat := 118140960795 + 2644948 * 2 ^ 59
def prefixEnd_2644948 : Nat := 4983230072969 + 3 ^ 40 * 2644948 * 2
def baseEnd_2644948 : Nat := 301806584477382858330247

theorem tailTrace_2644948 : CollatzResearch.WordTrace tailWord_2644948 prefixEnd_2644948 301806584477382858330247 := by
  unfold tailWord_2644948
  simp only [CollatzResearch.WordTrace]
  refine ⟨48234589410906296000075749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64312785881208394666767665 48234589410906296000075749)
  ·
    refine ⟨9043985514544930500014203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48234589410906296000075749 9043985514544930500014203)
    ·
      refine ⟨13565978271817395750021305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9043985514544930500014203 13565978271817395750021305)
      ·
        refine ⟨10174483703863046812515979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13565978271817395750021305 10174483703863046812515979)
        ·
          refine ⟨15261725555794570218773969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10174483703863046812515979 15261725555794570218773969)
          ·
            refine ⟨11446294166845927664080477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15261725555794570218773969 11446294166845927664080477)
            ·
              refine ⟨4292360312567222874030179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11446294166845927664080477 4292360312567222874030179)
              ·
                refine ⟨6438540468850834311045269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4292360312567222874030179 6438540468850834311045269)
                ·
                  refine ⟨301806584477382858330247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6438540468850834311045269 301806584477382858330247)
                  ·
                    rfl

theorem cell22_2644948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_2644948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2644948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2644948 prefixEnd_2644948 := by exact prefixLift 2644948
  have htrace : WordTrace (prefixWord ++ tailWord_2644948) baseStart_2644948 baseEnd_2644948 := by
    simpa [prefixWord, tailWord_2644948, baseEnd_2644948] using wordTrace_append hprefix tailTrace_2644948
  have hstable : (prefixWord ++ tailWord_2644948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644948).length < 2 ^ (prefixWord ++ tailWord_2644948).sum := by decide
  have hdescent : baseEnd_2644948 < baseStart_2644948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644961 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 6, 4]
def baseStart_2644961 : Nat := 118140960795 + 2644961 * 2 ^ 59
def prefixEnd_2644961 : Nat := 4983230072969 + 3 ^ 40 * 2644961 * 2
def baseEnd_2644961 : Nat := 905424203597820874415701

theorem tailTrace_2644961 : CollatzResearch.WordTrace tailWord_2644961 prefixEnd_2644961 905424203597820874415701 := by
  unfold tailWord_2644961
  simp only [CollatzResearch.WordTrace]
  refine ⟨96469652970765495220374737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64313101980510330146916491 96469652970765495220374737)
  ·
    refine ⟨72352239728074121415281053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96469652970765495220374737 72352239728074121415281053)
    ·
      refine ⟨27132089898027795530730395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72352239728074121415281053 27132089898027795530730395)
      ·
        refine ⟨40698134847041693296095593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27132089898027795530730395 40698134847041693296095593)
        ·
          refine ⟨30523601135281269972071695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40698134847041693296095593 30523601135281269972071695)
          ·
            refine ⟨45785401702921904958107543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30523601135281269972071695 45785401702921904958107543)
            ·
              refine ⟨68678102554382857437161315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45785401702921904958107543 68678102554382857437161315)
              ·
                refine ⟨103017153831574286155741973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68678102554382857437161315 103017153831574286155741973)
                ·
                  refine ⟨4828929085855044663550405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103017153831574286155741973 4828929085855044663550405)
                  ·
                    refine ⟨905424203597820874415701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4828929085855044663550405 905424203597820874415701)
                    ·
                      rfl

theorem cell22_2644961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_2644961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2644961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2644961 prefixEnd_2644961 := by exact prefixLift 2644961
  have htrace : WordTrace (prefixWord ++ tailWord_2644961) baseStart_2644961 baseEnd_2644961 := by
    simpa [prefixWord, tailWord_2644961, baseEnd_2644961] using wordTrace_append hprefix tailTrace_2644961
  have hstable : (prefixWord ++ tailWord_2644961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644961).length < 2 ^ (prefixWord ++ tailWord_2644961).sum := by decide
  have hdescent : baseEnd_2644961 < baseStart_2644961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645025 : List Nat := [1, 2, 3, 2, 3, 2, 1, 2, 3, 3]
def baseStart_2645025 : Nat := 118140960795 + 2645025 * 2 ^ 59
def prefixEnd_2645025 : Nat := 4983230072969 + 3 ^ 40 * 2645025 * 2
def baseEnd_2645025 : Nat := 905446112105746040815505

theorem tailTrace_2645025 : CollatzResearch.WordTrace tailWord_2645025 prefixEnd_2645025 905446112105746040815505 := by
  unfold tailWord_2645025
  simp only [CollatzResearch.WordTrace]
  refine ⟨96471987242533634150704529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64314658161689089433803019 96471987242533634150704529)
  ·
    refine ⟨72353990431900225613028397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96471987242533634150704529 72353990431900225613028397)
    ·
      refine ⟨27132746411962584604885649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72353990431900225613028397 27132746411962584604885649)
      ·
        refine ⟨20349559808971938453664237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27132746411962584604885649 20349559808971938453664237)
        ·
          refine ⟨7631084928364476920124089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20349559808971938453664237 7631084928364476920124089)
          ·
            refine ⟨5723313696273357690093067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7631084928364476920124089 5723313696273357690093067)
            ·
              refine ⟨8584970544410036535139601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5723313696273357690093067 8584970544410036535139601)
              ·
                refine ⟨6438727908307527401354701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8584970544410036535139601 6438727908307527401354701)
                ·
                  refine ⟨2414522965615322775508013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6438727908307527401354701 2414522965615322775508013)
                  ·
                    refine ⟨905446112105746040815505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2414522965615322775508013 905446112105746040815505)
                    ·
                      rfl

theorem cell22_2645025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_2645025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645025 prefixEnd_2645025 := by exact prefixLift 2645025
  have htrace : WordTrace (prefixWord ++ tailWord_2645025) baseStart_2645025 baseEnd_2645025 := by
    simpa [prefixWord, tailWord_2645025, baseEnd_2645025] using wordTrace_append hprefix tailTrace_2645025
  have hstable : (prefixWord ++ tailWord_2645025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645025).length < 2 ^ (prefixWord ++ tailWord_2645025).sum := by decide
  have hdescent : baseEnd_2645025 < baseStart_2645025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645036 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 1, 7]
def baseStart_2645036 : Nat := 118140960795 + 2645036 * 2 ^ 59
def prefixEnd_2645036 : Nat := 4983230072969 + 3 ^ 40 * 2645036 * 2
def baseEnd_2645036 : Nat := 905449877630545678790471

theorem tailTrace_2645036 : CollatzResearch.WordTrace tailWord_2645036 prefixEnd_2645036 905449877630545678790471 := by
  unfold tailWord_2645036
  simp only [CollatzResearch.WordTrace]
  refine ⟨48236194222746891514677481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64314925630329188686236641 48236194222746891514677481)
  ·
    refine ⟨36177145667060168636008111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48236194222746891514677481 36177145667060168636008111)
    ·
      refine ⟨54265718500590252954012167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36177145667060168636008111 54265718500590252954012167)
      ·
        refine ⟨81398577750885379431018251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54265718500590252954012167 81398577750885379431018251)
        ·
          refine ⟨122097866626328069146527377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81398577750885379431018251 122097866626328069146527377)
          ·
            refine ⟨91573399969746051859895533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122097866626328069146527377 91573399969746051859895533)
            ·
              refine ⟨34340024988654769447460825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91573399969746051859895533 34340024988654769447460825)
              ·
                refine ⟨25755018741491077085595619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34340024988654769447460825 25755018741491077085595619)
                ·
                  refine ⟨38632528112236615628393429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25755018741491077085595619 38632528112236615628393429)
                  ·
                    refine ⟨905449877630545678790471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38632528112236615628393429 905449877630545678790471)
                    ·
                      rfl

theorem cell22_2645036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_2645036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645036 prefixEnd_2645036 := by exact prefixLift 2645036
  have htrace : WordTrace (prefixWord ++ tailWord_2645036) baseStart_2645036 baseEnd_2645036 := by
    simpa [prefixWord, tailWord_2645036, baseEnd_2645036] using wordTrace_append hprefix tailTrace_2645036
  have hstable : (prefixWord ++ tailWord_2645036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645036).length < 2 ^ (prefixWord ++ tailWord_2645036).sum := by decide
  have hdescent : baseEnd_2645036 < baseStart_2645036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645038 : List Nat := [4, 1, 3, 1, 1, 1, 2, 2, 7]
def baseStart_2645038 : Nat := 118140960795 + 2645038 * 2 ^ 59
def prefixEnd_2645038 : Nat := 4983230072969 + 3 ^ 40 * 2645038 * 2
def baseEnd_2645038 : Nat := 301816854090472780080155

theorem tailTrace_2645038 : CollatzResearch.WordTrace tailWord_2645038 prefixEnd_2645038 301816854090472780080155 := by
  unfold tailWord_2645038
  simp only [CollatzResearch.WordTrace]
  refine ⟨12059057673935817171365971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64314974260991024913951845 12059057673935817171365971)
  ·
    refine ⟨18088586510903725757048957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12059057673935817171365971 18088586510903725757048957)
    ·
      refine ⟨6783219941588897158893359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18088586510903725757048957 6783219941588897158893359)
      ·
        refine ⟨10174829912383345738340039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6783219941588897158893359 10174829912383345738340039)
        ·
          refine ⟨15262244868575018607510059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10174829912383345738340039 15262244868575018607510059)
          ·
            refine ⟨22893367302862527911265089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15262244868575018607510059 22893367302862527911265089)
            ·
              refine ⟨17170025477146895933448817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22893367302862527911265089 17170025477146895933448817)
              ·
                refine ⟨12877519107860171950086613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17170025477146895933448817 12877519107860171950086613)
                ·
                  refine ⟨301816854090472780080155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12877519107860171950086613 301816854090472780080155)
                  ·
                    rfl

theorem cell22_2645038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_2645038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645038 prefixEnd_2645038 := by exact prefixLift 2645038
  have htrace : WordTrace (prefixWord ++ tailWord_2645038) baseStart_2645038 baseEnd_2645038 := by
    simpa [prefixWord, tailWord_2645038, baseEnd_2645038] using wordTrace_append hprefix tailTrace_2645038
  have hstable : (prefixWord ++ tailWord_2645038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645038).length < 2 ^ (prefixWord ++ tailWord_2645038).sum := by decide
  have hdescent : baseEnd_2645038 < baseStart_2645038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645042 : List Nat := [3, 2, 1, 1, 2, 2, 4, 3, 1, 3]
def baseStart_2645042 : Nat := 118140960795 + 2645042 * 2 ^ 59
def prefixEnd_2645042 : Nat := 4983230072969 + 3 ^ 40 * 2645042 * 2
def baseEnd_2645042 : Nat := 905451931553163663140453

theorem tailTrace_2645042 : CollatzResearch.WordTrace tailWord_2645042 prefixEnd_2645042 905451931553163663140453 := by
  unfold tailWord_2645042
  simp only [CollatzResearch.WordTrace]
  refine ⟨24118151820868011513518345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64315071522314697369382253 24118151820868011513518345)
  ·
    refine ⟨18088613865651008635138759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24118151820868011513518345 18088613865651008635138759)
    ·
      refine ⟨27132920798476512952708139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18088613865651008635138759 27132920798476512952708139)
      ·
        refine ⟨40699381197714769429062209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27132920798476512952708139 40699381197714769429062209)
        ·
          refine ⟨30524535898286077071796657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40699381197714769429062209 30524535898286077071796657)
          ·
            refine ⟨22893401923714557803847493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30524535898286077071796657 22893401923714557803847493)
            ·
              refine ⟨4292512860696479588221405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22893401923714557803847493 4292512860696479588221405)
              ·
                refine ⟨1609692322761179845583027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4292512860696479588221405 1609692322761179845583027)
                ·
                  refine ⟨2414538484141769768374541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1609692322761179845583027 2414538484141769768374541)
                  ·
                    refine ⟨905451931553163663140453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2414538484141769768374541 905451931553163663140453)
                    ·
                      rfl

theorem cell22_2645042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_2645042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645042 prefixEnd_2645042 := by exact prefixLift 2645042
  have htrace : WordTrace (prefixWord ++ tailWord_2645042) baseStart_2645042 baseEnd_2645042 := by
    simpa [prefixWord, tailWord_2645042, baseEnd_2645042] using wordTrace_append hprefix tailTrace_2645042
  have hstable : (prefixWord ++ tailWord_2645042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645042).length < 2 ^ (prefixWord ++ tailWord_2645042).sum := by decide
  have hdescent : baseEnd_2645042 < baseStart_2645042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645053 : List Nat := [1, 4, 1, 3, 1, 2, 1, 2, 2, 5]
def baseStart_2645053 : Nat := 118140960795 + 2645053 * 2 ^ 59
def prefixEnd_2645053 : Nat := 4983230072969 + 3 ^ 40 * 2645053 * 2
def baseEnd_2645053 : Nat := 905455697077963301115419

theorem tailTrace_2645053 : CollatzResearch.WordTrace tailWord_2645053 prefixEnd_2645053 905455697077963301115419 := by
  unfold tailWord_2645053
  simp only [CollatzResearch.WordTrace]
  refine ⟨96473008486432194932723813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64315338990954796621815875 96473008486432194932723813)
  ·
    refine ⟨18088689091206036549885715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96473008486432194932723813 18088689091206036549885715)
    ·
      refine ⟨27133033636809054824828573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18088689091206036549885715 27133033636809054824828573)
      ·
        refine ⟨10174887613803395559310715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27133033636809054824828573 10174887613803395559310715)
        ·
          refine ⟨15262331420705093338966073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10174887613803395559310715 15262331420705093338966073)
          ·
            refine ⟨11446748565528820004224555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15262331420705093338966073 11446748565528820004224555)
            ·
              refine ⟨17170122848293230006336833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11446748565528820004224555 17170122848293230006336833)
              ·
                refine ⟨12877592136219922504752625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17170122848293230006336833 12877592136219922504752625)
                ·
                  refine ⟨9658194102164941878564469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12877592136219922504752625 9658194102164941878564469)
                  ·
                    refine ⟨905455697077963301115419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9658194102164941878564469 905455697077963301115419)
                    ·
                      rfl

theorem cell22_2645053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_2645053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645053 prefixEnd_2645053 := by exact prefixLift 2645053
  have htrace : WordTrace (prefixWord ++ tailWord_2645053) baseStart_2645053 baseEnd_2645053 := by
    simpa [prefixWord, tailWord_2645053, baseEnd_2645053] using wordTrace_append hprefix tailTrace_2645053
  have hstable : (prefixWord ++ tailWord_2645053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645053).length < 2 ^ (prefixWord ++ tailWord_2645053).sum := by decide
  have hdescent : baseEnd_2645053 < baseStart_2645053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645117 : List Nat := [1, 4, 1, 1, 3, 1, 5, 2, 4]
def baseStart_2645117 : Nat := 118140960795 + 2645117 * 2 ^ 59
def prefixEnd_2645117 : Nat := 4983230072969 + 3 ^ 40 * 2645117 * 2
def baseEnd_2645117 : Nat := 301825868528629489171741

theorem tailTrace_2645117 : CollatzResearch.WordTrace tailWord_2645117 prefixEnd_2645117 301825868528629489171741 := by
  unfold tailWord_2645117
  simp only [CollatzResearch.WordTrace]
  refine ⟨96475342758200333863053605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64316895172133555908702403 96475342758200333863053605)
  ·
    refine ⟨18089126767162562599322551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96475342758200333863053605 18089126767162562599322551)
    ·
      refine ⟨27133690150743843898983827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18089126767162562599322551 27133690150743843898983827)
      ·
        refine ⟨40700535226115765848475741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27133690150743843898983827 40700535226115765848475741)
        ·
          refine ⟨15262700709793412193178403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40700535226115765848475741 15262700709793412193178403)
          ·
            refine ⟨22894051064690118289767605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15262700709793412193178403 22894051064690118289767605)
            ·
              refine ⟨2146317287314698589665713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22894051064690118289767605 2146317287314698589665713)
              ·
                refine ⟨1609737965486023942249285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2146317287314698589665713 1609737965486023942249285)
                ·
                  refine ⟨301825868528629489171741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1609737965486023942249285 301825868528629489171741)
                  ·
                    rfl

theorem cell22_2645117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_2645117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645117 prefixEnd_2645117 := by exact prefixLift 2645117
  have htrace : WordTrace (prefixWord ++ tailWord_2645117) baseStart_2645117 baseEnd_2645117 := by
    simpa [prefixWord, tailWord_2645117, baseEnd_2645117] using wordTrace_append hprefix tailTrace_2645117
  have hstable : (prefixWord ++ tailWord_2645117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645117).length < 2 ^ (prefixWord ++ tailWord_2645117).sum := by decide
  have hdescent : baseEnd_2645117 < baseStart_2645117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645235 : List Nat := [1, 1, 1, 2, 2, 6, 2, 1, 6]
def baseStart_2645235 : Nat := 118140960795 + 2645235 * 2 ^ 59
def prefixEnd_2645235 : Nat := 4983230072969 + 3 ^ 40 * 2645235 * 2
def baseEnd_2645235 : Nat := 301839333132458497688287

theorem tailTrace_2645235 : CollatzResearch.WordTrace tailWord_2645235 prefixEnd_2645235 301839333132458497688287 := by
  unfold tailWord_2645235
  simp only [CollatzResearch.WordTrace]
  refine ⟨96479646571772840015849159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64319764381181893343899439 96479646571772840015849159)
  ·
    refine ⟨144719469857659260023773739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96479646571772840015849159 144719469857659260023773739)
    ·
      refine ⟨217079204786488890035660609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144719469857659260023773739 217079204786488890035660609)
      ·
        refine ⟨162809403589866667526745457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217079204786488890035660609 162809403589866667526745457)
        ·
          refine ⟨122107052692400000645059093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162809403589866667526745457 122107052692400000645059093)
          ·
            refine ⟨5723768094956250030237145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 122107052692400000645059093 5723768094956250030237145)
            ·
              refine ⟨4292826071217187522677859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5723768094956250030237145 4292826071217187522677859)
              ·
                refine ⟨6439239106825781284016789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4292826071217187522677859 6439239106825781284016789)
                ·
                  refine ⟨301839333132458497688287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6439239106825781284016789 301839333132458497688287)
                  ·
                    rfl

theorem cell22_2645235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 6].length) (baseStart_2645235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645235 prefixEnd_2645235 := by exact prefixLift 2645235
  have htrace : WordTrace (prefixWord ++ tailWord_2645235) baseStart_2645235 baseEnd_2645235 := by
    simpa [prefixWord, tailWord_2645235, baseEnd_2645235] using wordTrace_append hprefix tailTrace_2645235
  have hstable : (prefixWord ++ tailWord_2645235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645235).length < 2 ^ (prefixWord ++ tailWord_2645235).sum := by decide
  have hdescent : baseEnd_2645235 < baseStart_2645235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645265 : List Nat := [1, 2, 2, 1, 1, 4, 2, 3, 2, 4]
def baseStart_2645265 : Nat := 118140960795 + 2645265 * 2 ^ 59
def prefixEnd_2645265 : Nat := 4983230072969 + 3 ^ 40 * 2645265 * 2
def baseEnd_2645265 : Nat := 905528269010465414814769

theorem tailTrace_2645265 : CollatzResearch.WordTrace tailWord_2645265 prefixEnd_2645265 905528269010465414814769 := by
  unfold tailWord_2645265
  simp only [CollatzResearch.WordTrace]
  refine ⟨96480740761664155139441249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64320493841109436759627499 96480740761664155139441249)
  ·
    refine ⟨72360555571248116354580937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96480740761664155139441249 72360555571248116354580937)
    ·
      refine ⟨54270416678436087265935703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72360555571248116354580937 54270416678436087265935703)
      ·
        refine ⟨81405625017654130898903555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54270416678436087265935703 81405625017654130898903555)
        ·
          refine ⟨122108437526481196348355333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81405625017654130898903555 122108437526481196348355333)
          ·
            refine ⟨22895332036215224315316625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122108437526481196348355333 22895332036215224315316625)
            ·
              refine ⟨17171499027161418236487469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22895332036215224315316625 17171499027161418236487469)
              ·
                refine ⟨6439312135185531838682801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17171499027161418236487469 6439312135185531838682801)
                ·
                  refine ⟨4829484101389148879012101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6439312135185531838682801 4829484101389148879012101)
                  ·
                    refine ⟨905528269010465414814769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4829484101389148879012101 905528269010465414814769)
                    ·
                      rfl

theorem cell22_2645265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_2645265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645265 prefixEnd_2645265 := by exact prefixLift 2645265
  have htrace : WordTrace (prefixWord ++ tailWord_2645265) baseStart_2645265 baseEnd_2645265 := by
    simpa [prefixWord, tailWord_2645265, baseEnd_2645265] using wordTrace_append hprefix tailTrace_2645265
  have hstable : (prefixWord ++ tailWord_2645265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645265).length < 2 ^ (prefixWord ++ tailWord_2645265).sum := by decide
  have hdescent : baseEnd_2645265 < baseStart_2645265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645301 : List Nat := [1, 3, 3, 1, 2, 4, 2, 1, 2, 3]
def baseStart_2645301 : Nat := 118140960795 + 2645301 * 2 ^ 59
def prefixEnd_2645301 : Nat := 4983230072969 + 3 ^ 40 * 2645301 * 2
def baseEnd_2645301 : Nat := 905540592546173320914659

theorem tailTrace_2645301 : CollatzResearch.WordTrace tailWord_2645301 prefixEnd_2645301 905540592546173320914659 := by
  unfold tailWord_2645301
  simp only [CollatzResearch.WordTrace]
  refine ⟨96482053789533733287751757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64321369193022488858501171 96482053789533733287751757)
  ·
    refine ⟨36180770171075149982906909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96482053789533733287751757 36180770171075149982906909)
    ·
      refine ⟨13567788814153181243590091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36180770171075149982906909 13567788814153181243590091)
      ·
        refine ⟨20351683221229771865385137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13567788814153181243590091 20351683221229771865385137)
        ·
          refine ⟨15263762415922328899038853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20351683221229771865385137 15263762415922328899038853)
          ·
            refine ⟨2861955452985436668569785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15263762415922328899038853 2861955452985436668569785)
            ·
              refine ⟨2146466589739077501427339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2861955452985436668569785 2146466589739077501427339)
              ·
                refine ⟨3219699884608616252141009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2146466589739077501427339 3219699884608616252141009)
                ·
                  refine ⟨2414774913456462189105757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3219699884608616252141009 2414774913456462189105757)
                  ·
                    refine ⟨905540592546173320914659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2414774913456462189105757 905540592546173320914659)
                    ·
                      rfl

theorem cell22_2645301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_2645301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645301 prefixEnd_2645301 := by exact prefixLift 2645301
  have htrace : WordTrace (prefixWord ++ tailWord_2645301) baseStart_2645301 baseEnd_2645301 := by
    simpa [prefixWord, tailWord_2645301, baseEnd_2645301] using wordTrace_append hprefix tailTrace_2645301
  have hstable : (prefixWord ++ tailWord_2645301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645301).length < 2 ^ (prefixWord ++ tailWord_2645301).sum := by decide
  have hdescent : baseEnd_2645301 < baseStart_2645301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645329 : List Nat := [1, 2, 2, 1, 4, 1, 2, 5, 1, 3]
def baseStart_2645329 : Nat := 118140960795 + 2645329 * 2 ^ 59
def prefixEnd_2645329 : Nat := 4983230072969 + 3 ^ 40 * 2645329 * 2
def baseEnd_2645329 : Nat := 905550177518390581214573

theorem tailTrace_2645329 : CollatzResearch.WordTrace tailWord_2645329 prefixEnd_2645329 905550177518390581214573 := by
  unfold tailWord_2645329
  simp only [CollatzResearch.WordTrace]
  refine ⟨96483075033432294069771041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64322050022288196046514027 96483075033432294069771041)
  ·
    refine ⟨72362306275074220552328281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96483075033432294069771041 72362306275074220552328281)
    ·
      refine ⟨54271729706305665414246211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72362306275074220552328281 54271729706305665414246211)
      ·
        refine ⟨81407594559458498121369317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54271729706305665414246211 81407594559458498121369317)
        ·
          refine ⟨15263923979898468397756747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81407594559458498121369317 15263923979898468397756747)
          ·
            refine ⟨22895885969847702596635121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15263923979898468397756747 22895885969847702596635121)
            ·
              refine ⟨17171914477385776947476341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22895885969847702596635121 17171914477385776947476341)
              ·
                refine ⟨1609866982254916588825907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17171914477385776947476341 1609866982254916588825907)
                ·
                  refine ⟨2414800473382374883238861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1609866982254916588825907 2414800473382374883238861)
                  ·
                    refine ⟨905550177518390581214573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2414800473382374883238861 905550177518390581214573)
                    ·
                      rfl

theorem cell22_2645329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5, 1, 3].length) (baseStart_2645329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645329 prefixEnd_2645329 := by exact prefixLift 2645329
  have htrace : WordTrace (prefixWord ++ tailWord_2645329) baseStart_2645329 baseEnd_2645329 := by
    simpa [prefixWord, tailWord_2645329, baseEnd_2645329] using wordTrace_append hprefix tailTrace_2645329
  have hstable : (prefixWord ++ tailWord_2645329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645329).length < 2 ^ (prefixWord ++ tailWord_2645329).sum := by decide
  have hdescent : baseEnd_2645329 < baseStart_2645329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645346 : List Nat := [3, 3, 2, 1, 1, 1, 3, 4, 1, 3]
def baseStart_2645346 : Nat := 118140960795 + 2645346 * 2 ^ 59
def prefixEnd_2645346 : Nat := 4983230072969 + 3 ^ 40 * 2645346 * 2
def baseEnd_2645346 : Nat := 905555996965808203539521

theorem tailTrace_2645346 : CollatzResearch.WordTrace tailWord_2645346 prefixEnd_2645346 905555996965808203539521 := by
  unfold tailWord_2645346
  simp only [CollatzResearch.WordTrace]
  refine ⟨24120923768592676493284973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64322463382913803982093261 24120923768592676493284973)
  ·
    refine ⟨9045346413222253684981865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24120923768592676493284973 9045346413222253684981865)
    ·
      refine ⟨6784009809916690263736399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9045346413222253684981865 6784009809916690263736399)
      ·
        refine ⟨10176014714875035395604599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6784009809916690263736399 10176014714875035395604599)
        ·
          refine ⟨15264022072312553093406899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10176014714875035395604599 15264022072312553093406899)
          ·
            refine ⟨22896033108468829640110349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15264022072312553093406899 22896033108468829640110349)
            ·
              refine ⟨8586012415675811115041381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22896033108468829640110349 8586012415675811115041381)
              ·
                refine ⟨1609877327939214584070259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8586012415675811115041381 1609877327939214584070259)
                ·
                  refine ⟨2414815991908821876105389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1609877327939214584070259 2414815991908821876105389)
                  ·
                    refine ⟨905555996965808203539521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2414815991908821876105389 905555996965808203539521)
                    ·
                      rfl

theorem cell22_2645346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_2645346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645346 prefixEnd_2645346 := by exact prefixLift 2645346
  have htrace : WordTrace (prefixWord ++ tailWord_2645346) baseStart_2645346 baseEnd_2645346 := by
    simpa [prefixWord, tailWord_2645346, baseEnd_2645346] using wordTrace_append hprefix tailTrace_2645346
  have hstable : (prefixWord ++ tailWord_2645346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645346).length < 2 ^ (prefixWord ++ tailWord_2645346).sum := by decide
  have hdescent : baseEnd_2645346 < baseStart_2645346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645357 : List Nat := [1, 5, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_2645357 : Nat := 118140960795 + 2645357 * 2 ^ 59
def prefixEnd_2645357 : Nat := 4983230072969 + 3 ^ 40 * 2645357 * 2
def baseEnd_2645357 : Nat := 905559762490607841514487

theorem tailTrace_2645357 : CollatzResearch.WordTrace tailWord_2645357 prefixEnd_2645357 905559762490607841514487 := by
  unfold tailWord_2645357
  simp only [CollatzResearch.WordTrace]
  refine ⟨96484096277330854851790325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64322730851553903234526883 96484096277330854851790325)
  ·
    refine ⟨9045384025999767642355343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96484096277330854851790325 9045384025999767642355343)
    ·
      refine ⟨13568076038999651463533015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9045384025999767642355343 13568076038999651463533015)
      ·
        refine ⟨20352114058499477195299523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13568076038999651463533015 20352114058499477195299523)
        ·
          refine ⟨30528171087749215792949285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20352114058499477195299523 30528171087749215792949285)
          ·
            refine ⟨5724032078952977961177991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30528171087749215792949285 5724032078952977961177991)
            ·
              refine ⟨8586048118429466941766987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5724032078952977961177991 8586048118429466941766987)
              ·
                refine ⟨12879072177644200412650481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8586048118429466941766987 12879072177644200412650481)
                ·
                  refine ⟨9659304133233150309487861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12879072177644200412650481 9659304133233150309487861)
                  ·
                    refine ⟨905559762490607841514487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9659304133233150309487861 905559762490607841514487)
                    ·
                      rfl

theorem cell22_2645357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_2645357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645357 prefixEnd_2645357 := by exact prefixLift 2645357
  have htrace : WordTrace (prefixWord ++ tailWord_2645357) baseStart_2645357 baseEnd_2645357 := by
    simpa [prefixWord, tailWord_2645357, baseEnd_2645357] using wordTrace_append hprefix tailTrace_2645357
  have hstable : (prefixWord ++ tailWord_2645357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645357).length < 2 ^ (prefixWord ++ tailWord_2645357).sum := by decide
  have hdescent : baseEnd_2645357 < baseStart_2645357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645370 : List Nat := [3, 1, 1, 1, 1, 1, 2, 6, 6]
def baseStart_2645370 : Nat := 118140960795 + 2645370 * 2 ^ 59
def prefixEnd_2645370 : Nat := 4983230072969 + 3 ^ 40 * 2645370 * 2
def baseEnd_2645370 : Nat := 301854737552093380313149

theorem tailTrace_2645370 : CollatzResearch.WordTrace tailWord_2645370 prefixEnd_2645370 301854737552093380313149 := by
  unfold tailWord_2645370
  simp only [CollatzResearch.WordTrace]
  refine ⟨24121142606570939518003391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64323046950855838714675709 24121142606570939518003391)
  ·
    refine ⟨36181713909856409277005087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24121142606570939518003391 36181713909856409277005087)
    ·
      refine ⟨54272570864784613915507631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36181713909856409277005087 54272570864784613915507631)
      ·
        refine ⟨81408856297176920873261447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54272570864784613915507631 81408856297176920873261447)
        ·
          refine ⟨122113284445765381309892171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81408856297176920873261447 122113284445765381309892171)
          ·
            refine ⟨183169926668648071964838257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122113284445765381309892171 183169926668648071964838257)
            ·
              refine ⟨137377445001486053973628693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183169926668648071964838257 137377445001486053973628693)
              ·
                refine ⟨6439567734444658780013845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 137377445001486053973628693 6439567734444658780013845)
                ·
                  refine ⟨301854737552093380313149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6439567734444658780013845 301854737552093380313149)
                  ·
                    rfl

theorem cell22_2645370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 6].length) (baseStart_2645370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645370 prefixEnd_2645370 := by exact prefixLift 2645370
  have htrace : WordTrace (prefixWord ++ tailWord_2645370) baseStart_2645370 baseEnd_2645370 := by
    simpa [prefixWord, tailWord_2645370, baseEnd_2645370] using wordTrace_append hprefix tailTrace_2645370
  have hstable : (prefixWord ++ tailWord_2645370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645370).length < 2 ^ (prefixWord ++ tailWord_2645370).sum := by decide
  have hdescent : baseEnd_2645370 < baseStart_2645370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645372 : List Nat := [2, 2, 2, 1, 1, 1, 4, 4, 1, 4]
def baseStart_2645372 : Nat := 118140960795 + 2645372 * 2 ^ 59
def prefixEnd_2645372 : Nat := 4983230072969 + 3 ^ 40 * 2645372 * 2
def baseEnd_2645372 : Nat := 905564897297152802389441

theorem tailTrace_2645372 : CollatzResearch.WordTrace tailWord_2645372 prefixEnd_2645372 905564897297152802389441 := by
  unfold tailWord_2645372
  simp only [CollatzResearch.WordTrace]
  refine ⟨48242321686138256206793185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64323095581517674942390913 48242321686138256206793185)
  ·
    refine ⟨36181741264603692155094889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48242321686138256206793185 36181741264603692155094889)
    ·
      refine ⟨27136305948452769116321167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36181741264603692155094889 27136305948452769116321167)
      ·
        refine ⟨40704458922679153674481751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27136305948452769116321167 40704458922679153674481751)
        ·
          refine ⟨61056688384018730511722627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40704458922679153674481751 61056688384018730511722627)
          ·
            refine ⟨91585032576028095767583941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61056688384018730511722627 91585032576028095767583941)
            ·
              refine ⟨17172193608005267956421989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91585032576028095767583941 17172193608005267956421989)
              ·
                refine ⟨3219786301500987741829123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17172193608005267956421989 3219786301500987741829123)
                ·
                  refine ⟨4829679452251481612743685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3219786301500987741829123 4829679452251481612743685)
                  ·
                    refine ⟨905564897297152802389441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4829679452251481612743685 905564897297152802389441)
                    ·
                      rfl

theorem cell22_2645372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_2645372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645372 prefixEnd_2645372 := by exact prefixLift 2645372
  have htrace : WordTrace (prefixWord ++ tailWord_2645372) baseStart_2645372 baseEnd_2645372 := by
    simpa [prefixWord, tailWord_2645372, baseEnd_2645372] using wordTrace_append hprefix tailTrace_2645372
  have hstable : (prefixWord ++ tailWord_2645372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645372).length < 2 ^ (prefixWord ++ tailWord_2645372).sum := by decide
  have hdescent : baseEnd_2645372 < baseStart_2645372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645432 : List Nat := [2, 1, 2, 1, 2, 2, 6, 6]
def baseStart_2645432 : Nat := 118140960795 + 2645432 * 2 ^ 59
def prefixEnd_2645432 : Nat := 4983230072969 + 3 ^ 40 * 2645432 * 2
def baseEnd_2645432 : Nat := 100620604058148071765473

theorem tailTrace_2645432 : CollatzResearch.WordTrace tailWord_2645432 prefixEnd_2645432 100620604058148071765473 := by
  unfold tailWord_2645432
  simp only [CollatzResearch.WordTrace]
  refine ⟨48243415876029571330385275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64324554501372761773847033 48243415876029571330385275)
  ·
    refine ⟨72365123814044356995577913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48243415876029571330385275 72365123814044356995577913)
    ·
      refine ⟨54273842860533267746683435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72365123814044356995577913 54273842860533267746683435)
      ·
        refine ⟨81410764290799901620025153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54273842860533267746683435 81410764290799901620025153)
        ·
          refine ⟨61058073218099926215018865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81410764290799901620025153 61058073218099926215018865)
          ·
            refine ⟨45793554913574944661264149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61058073218099926215018865 45793554913574944661264149)
            ·
              refine ⟨2146572886573825530996757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45793554913574944661264149 2146572886573825530996757)
              ·
                refine ⟨100620604058148071765473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2146572886573825530996757 100620604058148071765473)
                ·
                  rfl

theorem cell22_2645432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 6].length) (baseStart_2645432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645432 prefixEnd_2645432 := by exact prefixLift 2645432
  have htrace : WordTrace (prefixWord ++ tailWord_2645432) baseStart_2645432 baseEnd_2645432 := by
    simpa [prefixWord, tailWord_2645432, baseEnd_2645432] using wordTrace_append hprefix tailTrace_2645432
  have hstable : (prefixWord ++ tailWord_2645432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645432).length < 2 ^ (prefixWord ++ tailWord_2645432).sum := by decide
  have hdescent : baseEnd_2645432 < baseStart_2645432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645464 : List Nat := [2, 1, 2, 2, 2, 1, 5, 1, 3, 3]
def baseStart_2645464 : Nat := 118140960795 + 2645464 * 2 ^ 59
def prefixEnd_2645464 : Nat := 4983230072969 + 3 ^ 40 * 2645464 * 2
def baseEnd_2645464 : Nat := 905596390777295229089159

theorem tailTrace_2645464 : CollatzResearch.WordTrace tailWord_2645464 prefixEnd_2645464 905596390777295229089159 := by
  unfold tailWord_2645464
  simp only [CollatzResearch.WordTrace]
  refine ⟨48243999443971606062967723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64325332591962141417290297 48243999443971606062967723)
  ·
    refine ⟨72365999165957409094451585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48243999443971606062967723 72365999165957409094451585)
    ·
      refine ⟨54274499374468056820838689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72365999165957409094451585 54274499374468056820838689)
      ·
        refine ⟨40705874530851042615629017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54274499374468056820838689 40705874530851042615629017)
        ·
          refine ⟨30529405898138281961721763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40705874530851042615629017 30529405898138281961721763)
          ·
            refine ⟨45794108847207422942582645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30529405898138281961721763 45794108847207422942582645)
            ·
              refine ⟨4293197704425695900867123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45794108847207422942582645 4293197704425695900867123)
              ·
                refine ⟨6439796556638543851300685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4293197704425695900867123 6439796556638543851300685)
                ·
                  refine ⟨2414923708739453944237757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6439796556638543851300685 2414923708739453944237757)
                  ·
                    refine ⟨905596390777295229089159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2414923708739453944237757 905596390777295229089159)
                    ·
                      rfl

theorem cell22_2645464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 3, 3].length) (baseStart_2645464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645464 prefixEnd_2645464 := by exact prefixLift 2645464
  have htrace : WordTrace (prefixWord ++ tailWord_2645464) baseStart_2645464 baseEnd_2645464 := by
    simpa [prefixWord, tailWord_2645464, baseEnd_2645464] using wordTrace_append hprefix tailTrace_2645464
  have hstable : (prefixWord ++ tailWord_2645464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645464).length < 2 ^ (prefixWord ++ tailWord_2645464).sum := by decide
  have hdescent : baseEnd_2645464 < baseStart_2645464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645515 : List Nat := [1, 1, 1, 1, 8, 2, 2, 2, 1, 3]
def baseStart_2645515 : Nat := 118140960795 + 2645515 * 2 ^ 59
def prefixEnd_2645515 : Nat := 4983230072969 + 3 ^ 40 * 2645515 * 2
def baseEnd_2645515 : Nat := 905613849119548096064003

theorem tailTrace_2645515 : CollatzResearch.WordTrace tailWord_2645515 prefixEnd_2645515 905613849119548096064003 := by
  unfold tailWord_2645515
  simp only [CollatzResearch.WordTrace]
  refine ⟨96489859010758447836041999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64326572673838965224027999 96489859010758447836041999)
  ·
    refine ⟨144734788516137671754062999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96489859010758447836041999 144734788516137671754062999)
    ·
      refine ⟨217102182774206507631094499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144734788516137671754062999 217102182774206507631094499)
      ·
        refine ⟨325653274161309761446641749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217102182774206507631094499 325653274161309761446641749)
        ·
          refine ⟨3816249306577848766952833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 325653274161309761446641749 3816249306577848766952833)
          ·
            refine ⟨2862186979933386575214625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3816249306577848766952833 2862186979933386575214625)
            ·
              refine ⟨2146640234950039931410969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2862186979933386575214625 2146640234950039931410969)
              ·
                refine ⟨1609980176212529948558227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2146640234950039931410969 1609980176212529948558227)
                ·
                  refine ⟨2414970264318794922837341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1609980176212529948558227 2414970264318794922837341)
                  ·
                    refine ⟨905613849119548096064003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2414970264318794922837341 905613849119548096064003)
                    ·
                      rfl

theorem cell22_2645515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2, 1, 3].length) (baseStart_2645515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645515 prefixEnd_2645515 := by exact prefixLift 2645515
  have htrace : WordTrace (prefixWord ++ tailWord_2645515) baseStart_2645515 baseEnd_2645515 := by
    simpa [prefixWord, tailWord_2645515, baseEnd_2645515] using wordTrace_append hprefix tailTrace_2645515
  have hstable : (prefixWord ++ tailWord_2645515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645515).length < 2 ^ (prefixWord ++ tailWord_2645515).sum := by decide
  have hdescent : baseEnd_2645515 < baseStart_2645515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645539 : List Nat := [1, 1, 1, 4, 5, 1, 1, 2, 6]
def baseStart_2645539 : Nat := 118140960795 + 2645539 * 2 ^ 59
def prefixEnd_2645539 : Nat := 4983230072969 + 3 ^ 40 * 2645539 * 2
def baseEnd_2645539 : Nat := 301874021603340011154643

theorem tailTrace_2645539 : CollatzResearch.WordTrace tailWord_2645539 prefixEnd_2645539 301874021603340011154643 := by
  unfold tailWord_2645539
  simp only [CollatzResearch.WordTrace]
  refine ⟨96490734362671499934915671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64327156241780999956610447 96490734362671499934915671)
  ·
    refine ⟨144736101544007249902373507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96490734362671499934915671 144736101544007249902373507)
    ·
      refine ⟨217104152316010874853560261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144736101544007249902373507 217104152316010874853560261)
      ·
        refine ⟨40707028559252039035042549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 217104152316010874853560261 40707028559252039035042549)
        ·
          refine ⟨3816283927429878659535239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40707028559252039035042549 3816283927429878659535239)
          ·
            refine ⟨5724425891144817989302859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3816283927429878659535239 5724425891144817989302859)
            ·
              refine ⟨8586638836717226983954289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5724425891144817989302859 8586638836717226983954289)
              ·
                refine ⟨6439979127537920237965717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8586638836717226983954289 6439979127537920237965717)
                ·
                  refine ⟨301874021603340011154643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6439979127537920237965717 301874021603340011154643)
                  ·
                    rfl

theorem cell22_2645539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 6].length) (baseStart_2645539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645539 prefixEnd_2645539 := by exact prefixLift 2645539
  have htrace : WordTrace (prefixWord ++ tailWord_2645539) baseStart_2645539 baseEnd_2645539 := by
    simpa [prefixWord, tailWord_2645539, baseEnd_2645539] using wordTrace_append hprefix tailTrace_2645539
  have hstable : (prefixWord ++ tailWord_2645539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645539).length < 2 ^ (prefixWord ++ tailWord_2645539).sum := by decide
  have hdescent : baseEnd_2645539 < baseStart_2645539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645554 : List Nat := [3, 2, 1, 1, 2, 1, 1, 4, 4, 3]
def baseStart_2645554 : Nat := 118140960795 + 2645554 * 2 ^ 59
def prefixEnd_2645554 : Nat := 4983230072969 + 3 ^ 40 * 2645554 * 2
def baseEnd_2645554 : Nat := 905627199616564994338883

theorem tailTrace_2645554 : CollatzResearch.WordTrace tailWord_2645554 prefixEnd_2645554 905627199616564994338883 := by
  unfold tailWord_2645554
  simp only [CollatzResearch.WordTrace]
  refine ⟨24122820364404289374177929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64327520971744771664474477 24122820364404289374177929)
  ·
    refine ⟨18092115273303217030633447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24122820364404289374177929 18092115273303217030633447)
    ·
      refine ⟨27138172909954825545950171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18092115273303217030633447 27138172909954825545950171)
      ·
        refine ⟨40707259364932238318925257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27138172909954825545950171 40707259364932238318925257)
        ·
          refine ⟨30530444523699178739193943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40707259364932238318925257 30530444523699178739193943)
          ·
            refine ⟨45795666785548768108790915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30530444523699178739193943 45795666785548768108790915)
            ·
              refine ⟨68693500178323152163186373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45795666785548768108790915 68693500178323152163186373)
              ·
                refine ⟨12880031283435591030597445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68693500178323152163186373 12880031283435591030597445)
                ·
                  refine ⟨2415005865644173318237021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12880031283435591030597445 2415005865644173318237021)
                  ·
                    refine ⟨905627199616564994338883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2415005865644173318237021 905627199616564994338883)
                    ·
                      rfl

theorem cell22_2645554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_2645554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645554 prefixEnd_2645554 := by exact prefixLift 2645554
  have htrace : WordTrace (prefixWord ++ tailWord_2645554) baseStart_2645554 baseEnd_2645554 := by
    simpa [prefixWord, tailWord_2645554, baseEnd_2645554] using wordTrace_append hprefix tailTrace_2645554
  have hstable : (prefixWord ++ tailWord_2645554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645554).length < 2 ^ (prefixWord ++ tailWord_2645554).sum := by decide
  have hdescent : baseEnd_2645554 < baseStart_2645554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645558 : List Nat := [5, 1, 2, 1, 3, 1, 1, 3, 1, 4]
def baseStart_2645558 : Nat := 118140960795 + 2645558 * 2 ^ 59
def prefixEnd_2645558 : Nat := 4983230072969 + 3 ^ 40 * 2645558 * 2
def baseEnd_2645558 : Nat := 905628568898310317238871

theorem tailTrace_2645558 : CollatzResearch.WordTrace tailWord_2645558 prefixEnd_2645558 905628568898310317238871 := by
  unfold tailWord_2645558
  simp only [CollatzResearch.WordTrace]
  refine ⟨6030714209350166636241083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64327618233068444119904885 6030714209350166636241083)
  ·
    refine ⟨9046071314025249954361625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6030714209350166636241083 9046071314025249954361625)
    ·
      refine ⟨6784553485518937465771219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9046071314025249954361625 6784553485518937465771219)
      ·
        refine ⟨10176830228278406198656829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6784553485518937465771219 10176830228278406198656829)
        ·
          refine ⟨3816311335604402324496311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10176830228278406198656829 3816311335604402324496311)
          ·
            refine ⟨5724467003406603486744467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3816311335604402324496311 5724467003406603486744467)
            ·
              refine ⟨8586700505109905230116701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5724467003406603486744467 8586700505109905230116701)
              ·
                refine ⟨3220012689416214461293763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8586700505109905230116701 3220012689416214461293763)
                ·
                  refine ⟨4830019034124321691940645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3220012689416214461293763 4830019034124321691940645)
                  ·
                    refine ⟨905628568898310317238871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4830019034124321691940645 905628568898310317238871)
                    ·
                      rfl

theorem cell22_2645558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_2645558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645558 prefixEnd_2645558 := by exact prefixLift 2645558
  have htrace : WordTrace (prefixWord ++ tailWord_2645558) baseStart_2645558 baseEnd_2645558 := by
    simpa [prefixWord, tailWord_2645558, baseEnd_2645558] using wordTrace_append hprefix tailTrace_2645558
  have hstable : (prefixWord ++ tailWord_2645558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645558).length < 2 ^ (prefixWord ++ tailWord_2645558).sum := by decide
  have hdescent : baseEnd_2645558 < baseStart_2645558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645567 : List Nat := [1, 1, 2, 2, 3, 4, 9]
def baseStart_2645567 : Nat := 118140960795 + 2645567 * 2 ^ 59
def prefixEnd_2645567 : Nat := 4983230072969 + 3 ^ 40 * 2645567 * 2
def baseEnd_2645567 : Nat := 33541912954897677546809

theorem tailTrace_2645567 : CollatzResearch.WordTrace tailWord_2645567 prefixEnd_2645567 33541912954897677546809 := by
  unfold tailWord_2645567
  simp only [CollatzResearch.WordTrace]
  refine ⟨96491755606570060716934955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64327837071046707144623303 96491755606570060716934955)
  ·
    refine ⟨144737633409855091075402433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96491755606570060716934955 144737633409855091075402433)
    ·
      refine ⟨108553225057391318306551825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144737633409855091075402433 108553225057391318306551825)
      ·
        refine ⟨81414918793043488729913869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108553225057391318306551825 81414918793043488729913869)
        ·
          refine ⟨30530594547391308273717701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81414918793043488729913869 30530594547391308273717701)
          ·
            refine ⟨5724486477635870301322069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30530594547391308273717701 5724486477635870301322069)
            ·
              refine ⟨33541912954897677546809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5724486477635870301322069 33541912954897677546809)
              ·
                rfl

theorem cell22_2645567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 9].length) (baseStart_2645567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645567 prefixEnd_2645567 := by exact prefixLift 2645567
  have htrace : WordTrace (prefixWord ++ tailWord_2645567) baseStart_2645567 baseEnd_2645567 := by
    simpa [prefixWord, tailWord_2645567, baseEnd_2645567] using wordTrace_append hprefix tailTrace_2645567
  have hstable : (prefixWord ++ tailWord_2645567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645567).length < 2 ^ (prefixWord ++ tailWord_2645567).sum := by decide
  have hdescent : baseEnd_2645567 < baseStart_2645567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645569 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 4, 4]
def baseStart_2645569 : Nat := 118140960795 + 2645569 * 2 ^ 59
def prefixEnd_2645569 : Nat := 4983230072969 + 3 ^ 40 * 2645569 * 2
def baseEnd_2645569 : Nat := 905632334423109955213837

theorem tailTrace_2645569 : CollatzResearch.WordTrace tailWord_2645569 prefixEnd_2645569 905632334423109955213837 := by
  unfold tailWord_2645569
  simp only [CollatzResearch.WordTrace]
  refine ⟨96491828552562815058507761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64327885701708543372338507 96491828552562815058507761)
  ·
    refine ⟨72368871414422111293880821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96491828552562815058507761 72368871414422111293880821)
    ·
      refine ⟨6784581695102072933801327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72368871414422111293880821 6784581695102072933801327)
      ·
        refine ⟨10176872542653109400701991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6784581695102072933801327 10176872542653109400701991)
        ·
          refine ⟨15265308813979664101052987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10176872542653109400701991 15265308813979664101052987)
          ·
            refine ⟨22897963220969496151579481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15265308813979664101052987 22897963220969496151579481)
            ·
              refine ⟨17173472415727122113684611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22897963220969496151579481 17173472415727122113684611)
              ·
                refine ⟨25760208623590683170526917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17173472415727122113684611 25760208623590683170526917)
                ·
                  refine ⟨4830039116923253094473797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25760208623590683170526917 4830039116923253094473797)
                  ·
                    refine ⟨905632334423109955213837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4830039116923253094473797 905632334423109955213837)
                    ·
                      rfl

theorem cell22_2645569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_2645569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645569 prefixEnd_2645569 := by exact prefixLift 2645569
  have htrace : WordTrace (prefixWord ++ tailWord_2645569) baseStart_2645569 baseEnd_2645569 := by
    simpa [prefixWord, tailWord_2645569, baseEnd_2645569] using wordTrace_append hprefix tailTrace_2645569
  have hstable : (prefixWord ++ tailWord_2645569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645569).length < 2 ^ (prefixWord ++ tailWord_2645569).sum := by decide
  have hdescent : baseEnd_2645569 < baseStart_2645569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645588 : List Nat := [2, 4, 1, 1, 1, 2, 5, 1, 2, 3]
def baseStart_2645588 : Nat := 118140960795 + 2645588 * 2 ^ 59
def prefixEnd_2645588 : Nat := 4983230072969 + 3 ^ 40 * 2645588 * 2
def baseEnd_2645588 : Nat := 905638838511400238988779

theorem tailTrace_2645588 : CollatzResearch.WordTrace tailWord_2645588 prefixEnd_2645588 905638838511400238988779 := by
  unfold tailWord_2645588
  simp only [CollatzResearch.WordTrace]
  refine ⟨48246260769746990651724709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64328347692995987535632945 48246260769746990651724709)
  ·
    refine ⟨9046173894327560747198383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48246260769746990651724709 9046173894327560747198383)
    ·
      refine ⟨13569260841491341120797575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9046173894327560747198383 13569260841491341120797575)
      ·
        refine ⟨20353891262237011681196363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13569260841491341120797575 20353891262237011681196363)
        ·
          refine ⟨30530836893355517521794545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20353891262237011681196363 30530836893355517521794545)
          ·
            refine ⟨22898127670016638141345909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30530836893355517521794545 22898127670016638141345909)
            ·
              refine ⟨2146699469064059825751179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22898127670016638141345909 2146699469064059825751179)
              ·
                refine ⟨3220049203596089738626769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2146699469064059825751179 3220049203596089738626769)
                ·
                  refine ⟨2415036902697067303970077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3220049203596089738626769 2415036902697067303970077)
                  ·
                    refine ⟨905638838511400238988779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2415036902697067303970077 905638838511400238988779)
                    ·
                      rfl

theorem cell22_2645588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_2645588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645588 prefixEnd_2645588 := by exact prefixLift 2645588
  have htrace : WordTrace (prefixWord ++ tailWord_2645588) baseStart_2645588 baseEnd_2645588 := by
    simpa [prefixWord, tailWord_2645588, baseEnd_2645588] using wordTrace_append hprefix tailTrace_2645588
  have hstable : (prefixWord ++ tailWord_2645588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645588).length < 2 ^ (prefixWord ++ tailWord_2645588).sum := by decide
  have hdescent : baseEnd_2645588 < baseStart_2645588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645629 : List Nat := [1, 4, 1, 1, 4, 1, 2, 1, 7]
def baseStart_2645629 : Nat := 118140960795 + 2645629 * 2 ^ 59
def prefixEnd_2645629 : Nat := 4983230072969 + 3 ^ 40 * 2645629 * 2
def baseEnd_2645629 : Nat := 301884291216429932904551

theorem tailTrace_2645629 : CollatzResearch.WordTrace tailWord_2645629 prefixEnd_2645629 301884291216429932904551 := by
  unfold tailWord_2645629
  simp only [CollatzResearch.WordTrace]
  refine ⟨96494016932345445305691941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64329344621563630203794627 96494016932345445305691941)
  ·
    refine ⟨18092628174814770994817239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96494016932345445305691941 18092628174814770994817239)
    ·
      refine ⟨27138942262222156492225859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18092628174814770994817239 27138942262222156492225859)
      ·
        refine ⟨40708413393333234738338789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27138942262222156492225859 40708413393333234738338789)
        ·
          refine ⟨7632827511249981513438523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40708413393333234738338789 7632827511249981513438523)
          ·
            refine ⟨11449241266874972270157785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7632827511249981513438523 11449241266874972270157785)
            ·
              refine ⟨8586930950156229202618339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11449241266874972270157785 8586930950156229202618339)
              ·
                refine ⟨12880396425234343803927509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8586930950156229202618339 12880396425234343803927509)
                ·
                  refine ⟨301884291216429932904551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12880396425234343803927509 301884291216429932904551)
                  ·
                    rfl

theorem cell22_2645629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_2645629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645629 prefixEnd_2645629 := by exact prefixLift 2645629
  have htrace : WordTrace (prefixWord ++ tailWord_2645629) baseStart_2645629 baseEnd_2645629 := by
    simpa [prefixWord, tailWord_2645629, baseEnd_2645629] using wordTrace_append hprefix tailTrace_2645629
  have hstable : (prefixWord ++ tailWord_2645629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645629).length < 2 ^ (prefixWord ++ tailWord_2645629).sum := by decide
  have hdescent : baseEnd_2645629 < baseStart_2645629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645633 : List Nat := [1, 2, 4, 2, 1, 4, 1, 1, 3, 3]
def baseStart_2645633 : Nat := 118140960795 + 2645633 * 2 ^ 59
def prefixEnd_2645633 : Nat := 4983230072969 + 3 ^ 40 * 2645633 * 2
def baseEnd_2645633 : Nat := 905654242931035121613641

theorem tailTrace_2645633 : CollatzResearch.WordTrace tailWord_2645633 prefixEnd_2645633 905654242931035121613641 := by
  unfold tailWord_2645633
  simp only [CollatzResearch.WordTrace]
  refine ⟨96494162824330953988837553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64329441882887302659225035 96494162824330953988837553)
  ·
    refine ⟨72370622118248215491628165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96494162824330953988837553 72370622118248215491628165)
    ·
      refine ⟨13569491647171540404680281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72370622118248215491628165 13569491647171540404680281)
      ·
        refine ⟨10177118735378655303510211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13569491647171540404680281 10177118735378655303510211)
        ·
          refine ⟨15265678103067982955265317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10177118735378655303510211 15265678103067982955265317)
          ·
            refine ⟨2862314644325246804112247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15265678103067982955265317 2862314644325246804112247)
            ·
              refine ⟨4293471966487870206168371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2862314644325246804112247 4293471966487870206168371)
              ·
                refine ⟨6440207949731805309252557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4293471966487870206168371 6440207949731805309252557)
                ·
                  refine ⟨2415077981149426990969709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6440207949731805309252557 2415077981149426990969709)
                  ·
                    refine ⟨905654242931035121613641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2415077981149426990969709 905654242931035121613641)
                    ·
                      rfl

theorem cell22_2645633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_2645633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645633 prefixEnd_2645633 := by exact prefixLift 2645633
  have htrace : WordTrace (prefixWord ++ tailWord_2645633) baseStart_2645633 baseEnd_2645633 := by
    simpa [prefixWord, tailWord_2645633, baseEnd_2645633] using wordTrace_append hprefix tailTrace_2645633
  have hstable : (prefixWord ++ tailWord_2645633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645633).length < 2 ^ (prefixWord ++ tailWord_2645633).sum := by decide
  have hdescent : baseEnd_2645633 < baseStart_2645633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645646 : List Nat := [4, 1, 1, 3, 1, 3, 1, 3, 5]
def baseStart_2645646 : Nat := 118140960795 + 2645646 * 2 ^ 59
def prefixEnd_2645646 : Nat := 4983230072969 + 3 ^ 40 * 2645646 * 2
def baseEnd_2645646 : Nat := 301886231032235807012867

theorem tailTrace_2645646 : CollatzResearch.WordTrace tailWord_2645646 prefixEnd_2645646 301886231032235807012867 := by
  unfold tailWord_2645646
  simp only [CollatzResearch.WordTrace]
  refine ⟨12061829621660482151132599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64329757982189238139373861 12061829621660482151132599)
  ·
    refine ⟨18092744432490723226698899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12061829621660482151132599 18092744432490723226698899)
    ·
      refine ⟨27139116648736084840048349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18092744432490723226698899 27139116648736084840048349)
      ·
        refine ⟨10177168743276031815018131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27139116648736084840048349 10177168743276031815018131)
        ·
          refine ⟨15265753114914047722527197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10177168743276031815018131 15265753114914047722527197)
          ·
            refine ⟨5724657418092767895947699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15265753114914047722527197 5724657418092767895947699)
            ·
              refine ⟨8586986127139151843921549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5724657418092767895947699 8586986127139151843921549)
              ·
                refine ⟨3220119797677181941470581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8586986127139151843921549 3220119797677181941470581)
                ·
                  refine ⟨301886231032235807012867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3220119797677181941470581 301886231032235807012867)
                  ·
                    rfl

theorem cell22_2645646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_2645646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645646 prefixEnd_2645646 := by exact prefixLift 2645646
  have htrace : WordTrace (prefixWord ++ tailWord_2645646) baseStart_2645646 baseEnd_2645646 := by
    simpa [prefixWord, tailWord_2645646, baseEnd_2645646] using wordTrace_append hprefix tailTrace_2645646
  have hstable : (prefixWord ++ tailWord_2645646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645646).length < 2 ^ (prefixWord ++ tailWord_2645646).sum := by decide
  have hdescent : baseEnd_2645646 < baseStart_2645646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645704 : List Nat := [2, 1, 3, 1, 2, 2, 2, 2, 1, 6]
def baseStart_2645704 : Nat := 118140960795 + 2645704 * 2 ^ 59
def prefixEnd_2645704 : Nat := 4983230072969 + 3 ^ 40 * 2645704 * 2
def baseEnd_2645704 : Nat := 905678547682014603088423

theorem tailTrace_2645704 : CollatzResearch.WordTrace tailWord_2645704 prefixEnd_2645704 905678547682014603088423 := by
  unfold tailWord_2645704
  simp only [CollatzResearch.WordTrace]
  refine ⟨48248376203536866557336083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64331168271382488743114777 48248376203536866557336083)
  ·
    refine ⟨72372564305305299836004125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48248376203536866557336083 72372564305305299836004125)
    ·
      refine ⟨27139711614489487438501547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72372564305305299836004125 27139711614489487438501547)
      ·
        refine ⟨40709567421734231157752321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27139711614489487438501547 40709567421734231157752321)
        ·
          refine ⟨30532175566300673368314241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40709567421734231157752321 30532175566300673368314241)
          ·
            refine ⟨22899131674725505026235681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30532175566300673368314241 22899131674725505026235681)
            ·
              refine ⟨17174348756044128769676761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22899131674725505026235681 17174348756044128769676761)
              ·
                refine ⟨12880761567033096577257571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17174348756044128769676761 12880761567033096577257571)
                ·
                  refine ⟨19321142350549644865886357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12880761567033096577257571 19321142350549644865886357)
                  ·
                    refine ⟨905678547682014603088423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19321142350549644865886357 905678547682014603088423)
                    ·
                      rfl

theorem cell22_2645704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_2645704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645704 prefixEnd_2645704 := by exact prefixLift 2645704
  have htrace : WordTrace (prefixWord ++ tailWord_2645704) baseStart_2645704 baseEnd_2645704 := by
    simpa [prefixWord, tailWord_2645704, baseEnd_2645704] using wordTrace_append hprefix tailTrace_2645704
  have hstable : (prefixWord ++ tailWord_2645704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645704).length < 2 ^ (prefixWord ++ tailWord_2645704).sum := by decide
  have hdescent : baseEnd_2645704 < baseStart_2645704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645721 : List Nat := [1, 2, 1, 2, 3, 3, 3, 1, 2, 4]
def baseStart_2645721 : Nat := 118140960795 + 2645721 * 2 ^ 59
def prefixEnd_2645721 : Nat := 4983230072969 + 3 ^ 40 * 2645721 * 2
def baseEnd_2645721 : Nat := 905684367129432225413371

theorem tailTrace_2645721 : CollatzResearch.WordTrace tailWord_2645721 prefixEnd_2645721 905684367129432225413371 := by
  unfold tailWord_2645721
  simp only [CollatzResearch.WordTrace]
  refine ⟨96497372448012145018041017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64331581632008096678694011 96497372448012145018041017)
  ·
    refine ⟨72373029336009108763530763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96497372448012145018041017 72373029336009108763530763)
    ·
      refine ⟨108559544004013663145296145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72373029336009108763530763 108559544004013663145296145)
      ·
        refine ⟨81419658003010247358972109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108559544004013663145296145 81419658003010247358972109)
        ·
          refine ⟨30532371751128842759614541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81419658003010247358972109 30532371751128842759614541)
          ·
            refine ⟨11449639406673316034855453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30532371751128842759614541 11449639406673316034855453)
            ·
              refine ⟨4293614777502493513070795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11449639406673316034855453 4293614777502493513070795)
              ·
                refine ⟨6440422166253740269606193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4293614777502493513070795 6440422166253740269606193)
                ·
                  refine ⟨4830316624690305202204645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6440422166253740269606193 4830316624690305202204645)
                  ·
                    refine ⟨905684367129432225413371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4830316624690305202204645 905684367129432225413371)
                    ·
                      rfl

theorem cell22_2645721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 4].length) (baseStart_2645721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645721 prefixEnd_2645721 := by exact prefixLift 2645721
  have htrace : WordTrace (prefixWord ++ tailWord_2645721) baseStart_2645721 baseEnd_2645721 := by
    simpa [prefixWord, tailWord_2645721, baseEnd_2645721] using wordTrace_append hprefix tailTrace_2645721
  have hstable : (prefixWord ++ tailWord_2645721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645721).length < 2 ^ (prefixWord ++ tailWord_2645721).sum := by decide
  have hdescent : baseEnd_2645721 < baseStart_2645721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645751 : List Nat := [1, 1, 3, 1, 1, 1, 5, 3, 3, 3]
def baseStart_2645751 : Nat := 118140960795 + 2645751 * 2 ^ 59
def prefixEnd_2645751 : Nat := 4983230072969 + 3 ^ 40 * 2645751 * 2
def baseEnd_2645751 : Nat := 905694636742522147163279

theorem tailTrace_2645751 : CollatzResearch.WordTrace tailWord_2645751 prefixEnd_2645751 905694636742522147163279 := by
  unfold tailWord_2645751
  simp only [CollatzResearch.WordTrace]
  refine ⟨96498466637903460141633107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64332311091935640094422071 96498466637903460141633107)
  ·
    refine ⟨144747699956855190212449661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96498466637903460141633107 144747699956855190212449661)
    ·
      refine ⟨54280387483820696329668623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144747699956855190212449661 54280387483820696329668623)
      ·
        refine ⟨81420581225731044494502935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54280387483820696329668623 81420581225731044494502935)
        ·
          refine ⟨122130871838596566741754403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81420581225731044494502935 122130871838596566741754403)
          ·
            refine ⟨183196307757894850112631605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122130871838596566741754403 183196307757894850112631605)
            ·
              refine ⟨17174653852302642198059213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 183196307757894850112631605 17174653852302642198059213)
              ·
                refine ⟨6440495194613490824272205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17174653852302642198059213 6440495194613490824272205)
                ·
                  refine ⟨2415185697980059059102077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6440495194613490824272205 2415185697980059059102077)
                  ·
                    refine ⟨905694636742522147163279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2415185697980059059102077 905694636742522147163279)
                    ·
                      rfl

theorem cell22_2645751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3, 3].length) (baseStart_2645751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645751 prefixEnd_2645751 := by exact prefixLift 2645751
  have htrace : WordTrace (prefixWord ++ tailWord_2645751) baseStart_2645751 baseEnd_2645751 := by
    simpa [prefixWord, tailWord_2645751, baseEnd_2645751] using wordTrace_append hprefix tailTrace_2645751
  have hstable : (prefixWord ++ tailWord_2645751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645751).length < 2 ^ (prefixWord ++ tailWord_2645751).sum := by decide
  have hdescent : baseEnd_2645751 < baseStart_2645751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645779 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 4, 5]
def baseStart_2645779 : Nat := 118140960795 + 2645779 * 2 ^ 59
def prefixEnd_2645779 : Nat := 4983230072969 + 3 ^ 40 * 2645779 * 2
def baseEnd_2645779 : Nat := 905704221714739407463193

theorem tailTrace_2645779 : CollatzResearch.WordTrace tailWord_2645779 prefixEnd_2645779 905704221714739407463193 := by
  unfold tailWord_2645779
  simp only [CollatzResearch.WordTrace]
  refine ⟨96499487881802020923652391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64332991921201347282434927 96499487881802020923652391)
  ·
    refine ⟨144749231822703031385478587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96499487881802020923652391 144749231822703031385478587)
    ·
      refine ⟨217123847734054547078217881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144749231822703031385478587 217123847734054547078217881)
      ·
        refine ⟨162842885800540910308663411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217123847734054547078217881 162842885800540910308663411)
        ·
          refine ⟨244264328700811365462995117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162842885800540910308663411 244264328700811365462995117)
          ·
            refine ⟨91599123262804262048623169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 244264328700811365462995117 91599123262804262048623169)
            ·
              refine ⟨68699342447103196536467377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91599123262804262048623169 68699342447103196536467377)
              ·
                refine ⟨51524506835327397402350533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68699342447103196536467377 51524506835327397402350533)
                ·
                  refine ⟨9660845031623887012940725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51524506835327397402350533 9660845031623887012940725)
                  ·
                    refine ⟨905704221714739407463193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9660845031623887012940725 905704221714739407463193)
                    ·
                      rfl

theorem cell22_2645779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 5].length) (baseStart_2645779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645779 prefixEnd_2645779 := by exact prefixLift 2645779
  have htrace : WordTrace (prefixWord ++ tailWord_2645779) baseStart_2645779 baseEnd_2645779 := by
    simpa [prefixWord, tailWord_2645779, baseEnd_2645779] using wordTrace_append hprefix tailTrace_2645779
  have hstable : (prefixWord ++ tailWord_2645779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645779).length < 2 ^ (prefixWord ++ tailWord_2645779).sum := by decide
  have hdescent : baseEnd_2645779 < baseStart_2645779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645841 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 3, 5]
def baseStart_2645841 : Nat := 118140960795 + 2645841 * 2 ^ 59
def prefixEnd_2645841 : Nat := 4983230072969 + 3 ^ 40 * 2645841 * 2
def baseEnd_2645841 : Nat := 905725445581791912413003

theorem tailTrace_2645841 : CollatzResearch.WordTrace tailWord_2645841 prefixEnd_2645841 905725445581791912413003 := by
  unfold tailWord_2645841
  simp only [CollatzResearch.WordTrace]
  refine ⟨96501749207577405512409377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64334499471718270341606251 96501749207577405512409377)
  ·
    refine ⟨72376311905683054134307033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96501749207577405512409377 72376311905683054134307033)
    ·
      refine ⟨54282233929262290600730275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72376311905683054134307033 54282233929262290600730275)
      ·
        refine ⟨81423350893893435901095413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54282233929262290600730275 81423350893893435901095413)
        ·
          refine ⟨7633439146302509615727695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81423350893893435901095413 7633439146302509615727695)
          ·
            refine ⟨11450158719453764423591543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7633439146302509615727695 11450158719453764423591543)
            ·
              refine ⟨17175238079180646635387315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11450158719453764423591543 17175238079180646635387315)
              ·
                refine ⟨25762857118770969953080973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17175238079180646635387315 25762857118770969953080973)
                ·
                  refine ⟨9661071419539113732405365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25762857118770969953080973 9661071419539113732405365)
                  ·
                    refine ⟨905725445581791912413003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9661071419539113732405365 905725445581791912413003)
                    ·
                      rfl

theorem cell22_2645841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_2645841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645841 prefixEnd_2645841 := by exact prefixLift 2645841
  have htrace : WordTrace (prefixWord ++ tailWord_2645841) baseStart_2645841 baseEnd_2645841 := by
    simpa [prefixWord, tailWord_2645841, baseEnd_2645841] using wordTrace_append hprefix tailTrace_2645841
  have hstable : (prefixWord ++ tailWord_2645841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645841).length < 2 ^ (prefixWord ++ tailWord_2645841).sum := by decide
  have hdescent : baseEnd_2645841 < baseStart_2645841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645845 : List Nat := [1, 3, 2, 2, 2, 3, 3, 1, 1, 4]
def baseStart_2645845 : Nat := 118140960795 + 2645845 * 2 ^ 59
def prefixEnd_2645845 : Nat := 4983230072969 + 3 ^ 40 * 2645845 * 2
def baseEnd_2645845 : Nat := 905726814863537235312991

theorem tailTrace_2645845 : CollatzResearch.WordTrace tailWord_2645845 prefixEnd_2645845 905726814863537235312991 := by
  unfold tailWord_2645845
  simp only [CollatzResearch.WordTrace]
  refine ⟨96501895099562914195554989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64334596733041942797036659 96501895099562914195554989)
  ·
    refine ⟨36188210662336092823333121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96501895099562914195554989 36188210662336092823333121)
    ·
      refine ⟨27141157996752069617499841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36188210662336092823333121 27141157996752069617499841)
      ·
        refine ⟨20355868497564052213124881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27141157996752069617499841 20355868497564052213124881)
        ·
          refine ⟨15266901373173039159843661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20355868497564052213124881 15266901373173039159843661)
          ·
            refine ⟨5725088014939889684941373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15266901373173039159843661 5725088014939889684941373)
            ·
              refine ⟨2146908005602458631853015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5725088014939889684941373 2146908005602458631853015)
              ·
                refine ⟨3220362008403687947779523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2146908005602458631853015 3220362008403687947779523)
                ·
                  refine ⟨4830543012605531921669285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3220362008403687947779523 4830543012605531921669285)
                  ·
                    refine ⟨905726814863537235312991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4830543012605531921669285 905726814863537235312991)
                    ·
                      rfl

theorem cell22_2645845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_2645845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645845 prefixEnd_2645845 := by exact prefixLift 2645845
  have htrace : WordTrace (prefixWord ++ tailWord_2645845) baseStart_2645845 baseEnd_2645845 := by
    simpa [prefixWord, tailWord_2645845, baseEnd_2645845] using wordTrace_append hprefix tailTrace_2645845
  have hstable : (prefixWord ++ tailWord_2645845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645845).length < 2 ^ (prefixWord ++ tailWord_2645845).sum := by decide
  have hdescent : baseEnd_2645845 < baseStart_2645845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645860 : List Nat := [2, 3, 1, 1, 5, 1, 1, 4, 4]
def baseStart_2645860 : Nat := 118140960795 + 2645860 * 2 ^ 59
def prefixEnd_2645860 : Nat := 4983230072969 + 3 ^ 40 * 2645860 * 2
def baseEnd_2645860 : Nat := 301910649890027398729315

theorem tailTrace_2645860 : CollatzResearch.WordTrace tailWord_2645860 prefixEnd_2645860 301910649890027398729315 := by
  unfold tailWord_2645860
  simp only [CollatzResearch.WordTrace]
  refine ⟨48251221097254285878675517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64334961463005714504900689 48251221097254285878675517)
  ·
    refine ⟨18094207911470357204503319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48251221097254285878675517 18094207911470357204503319)
    ·
      refine ⟨27141311867205535806754979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18094207911470357204503319 27141311867205535806754979)
      ·
        refine ⟨40711967800808303710132469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27141311867205535806754979 40711967800808303710132469)
        ·
          refine ⟨3816746981325778472824919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40711967800808303710132469 3816746981325778472824919)
          ·
            refine ⟨5725120471988667709237379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3816746981325778472824919 5725120471988667709237379)
            ·
              refine ⟨8587680707983001563856069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5725120471988667709237379 8587680707983001563856069)
              ·
                refine ⟨1610190132746812793223013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8587680707983001563856069 1610190132746812793223013)
                ·
                  refine ⟨301910649890027398729315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1610190132746812793223013 301910649890027398729315)
                  ·
                    rfl

theorem cell22_2645860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_2645860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645860 prefixEnd_2645860 := by exact prefixLift 2645860
  have htrace : WordTrace (prefixWord ++ tailWord_2645860) baseStart_2645860 baseEnd_2645860 := by
    simpa [prefixWord, tailWord_2645860, baseEnd_2645860] using wordTrace_append hprefix tailTrace_2645860
  have hstable : (prefixWord ++ tailWord_2645860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645860).length < 2 ^ (prefixWord ++ tailWord_2645860).sum := by decide
  have hdescent : baseEnd_2645860 < baseStart_2645860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645963 : List Nat := [1, 1, 1, 1, 3, 4, 1, 5, 1, 4]
def baseStart_2645963 : Nat := 118140960795 + 2645963 * 2 ^ 59
def prefixEnd_2645963 : Nat := 4983230072969 + 3 ^ 40 * 2645963 * 2
def baseEnd_2645963 : Nat := 905767208675024260862629

theorem tailTrace_2645963 : CollatzResearch.WordTrace tailWord_2645963 prefixEnd_2645963 905767208675024260862629 := by
  unfold tailWord_2645963
  simp only [CollatzResearch.WordTrace]
  refine ⟨96506198913135420348350543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64337465942090280232233695 96506198913135420348350543)
  ·
    refine ⟨144759298369703130522525815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96506198913135420348350543 144759298369703130522525815)
    ·
      refine ⟨217138947554554695783788723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144759298369703130522525815 217138947554554695783788723)
      ·
        refine ⟨325708421331832043675683085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217138947554554695783788723 325708421331832043675683085)
        ·
          refine ⟨122140657999437016378381157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 325708421331832043675683085 122140657999437016378381157)
          ·
            refine ⟨22901373374894440570946467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122140657999437016378381157 22901373374894440570946467)
            ·
              refine ⟨34352060062341660856419701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22901373374894440570946467 34352060062341660856419701)
              ·
                refine ⟨3220505630844530705289347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34352060062341660856419701 3220505630844530705289347)
                ·
                  refine ⟨4830758446266796057934021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3220505630844530705289347 4830758446266796057934021)
                  ·
                    refine ⟨905767208675024260862629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4830758446266796057934021 905767208675024260862629)
                    ·
                      rfl

theorem cell22_2645963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 4].length) (baseStart_2645963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645963 prefixEnd_2645963 := by exact prefixLift 2645963
  have htrace : WordTrace (prefixWord ++ tailWord_2645963) baseStart_2645963 baseEnd_2645963 := by
    simpa [prefixWord, tailWord_2645963, baseEnd_2645963] using wordTrace_append hprefix tailTrace_2645963
  have hstable : (prefixWord ++ tailWord_2645963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645963).length < 2 ^ (prefixWord ++ tailWord_2645963).sum := by decide
  have hdescent : baseEnd_2645963 < baseStart_2645963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645997 : List Nat := [1, 5, 1, 4, 1, 1, 1, 1, 3, 4]
def baseStart_2645997 : Nat := 118140960795 + 2645997 * 2 ^ 59
def prefixEnd_2645997 : Nat := 4983230072969 + 3 ^ 40 * 2645997 * 2
def baseEnd_2645997 : Nat := 905778847569859505512525

theorem tailTrace_2645997 : CollatzResearch.WordTrace tailWord_2645997 prefixEnd_2645997 905778847569859505512525 := by
  unfold tailWord_2645997
  simp only [CollatzResearch.WordTrace]
  refine ⟨96507438995012244155088245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64338292663341496103392163 96507438995012244155088245)
  ·
    refine ⟨9047572405782397889539523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96507438995012244155088245 9047572405782397889539523)
    ·
      refine ⟨13571358608673596834309285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9047572405782397889539523 13571358608673596834309285)
      ·
        refine ⟨2544629739126299406432991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13571358608673596834309285 2544629739126299406432991)
        ·
          refine ⟨3816944608689449109649487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2544629739126299406432991 3816944608689449109649487)
          ·
            refine ⟨5725416913034173664474231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3816944608689449109649487 5725416913034173664474231)
            ·
              refine ⟨8588125369551260496711347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5725416913034173664474231 8588125369551260496711347)
              ·
                refine ⟨12882188054326890745067021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8588125369551260496711347 12882188054326890745067021)
                ·
                  refine ⟨4830820520372584029400133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12882188054326890745067021 4830820520372584029400133)
                  ·
                    refine ⟨905778847569859505512525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4830820520372584029400133 905778847569859505512525)
                    ·
                      rfl

theorem cell22_2645997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_2645997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2645997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2645997 prefixEnd_2645997 := by exact prefixLift 2645997
  have htrace : WordTrace (prefixWord ++ tailWord_2645997) baseStart_2645997 baseEnd_2645997 := by
    simpa [prefixWord, tailWord_2645997, baseEnd_2645997] using wordTrace_append hprefix tailTrace_2645997
  have hstable : (prefixWord ++ tailWord_2645997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645997).length < 2 ^ (prefixWord ++ tailWord_2645997).sum := by decide
  have hdescent : baseEnd_2645997 < baseStart_2645997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646008 : List Nat := [2, 1, 2, 1, 1, 3, 3, 3, 2, 4]
def baseStart_2646008 : Nat := 118140960795 + 2646008 * 2 ^ 59
def prefixEnd_2646008 : Nat := 4983230072969 + 3 ^ 40 * 2646008 * 2
def baseEnd_2646008 : Nat := 905782613094659143487491

theorem tailTrace_2646008 : CollatzResearch.WordTrace tailWord_2646008 prefixEnd_2646008 905782613094659143487491 := by
  unfold tailWord_2646008
  simp only [CollatzResearch.WordTrace]
  refine ⟨48253920098986196516869339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64338560131981595355825785 48253920098986196516869339)
  ·
    refine ⟨72380880148479294775304009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48253920098986196516869339 72380880148479294775304009)
    ·
      refine ⟨54285660111359471081478007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72380880148479294775304009 54285660111359471081478007)
      ·
        refine ⟨81428490167039206622217011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54285660111359471081478007 81428490167039206622217011)
        ·
          refine ⟨122142735250558809933325517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81428490167039206622217011 122142735250558809933325517)
          ·
            refine ⟨45803525718959553724997069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122142735250558809933325517 45803525718959553724997069)
            ·
              refine ⟨17176322144609832646873901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45803525718959553724997069 17176322144609832646873901)
              ·
                refine ⟨6441120804228687242577713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17176322144609832646873901 6441120804228687242577713)
                ·
                  refine ⟨4830840603171515431933285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6441120804228687242577713 4830840603171515431933285)
                  ·
                    refine ⟨905782613094659143487491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4830840603171515431933285 905782613094659143487491)
                    ·
                      rfl

theorem cell22_2646008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_2646008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646008 prefixEnd_2646008 := by exact prefixLift 2646008
  have htrace : WordTrace (prefixWord ++ tailWord_2646008) baseStart_2646008 baseEnd_2646008 := by
    simpa [prefixWord, tailWord_2646008, baseEnd_2646008] using wordTrace_append hprefix tailTrace_2646008
  have hstable : (prefixWord ++ tailWord_2646008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646008).length < 2 ^ (prefixWord ++ tailWord_2646008).sum := by decide
  have hdescent : baseEnd_2646008 < baseStart_2646008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646014 : List Nat := [4, 2, 2, 2, 1, 2, 3, 1, 1, 4]
def baseStart_2646014 : Nat := 118140960795 + 2646014 * 2 ^ 59
def prefixEnd_2646014 : Nat := 4983230072969 + 3 ^ 40 * 2646014 * 2
def baseEnd_2646014 : Nat := 905784667017277127837473

theorem tailTrace_2646014 : CollatzResearch.WordTrace tailWord_2646014 prefixEnd_2646014 905784667017277127837473 := by
  unfold tailWord_2646014
  simp only [CollatzResearch.WordTrace]
  refine ⟨12063507379493832007307137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64338706023967104038971397 12063507379493832007307137)
  ·
    refine ⟨9047630534620374005480353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12063507379493832007307137 9047630534620374005480353)
    ·
      refine ⟨6785722900965280504110265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9047630534620374005480353 6785722900965280504110265)
      ·
        refine ⟨5089292175723960378082699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6785722900965280504110265 5089292175723960378082699)
        ·
          refine ⟨7633938263585940567124049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5089292175723960378082699 7633938263585940567124049)
          ·
            refine ⟨5725453697689455425343037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7633938263585940567124049 5725453697689455425343037)
            ·
              refine ⟨2147045136633545784503639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5725453697689455425343037 2147045136633545784503639)
              ·
                refine ⟨3220567704950318676755459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2147045136633545784503639 3220567704950318676755459)
                ·
                  refine ⟨4830851557425478015133189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3220567704950318676755459 4830851557425478015133189)
                  ·
                    refine ⟨905784667017277127837473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4830851557425478015133189 905784667017277127837473)
                    ·
                      rfl

theorem cell22_2646014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_2646014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646014 prefixEnd_2646014 := by exact prefixLift 2646014
  have htrace : WordTrace (prefixWord ++ tailWord_2646014) baseStart_2646014 baseEnd_2646014 := by
    simpa [prefixWord, tailWord_2646014, baseEnd_2646014] using wordTrace_append hprefix tailTrace_2646014
  have hstable : (prefixWord ++ tailWord_2646014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646014).length < 2 ^ (prefixWord ++ tailWord_2646014).sum := by decide
  have hdescent : baseEnd_2646014 < baseStart_2646014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646022 : List Nat := [6, 2, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_2646022 : Nat := 118140960795 + 2646022 * 2 ^ 59
def prefixEnd_2646022 : Nat := 4983230072969 + 3 ^ 40 * 2646022 * 2
def baseEnd_2646022 : Nat := 905787405580767773637449

theorem tailTrace_2646022 : CollatzResearch.WordTrace tailWord_2646022 prefixEnd_2646022 905787405580767773637449 := by
  unfold tailWord_2646022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3015885963122552294523385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 64338900546614448949832213 3015885963122552294523385)
  ·
    refine ⟨2261914472341914220892539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3015885963122552294523385 2261914472341914220892539)
    ·
      refine ⟨3392871708512871331338809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2261914472341914220892539 3392871708512871331338809)
      ·
        refine ⟨2544653781384653498504107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3392871708512871331338809 2544653781384653498504107)
        ·
          refine ⟨3816980672076980247756161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2544653781384653498504107 3816980672076980247756161)
          ·
            refine ⟨2862735504057735185817121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3816980672076980247756161 2862735504057735185817121)
            ·
              refine ⟨2147051628043301389362841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2862735504057735185817121 2147051628043301389362841)
              ·
                refine ⟨1610288721032476042022131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2147051628043301389362841 1610288721032476042022131)
                ·
                  refine ⟨2415433081548714063033197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1610288721032476042022131 2415433081548714063033197)
                  ·
                    refine ⟨905787405580767773637449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2415433081548714063033197 905787405580767773637449)
                    ·
                      rfl

theorem cell22_2646022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_2646022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646022 prefixEnd_2646022 := by exact prefixLift 2646022
  have htrace : WordTrace (prefixWord ++ tailWord_2646022) baseStart_2646022 baseEnd_2646022 := by
    simpa [prefixWord, tailWord_2646022, baseEnd_2646022] using wordTrace_append hprefix tailTrace_2646022
  have hstable : (prefixWord ++ tailWord_2646022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646022).length < 2 ^ (prefixWord ++ tailWord_2646022).sum := by decide
  have hdescent : baseEnd_2646022 < baseStart_2646022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646115 : List Nat := [1, 1, 1, 5, 1, 1, 3, 4, 1, 4]
def baseStart_2646115 : Nat := 118140960795 + 2646115 * 2 ^ 59
def prefixEnd_2646115 : Nat := 4983230072969 + 3 ^ 40 * 2646115 * 2
def baseEnd_2646115 : Nat := 905819241381346531062163

theorem tailTrace_2646115 : CollatzResearch.WordTrace tailWord_2646115 prefixEnd_2646115 905819241381346531062163 := by
  unfold tailWord_2646115
  simp only [CollatzResearch.WordTrace]
  refine ⟨96511742808584750307883799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64341161872389833538589199 96511742808584750307883799)
  ·
    refine ⟨144767614212877125461825699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96511742808584750307883799 144767614212877125461825699)
    ·
      refine ⟨217151421319315688192738549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144767614212877125461825699 217151421319315688192738549)
      ·
        refine ⟨20357945748685845768069239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 217151421319315688192738549 20357945748685845768069239)
        ·
          refine ⟨30536918623028768652103859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20357945748685845768069239 30536918623028768652103859)
          ·
            refine ⟨45805377934543152978155789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30536918623028768652103859 45805377934543152978155789)
            ·
              refine ⟨17177016725453682366808421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45805377934543152978155789 17177016725453682366808421)
              ·
                refine ⟨3220690636022565443776579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17177016725453682366808421 3220690636022565443776579)
                ·
                  refine ⟨4831035954033848165664869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3220690636022565443776579 4831035954033848165664869)
                  ·
                    refine ⟨905819241381346531062163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4831035954033848165664869 905819241381346531062163)
                    ·
                      rfl

theorem cell22_2646115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 4].length) (baseStart_2646115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646115 prefixEnd_2646115 := by exact prefixLift 2646115
  have htrace : WordTrace (prefixWord ++ tailWord_2646115) baseStart_2646115 baseEnd_2646115 := by
    simpa [prefixWord, tailWord_2646115, baseEnd_2646115] using wordTrace_append hprefix tailTrace_2646115
  have hstable : (prefixWord ++ tailWord_2646115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646115).length < 2 ^ (prefixWord ++ tailWord_2646115).sum := by decide
  have hdescent : baseEnd_2646115 < baseStart_2646115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646175 : List Nat := [1, 1, 2, 6, 1, 1, 2, 8]
def baseStart_2646175 : Nat := 118140960795 + 2646175 * 2 ^ 59
def prefixEnd_2646175 : Nat := 4983230072969 + 3 ^ 40 * 2646175 * 2
def baseEnd_2646175 : Nat := 100648864511947374951331

theorem tailTrace_2646175 : CollatzResearch.WordTrace tailWord_2646175 prefixEnd_2646175 100648864511947374951331 := by
  unfold tailWord_2646175
  simp only [CollatzResearch.WordTrace]
  refine ⟨96513931188367380555067979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64342620792244920370045319 96513931188367380555067979)
  ·
    refine ⟨144770896782551070832601969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96513931188367380555067979 144770896782551070832601969)
    ·
      refine ⟨108578172586913303124451477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144770896782551070832601969 108578172586913303124451477)
      ·
        refine ⟨5089601840011561083958663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 108578172586913303124451477 5089601840011561083958663)
        ·
          refine ⟨7634402760017341625937995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5089601840011561083958663 7634402760017341625937995)
          ·
            refine ⟨11451604140026012438906993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7634402760017341625937995 11451604140026012438906993)
            ·
              refine ⟨8588703105019509329180245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11451604140026012438906993 8588703105019509329180245)
              ·
                refine ⟨100648864511947374951331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8588703105019509329180245 100648864511947374951331)
                ·
                  rfl

theorem cell22_2646175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 8].length) (baseStart_2646175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646175 prefixEnd_2646175 := by exact prefixLift 2646175
  have htrace : WordTrace (prefixWord ++ tailWord_2646175) baseStart_2646175 baseEnd_2646175 := by
    simpa [prefixWord, tailWord_2646175, baseEnd_2646175] using wordTrace_append hprefix tailTrace_2646175
  have hstable : (prefixWord ++ tailWord_2646175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646175).length < 2 ^ (prefixWord ++ tailWord_2646175).sum := by decide
  have hdescent : baseEnd_2646175 < baseStart_2646175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646177 : List Nat := [1, 2, 3, 3, 1, 3, 2, 1, 2, 4]
def baseStart_2646177 : Nat := 118140960795 + 2646177 * 2 ^ 59
def prefixEnd_2646177 : Nat := 4983230072969 + 3 ^ 40 * 2646177 * 2
def baseEnd_2646177 : Nat := 905840465248399036011973

theorem tailTrace_2646177 : CollatzResearch.WordTrace tailWord_2646177 prefixEnd_2646177 905840465248399036011973 := by
  unfold tailWord_2646177
  simp only [CollatzResearch.WordTrace]
  refine ⟨96514004134360134896640785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64342669422906756597760523 96514004134360134896640785)
  ·
    refine ⟨72385503100770101172480589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96514004134360134896640785 72385503100770101172480589)
    ·
      refine ⟨27144563662788787939680221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72385503100770101172480589 27144563662788787939680221)
      ·
        refine ⟨10179211373545795477380083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27144563662788787939680221 10179211373545795477380083)
        ·
          refine ⟨15268817060318693216070125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10179211373545795477380083 15268817060318693216070125)
          ·
            refine ⟨5725806397619509956026297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15268817060318693216070125 5725806397619509956026297)
            ·
              refine ⟨4294354798214632467019723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5725806397619509956026297 4294354798214632467019723)
              ·
                refine ⟨6441532197321948700529585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4294354798214632467019723 6441532197321948700529585)
                ·
                  refine ⟨4831149147991461525397189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6441532197321948700529585 4831149147991461525397189)
                  ·
                    refine ⟨905840465248399036011973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4831149147991461525397189 905840465248399036011973)
                    ·
                      rfl

theorem cell22_2646177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_2646177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646177 prefixEnd_2646177 := by exact prefixLift 2646177
  have htrace : WordTrace (prefixWord ++ tailWord_2646177) baseStart_2646177 baseEnd_2646177 := by
    simpa [prefixWord, tailWord_2646177, baseEnd_2646177] using wordTrace_append hprefix tailTrace_2646177
  have hstable : (prefixWord ++ tailWord_2646177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646177).length < 2 ^ (prefixWord ++ tailWord_2646177).sum := by decide
  have hdescent : baseEnd_2646177 < baseStart_2646177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646209 : List Nat := [1, 2, 6, 1, 2, 2, 1, 7]
def baseStart_2646209 : Nat := 118140960795 + 2646209 * 2 ^ 59
def prefixEnd_2646209 : Nat := 4983230072969 + 3 ^ 40 * 2646209 * 2
def baseEnd_2646209 : Nat := 100650157722484624356875

theorem tailTrace_2646209 : CollatzResearch.WordTrace tailWord_2646209 prefixEnd_2646209 100650157722484624356875 := by
  unfold tailWord_2646209
  simp only [CollatzResearch.WordTrace]
  refine ⟨96515171270244204361805681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64343447513496136241203787 96515171270244204361805681)
  ·
    refine ⟨72386378452683153271354261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96515171270244204361805681 72386378452683153271354261)
    ·
      refine ⟨3393111489969522809594731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 72386378452683153271354261 3393111489969522809594731)
      ·
        refine ⟨5089667234954284214392097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3393111489969522809594731 5089667234954284214392097)
        ·
          refine ⟨3817250426215713160794073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5089667234954284214392097 3817250426215713160794073)
          ·
            refine ⟨2862937819661784870595555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3817250426215713160794073 2862937819661784870595555)
            ·
              refine ⟨4294406729492677305893333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2862937819661784870595555 4294406729492677305893333)
              ·
                refine ⟨100650157722484624356875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4294406729492677305893333 100650157722484624356875)
                ·
                  rfl

theorem cell22_2646209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 7].length) (baseStart_2646209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646209 prefixEnd_2646209 := by exact prefixLift 2646209
  have htrace : WordTrace (prefixWord ++ tailWord_2646209) baseStart_2646209 baseEnd_2646209 := by
    simpa [prefixWord, tailWord_2646209, baseEnd_2646209] using wordTrace_append hprefix tailTrace_2646209
  have hstable : (prefixWord ++ tailWord_2646209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646209).length < 2 ^ (prefixWord ++ tailWord_2646209).sum := by decide
  have hdescent : baseEnd_2646209 < baseStart_2646209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646355 : List Nat := [1, 1, 1, 2, 1, 1, 4, 4, 7]
def baseStart_2646355 : Nat := 118140960795 + 2646355 * 2 ^ 59
def prefixEnd_2646355 : Nat := 4983230072969 + 3 ^ 40 * 2646355 * 2
def baseEnd_2646355 : Nat := 301967132762021968353809

theorem tailTrace_2646355 : CollatzResearch.WordTrace tailWord_2646355 prefixEnd_2646355 301967132762021968353809 := by
  unfold tailWord_2646355
  simp only [CollatzResearch.WordTrace]
  refine ⟨96520496327715271296620519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64346997551810180864413679 96520496327715271296620519)
  ·
    refine ⟨144780744491572906944930779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96520496327715271296620519 144780744491572906944930779)
    ·
      refine ⟨217171116737359360417396169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144780744491572906944930779 217171116737359360417396169)
      ·
        refine ⟨162878337553019520313047127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217171116737359360417396169 162878337553019520313047127)
        ·
          refine ⟨244317506329529280469570691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162878337553019520313047127 244317506329529280469570691)
          ·
            refine ⟨366476259494293920704356037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244317506329529280469570691 366476259494293920704356037)
            ·
              refine ⟨68714298655180110132066757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 366476259494293920704356037 68714298655180110132066757)
              ·
                refine ⟨12883930997846270649762517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68714298655180110132066757 12883930997846270649762517)
                ·
                  refine ⟨301967132762021968353809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12883930997846270649762517 301967132762021968353809)
                  ·
                    rfl

theorem cell22_2646355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 7].length) (baseStart_2646355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646355 prefixEnd_2646355 := by exact prefixLift 2646355
  have htrace : WordTrace (prefixWord ++ tailWord_2646355) baseStart_2646355 baseEnd_2646355 := by
    simpa [prefixWord, tailWord_2646355, baseEnd_2646355] using wordTrace_append hprefix tailTrace_2646355
  have hstable : (prefixWord ++ tailWord_2646355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646355).length < 2 ^ (prefixWord ++ tailWord_2646355).sum := by decide
  have hdescent : baseEnd_2646355 < baseStart_2646355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646389 : List Nat := [1, 3, 4, 1, 2, 1, 2, 3, 5]
def baseStart_2646389 : Nat := 118140960795 + 2646389 * 2 ^ 59
def prefixEnd_2646389 : Nat := 4983230072969 + 3 ^ 40 * 2646389 * 2
def baseEnd_2646389 : Nat := 301971012393633716570441

theorem tailTrace_2646389 : CollatzResearch.WordTrace tailWord_2646389 prefixEnd_2646389 301971012393633716570441 := by
  unfold tailWord_2646389
  simp only [CollatzResearch.WordTrace]
  refine ⟨96521736409592095103358221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64347824273061396735572147 96521736409592095103358221)
  ·
    refine ⟨36195651153597035663759333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96521736409592095103358221 36195651153597035663759333)
    ·
      refine ⟨6786684591299444186954875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36195651153597035663759333 6786684591299444186954875)
      ·
        refine ⟨10180026886949166280432313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6786684591299444186954875 10180026886949166280432313)
        ·
          refine ⟨7635020165211874710324235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10180026886949166280432313 7635020165211874710324235)
          ·
            refine ⟨11452530247817812065486353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7635020165211874710324235 11452530247817812065486353)
            ·
              refine ⟨8589397685863359049114765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11452530247817812065486353 8589397685863359049114765)
              ·
                refine ⟨3221024132198759643418037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8589397685863359049114765 3221024132198759643418037)
                ·
                  refine ⟨301971012393633716570441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3221024132198759643418037 301971012393633716570441)
                  ·
                    rfl

theorem cell22_2646389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 5].length) (baseStart_2646389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646389 prefixEnd_2646389 := by exact prefixLift 2646389
  have htrace : WordTrace (prefixWord ++ tailWord_2646389) baseStart_2646389 baseEnd_2646389 := by
    simpa [prefixWord, tailWord_2646389, baseEnd_2646389] using wordTrace_append hprefix tailTrace_2646389
  have hstable : (prefixWord ++ tailWord_2646389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646389).length < 2 ^ (prefixWord ++ tailWord_2646389).sum := by decide
  have hdescent : baseEnd_2646389 < baseStart_2646389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646410 : List Nat := [3, 1, 2, 5, 1, 1, 2, 3, 1, 3]
def baseStart_2646410 : Nat := 118140960795 + 2646410 * 2 ^ 59
def prefixEnd_2646410 : Nat := 4983230072969 + 3 ^ 40 * 2646410 * 2
def baseEnd_2646410 : Nat := 905920225910064094936259

theorem tailTrace_2646410 : CollatzResearch.WordTrace tailWord_2646410 prefixEnd_2646410 905920225910064094936259 := by
  unfold tailWord_2646410
  simp only [CollatzResearch.WordTrace]
  refine ⟨24130625585629003922468171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64348334895010677126581789 24130625585629003922468171)
  ·
    refine ⟨36195938378443505883702257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24130625585629003922468171 36195938378443505883702257)
    ·
      refine ⟨27146953783832629412776693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36195938378443505883702257 27146953783832629412776693)
      ·
        refine ⟨2545026917234309007447815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27146953783832629412776693 2545026917234309007447815)
        ·
          refine ⟨3817540375851463511171723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2545026917234309007447815 3817540375851463511171723)
          ·
            refine ⟨5726310563777195266757585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3817540375851463511171723 5726310563777195266757585)
            ·
              refine ⟨4294732922832896450068189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5726310563777195266757585 4294732922832896450068189)
              ·
                refine ⟨1610524846062336168775571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4294732922832896450068189 1610524846062336168775571)
                ·
                  refine ⟨2415787269093504253163357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1610524846062336168775571 2415787269093504253163357)
                  ·
                    refine ⟨905920225910064094936259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2415787269093504253163357 905920225910064094936259)
                    ·
                      rfl

theorem cell22_2646410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_2646410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646410 prefixEnd_2646410 := by exact prefixLift 2646410
  have htrace : WordTrace (prefixWord ++ tailWord_2646410) baseStart_2646410 baseEnd_2646410 := by
    simpa [prefixWord, tailWord_2646410, baseEnd_2646410] using wordTrace_append hprefix tailTrace_2646410
  have hstable : (prefixWord ++ tailWord_2646410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646410).length < 2 ^ (prefixWord ++ tailWord_2646410).sum := by decide
  have hdescent : baseEnd_2646410 < baseStart_2646410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646434 : List Nat := [3, 3, 1, 2, 1, 1, 4, 1, 6]
def baseStart_2646434 : Nat := 118140960795 + 2646434 * 2 ^ 59
def prefixEnd_2646434 : Nat := 4983230072969 + 3 ^ 40 * 2646434 * 2
def baseEnd_2646434 : Nat := 301976147200178677445395

theorem tailTrace_2646434 : CollatzResearch.WordTrace tailWord_2646434 prefixEnd_2646434 301976147200178677445395 := by
  unfold tailWord_2646434
  simp only [CollatzResearch.WordTrace]
  refine ⟨24130844423607266947186589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64348918462952711859164237 24130844423607266947186589)
  ·
    refine ⟨9049066658852725105194971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24130844423607266947186589 9049066658852725105194971)
    ·
      refine ⟨13573599988279087657792457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9049066658852725105194971 13573599988279087657792457)
      ·
        refine ⟨10180199991209315743344343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13573599988279087657792457 10180199991209315743344343)
        ·
          refine ⟨15270299986813973615016515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10180199991209315743344343 15270299986813973615016515)
          ·
            refine ⟨22905449980220960422524773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15270299986813973615016515 22905449980220960422524773)
            ·
              refine ⟨4294771871291430079223395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22905449980220960422524773 4294771871291430079223395)
              ·
                refine ⟨6442157806937145118835093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4294771871291430079223395 6442157806937145118835093)
                ·
                  refine ⟨301976147200178677445395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6442157806937145118835093 301976147200178677445395)
                  ·
                    rfl

theorem cell22_2646434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_2646434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646434 prefixEnd_2646434 := by exact prefixLift 2646434
  have htrace : WordTrace (prefixWord ++ tailWord_2646434) baseStart_2646434 baseEnd_2646434 := by
    simpa [prefixWord, tailWord_2646434, baseEnd_2646434] using wordTrace_append hprefix tailTrace_2646434
  have hstable : (prefixWord ++ tailWord_2646434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646434).length < 2 ^ (prefixWord ++ tailWord_2646434).sum := by decide
  have hdescent : baseEnd_2646434 < baseStart_2646434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646449 : List Nat := [1, 2, 2, 4, 1, 2, 3, 1, 1, 5]
def baseStart_2646449 : Nat := 118140960795 + 2646449 * 2 ^ 59
def prefixEnd_2646449 : Nat := 4983230072969 + 3 ^ 40 * 2646449 * 2
def baseEnd_2646449 : Nat := 905933576407080993211139

theorem tailTrace_2646449 : CollatzResearch.WordTrace tailWord_2646449 prefixEnd_2646449 905933576407080993211139 := by
  unfold tailWord_2646449
  simp only [CollatzResearch.WordTrace]
  refine ⟨96523924789374725350542401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64349283192916483567028267 96523924789374725350542401)
  ·
    refine ⟨72392943592031044012906801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96523924789374725350542401 72392943592031044012906801)
    ·
      refine ⟨54294707694023283009680101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72392943592031044012906801 54294707694023283009680101)
      ·
        refine ⟨10180257692629365564315019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54294707694023283009680101 10180257692629365564315019)
        ·
          refine ⟨15270386538944048346472529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10180257692629365564315019 15270386538944048346472529)
          ·
            refine ⟨11452789904208036259854397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15270386538944048346472529 11452789904208036259854397)
            ·
              refine ⟨4294796214078013597445399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11452789904208036259854397 4294796214078013597445399)
              ·
                refine ⟨6442194321117020396168099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4294796214078013597445399 6442194321117020396168099)
                ·
                  refine ⟨9663291481675530594252149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6442194321117020396168099 9663291481675530594252149)
                  ·
                    refine ⟨905933576407080993211139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9663291481675530594252149 905933576407080993211139)
                    ·
                      rfl

theorem cell22_2646449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_2646449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646449 prefixEnd_2646449 := by exact prefixLift 2646449
  have htrace : WordTrace (prefixWord ++ tailWord_2646449) baseStart_2646449 baseEnd_2646449 := by
    simpa [prefixWord, tailWord_2646449, baseEnd_2646449] using wordTrace_append hprefix tailTrace_2646449
  have hstable : (prefixWord ++ tailWord_2646449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646449).length < 2 ^ (prefixWord ++ tailWord_2646449).sum := by decide
  have hdescent : baseEnd_2646449 < baseStart_2646449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646522 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 3, 7]
def baseStart_2646522 : Nat := 118140960795 + 2646522 * 2 ^ 59
def prefixEnd_2646522 : Nat := 4983230072969 + 3 ^ 40 * 2646522 * 2
def baseEnd_2646522 : Nat := 905958565798933136135915

theorem tailTrace_2646522 : CollatzResearch.WordTrace tailWord_2646522 prefixEnd_2646522 905958565798933136135915 := by
  unfold tailWord_2646522
  simp only [CollatzResearch.WordTrace]
  refine ⟨24131646829527564704487455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64351058212073505878633213 24131646829527564704487455)
  ·
    refine ⟨36197470244291347056731183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24131646829527564704487455 36197470244291347056731183)
    ·
      refine ⟨54296205366437020585096775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36197470244291347056731183 54296205366437020585096775)
      ·
        refine ⟨81444308049655530877645163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54296205366437020585096775 81444308049655530877645163)
        ·
          refine ⟨122166462074483296316467745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81444308049655530877645163 122166462074483296316467745)
          ·
            refine ⟨91624846555862472237350809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122166462074483296316467745 91624846555862472237350809)
            ·
              refine ⟨68718634916896854178013107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91624846555862472237350809 68718634916896854178013107)
              ·
                refine ⟨103077952375345281267019661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68718634916896854178013107 103077952375345281267019661)
                ·
                  refine ⟨38654232140754480475132373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103077952375345281267019661 38654232140754480475132373)
                  ·
                    refine ⟨905958565798933136135915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38654232140754480475132373 905958565798933136135915)
                    ·
                      rfl

theorem cell22_2646522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_2646522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646522 prefixEnd_2646522 := by exact prefixLift 2646522
  have htrace : WordTrace (prefixWord ++ tailWord_2646522) baseStart_2646522 baseEnd_2646522 := by
    simpa [prefixWord, tailWord_2646522, baseEnd_2646522] using wordTrace_append hprefix tailTrace_2646522
  have hstable : (prefixWord ++ tailWord_2646522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646522).length < 2 ^ (prefixWord ++ tailWord_2646522).sum := by decide
  have hdescent : baseEnd_2646522 < baseStart_2646522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646554 : List Nat := [3, 1, 1, 3, 1, 1, 3, 2, 3, 4]
def baseStart_2646554 : Nat := 118140960795 + 2646554 * 2 ^ 59
def prefixEnd_2646554 : Nat := 4983230072969 + 3 ^ 40 * 2646554 * 2
def baseEnd_2646554 : Nat := 905969520052895719335817

theorem tailTrace_2646554 : CollatzResearch.WordTrace tailWord_2646554 prefixEnd_2646554 905969520052895719335817 := by
  unfold tailWord_2646554
  simp only [CollatzResearch.WordTrace]
  refine ⟨24131938613498582070778679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64351836302662885522076477 24131938613498582070778679)
  ·
    refine ⟨36197907920247873106168019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24131938613498582070778679 36197907920247873106168019)
    ·
      refine ⟨54296861880371809659252029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36197907920247873106168019 54296861880371809659252029)
      ·
        refine ⟨20361323205139428622219511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54296861880371809659252029 20361323205139428622219511)
        ·
          refine ⟨30541984807709142933329267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20361323205139428622219511 30541984807709142933329267)
          ·
            refine ⟨45812977211563714399993901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30541984807709142933329267 45812977211563714399993901)
            ·
              refine ⟨17179866454336392899997713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45812977211563714399993901 17179866454336392899997713)
              ·
                refine ⟨12884899840752294674998285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17179866454336392899997713 12884899840752294674998285)
                ·
                  refine ⟨4831837440282110503124357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12884899840752294674998285 4831837440282110503124357)
                  ·
                    refine ⟨905969520052895719335817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4831837440282110503124357 905969520052895719335817)
                    ·
                      rfl

theorem cell22_2646554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_2646554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646554 prefixEnd_2646554 := by exact prefixLift 2646554
  have htrace : WordTrace (prefixWord ++ tailWord_2646554) baseStart_2646554 baseEnd_2646554 := by
    simpa [prefixWord, tailWord_2646554, baseEnd_2646554] using wordTrace_append hprefix tailTrace_2646554
  have hstable : (prefixWord ++ tailWord_2646554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646554).length < 2 ^ (prefixWord ++ tailWord_2646554).sum := by decide
  have hdescent : baseEnd_2646554 < baseStart_2646554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646584 : List Nat := [2, 1, 2, 1, 4, 1, 1, 4, 1, 5]
def baseStart_2646584 : Nat := 118140960795 + 2646584 * 2 ^ 59
def prefixEnd_2646584 : Nat := 4983230072969 + 3 ^ 40 * 2646584 * 2
def baseEnd_2646584 : Nat := 905979789665985641085725

theorem tailTrace_2646584 : CollatzResearch.WordTrace tailWord_2646584 prefixEnd_2646584 905979789665985641085725 := by
  unfold tailWord_2646584
  simp only [CollatzResearch.WordTrace]
  refine ⟨48264424321942821703353403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64352565762590428937804537 48264424321942821703353403)
  ·
    refine ⟨72396636482914232555030105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48264424321942821703353403 72396636482914232555030105)
    ·
      refine ⟨54297477362185674416272579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72396636482914232555030105 54297477362185674416272579)
      ·
        refine ⟨81446216043278511624408869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54297477362185674416272579 81446216043278511624408869)
        ·
          refine ⟨15271165508114720929576663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81446216043278511624408869 15271165508114720929576663)
          ·
            refine ⟨22906748262172081394364995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15271165508114720929576663 22906748262172081394364995)
            ·
              refine ⟨34360122393258122091547493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22906748262172081394364995 34360122393258122091547493)
              ·
                refine ⟨6442522948735897892165155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34360122393258122091547493 6442522948735897892165155)
                ·
                  refine ⟨9663784423103846838247733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6442522948735897892165155 9663784423103846838247733)
                  ·
                    refine ⟨905979789665985641085725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9663784423103846838247733 905979789665985641085725)
                    ·
                      rfl

theorem cell22_2646584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_2646584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646584 prefixEnd_2646584 := by exact prefixLift 2646584
  have htrace : WordTrace (prefixWord ++ tailWord_2646584) baseStart_2646584 baseEnd_2646584 := by
    simpa [prefixWord, tailWord_2646584, baseEnd_2646584] using wordTrace_append hprefix tailTrace_2646584
  have hstable : (prefixWord ++ tailWord_2646584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646584).length < 2 ^ (prefixWord ++ tailWord_2646584).sum := by decide
  have hdescent : baseEnd_2646584 < baseStart_2646584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646586 : List Nat := [3, 1, 1, 1, 3, 3, 1, 5, 4]
def baseStart_2646586 : Nat := 118140960795 + 2646586 * 2 ^ 59
def prefixEnd_2646586 : Nat := 4983230072969 + 3 ^ 40 * 2646586 * 2
def baseEnd_2646586 : Nat := 301993491435619434178573

theorem tailTrace_2646586 : CollatzResearch.WordTrace tailWord_2646586 prefixEnd_2646586 301993491435619434178573 := by
  unfold tailWord_2646586
  simp only [CollatzResearch.WordTrace]
  refine ⟨24132230397469599437069903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64352614393252265165519741 24132230397469599437069903)
  ·
    refine ⟨36198345596204399155604855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24132230397469599437069903 36198345596204399155604855)
    ·
      refine ⟨54297518394306598733407283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36198345596204399155604855 54297518394306598733407283)
      ·
        refine ⟨81446277591459898100110925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54297518394306598733407283 81446277591459898100110925)
        ·
          refine ⟨30542354096797461787541597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81446277591459898100110925 30542354096797461787541597)
          ·
            refine ⟨11453382786299048170328099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30542354096797461787541597 11453382786299048170328099)
            ·
              refine ⟨17180074179448572255492149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11453382786299048170328099 17180074179448572255492149)
              ·
                refine ⟨1610631954323303648952389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17180074179448572255492149 1610631954323303648952389)
                ·
                  refine ⟨301993491435619434178573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1610631954323303648952389 301993491435619434178573)
                  ·
                    rfl

theorem cell22_2646586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5, 4].length) (baseStart_2646586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646586 prefixEnd_2646586 := by exact prefixLift 2646586
  have htrace : WordTrace (prefixWord ++ tailWord_2646586) baseStart_2646586 baseEnd_2646586 := by
    simpa [prefixWord, tailWord_2646586, baseEnd_2646586] using wordTrace_append hprefix tailTrace_2646586
  have hstable : (prefixWord ++ tailWord_2646586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646586).length < 2 ^ (prefixWord ++ tailWord_2646586).sum := by decide
  have hdescent : baseEnd_2646586 < baseStart_2646586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646588 : List Nat := [2, 2, 2, 2, 3, 1, 4, 1, 1, 4]
def baseStart_2646588 : Nat := 118140960795 + 2646588 * 2 ^ 59
def prefixEnd_2646588 : Nat := 4983230072969 + 3 ^ 40 * 2646588 * 2
def baseEnd_2646588 : Nat := 905981158947730963985713

theorem tailTrace_2646588 : CollatzResearch.WordTrace tailWord_2646588 prefixEnd_2646588 905981158947730963985713 := by
  unfold tailWord_2646588
  simp only [CollatzResearch.WordTrace]
  refine ⟨48264497267935576044926209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64352663023914101393234945 48264497267935576044926209)
  ·
    refine ⟨36198372950951682033694657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48264497267935576044926209 36198372950951682033694657)
    ·
      refine ⟨27148779713213761525270993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36198372950951682033694657 27148779713213761525270993)
      ·
        refine ⟨20361584784910321143953245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27148779713213761525270993 20361584784910321143953245)
        ·
          refine ⟨7635594294341370428982467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20361584784910321143953245 7635594294341370428982467)
          ·
            refine ⟨11453391441512055643473701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7635594294341370428982467 11453391441512055643473701)
            ·
              refine ⟨2147510895283510433151319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11453391441512055643473701 2147510895283510433151319)
              ·
                refine ⟨3221266342925265649726979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2147510895283510433151319 3221266342925265649726979)
                ·
                  refine ⟨4831899514387898474590469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3221266342925265649726979 4831899514387898474590469)
                  ·
                    refine ⟨905981158947730963985713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4831899514387898474590469 905981158947730963985713)
                    ·
                      rfl

theorem cell22_2646588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_2646588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646588 prefixEnd_2646588 := by exact prefixLift 2646588
  have htrace : WordTrace (prefixWord ++ tailWord_2646588) baseStart_2646588 baseEnd_2646588 := by
    simpa [prefixWord, tailWord_2646588, baseEnd_2646588] using wordTrace_append hprefix tailTrace_2646588
  have hstable : (prefixWord ++ tailWord_2646588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646588).length < 2 ^ (prefixWord ++ tailWord_2646588).sum := by decide
  have hdescent : baseEnd_2646588 < baseStart_2646588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646659 : List Nat := [1, 1, 1, 3, 3, 1, 4, 1, 7]
def baseStart_2646659 : Nat := 118140960795 + 2646659 * 2 ^ 59
def prefixEnd_2646659 : Nat := 4983230072969 + 3 ^ 40 * 2646659 * 2
def baseEnd_2646659 : Nat := 302001821232903481820165

theorem tailTrace_2646659 : CollatzResearch.WordTrace tailWord_2646659 prefixEnd_2646659 302001821232903481820165 := by
  unfold tailWord_2646659
  simp only [CollatzResearch.WordTrace]
  refine ⟨96531584118613931215687031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64354389412409287477124687 96531584118613931215687031)
  ·
    refine ⟨144797376177920896823530547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96531584118613931215687031 144797376177920896823530547)
    ·
      refine ⟨217196064266881345235295821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144797376177920896823530547 217196064266881345235295821)
      ·
        refine ⟨81448524100080504463235933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217196064266881345235295821 81448524100080504463235933)
        ·
          refine ⟨30543196537530189173713475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81448524100080504463235933 30543196537530189173713475)
          ·
            refine ⟨45814794806295283760570213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30543196537530189173713475 45814794806295283760570213)
            ·
              refine ⟨8590274026180365705106915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45814794806295283760570213 8590274026180365705106915)
              ·
                refine ⟨12885411039270548557660373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8590274026180365705106915 12885411039270548557660373)
                ·
                  refine ⟨302001821232903481820165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12885411039270548557660373 302001821232903481820165)
                  ·
                    rfl

theorem cell22_2646659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 7].length) (baseStart_2646659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646659 prefixEnd_2646659 := by exact prefixLift 2646659
  have htrace : WordTrace (prefixWord ++ tailWord_2646659) baseStart_2646659 baseEnd_2646659 := by
    simpa [prefixWord, tailWord_2646659, baseEnd_2646659] using wordTrace_append hprefix tailTrace_2646659
  have hstable : (prefixWord ++ tailWord_2646659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646659).length < 2 ^ (prefixWord ++ tailWord_2646659).sum := by decide
  have hdescent : baseEnd_2646659 < baseStart_2646659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646738 : List Nat := [3, 2, 2, 2, 3, 1, 1, 2, 6]
def baseStart_2646738 : Nat := 118140960795 + 2646738 * 2 ^ 59
def prefixEnd_2646738 : Nat := 4983230072969 + 3 ^ 40 * 2646738 * 2
def baseEnd_2646738 : Nat := 302010835671060190911751

theorem tailTrace_2646738 : CollatzResearch.WordTrace tailWord_2646738 prefixEnd_2646738 302010835671060190911751 := by
  unfold tailWord_2646738
  simp only [CollatzResearch.WordTrace]
  refine ⟨24133616371331931926953217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64356310323551818471875245 24133616371331931926953217)
  ·
    refine ⟨18100212278498948945214913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24133616371331931926953217 18100212278498948945214913)
    ·
      refine ⟨13575159208874211708911185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18100212278498948945214913 13575159208874211708911185)
      ·
        refine ⟨10181369406655658781683389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13575159208874211708911185 10181369406655658781683389)
        ·
          refine ⟨3818013527495872043131271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10181369406655658781683389 3818013527495872043131271)
          ·
            refine ⟨5727020291243808064696907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3818013527495872043131271 5727020291243808064696907)
            ·
              refine ⟨8590530436865712097045361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5727020291243808064696907 8590530436865712097045361)
              ·
                refine ⟨6442897827649284072784021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8590530436865712097045361 6442897827649284072784021)
                ·
                  refine ⟨302010835671060190911751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6442897827649284072784021 302010835671060190911751)
                  ·
                    rfl

theorem cell22_2646738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_2646738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646738 prefixEnd_2646738 := by exact prefixLift 2646738
  have htrace : WordTrace (prefixWord ++ tailWord_2646738) baseStart_2646738 baseEnd_2646738 := by
    simpa [prefixWord, tailWord_2646738, baseEnd_2646738] using wordTrace_append hprefix tailTrace_2646738
  have hstable : (prefixWord ++ tailWord_2646738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646738).length < 2 ^ (prefixWord ++ tailWord_2646738).sum := by decide
  have hdescent : baseEnd_2646738 < baseStart_2646738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646751 : List Nat := [1, 1, 2, 3, 2, 4, 1, 1, 1, 6]
def baseStart_2646751 : Nat := 118140960795 + 2646751 * 2 ^ 59
def prefixEnd_2646751 : Nat := 4983230072969 + 3 ^ 40 * 2646751 * 2
def baseEnd_2646751 : Nat := 906036957178852872160213

theorem tailTrace_2646751 : CollatzResearch.WordTrace tailWord_2646751 prefixEnd_2646751 906036957178852872160213 := by
  unfold tailWord_2646751
  simp only [CollatzResearch.WordTrace]
  refine ⟨96534939634280630928036107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64356626422853753952024071 96534939634280630928036107)
  ·
    refine ⟨144802409451420946392054161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96534939634280630928036107 144802409451420946392054161)
    ·
      refine ⟨108601807088565709794040621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144802409451420946392054161 108601807088565709794040621)
      ·
        refine ⟨40725677658212141172765233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108601807088565709794040621 40725677658212141172765233)
        ·
          refine ⟨30544258243659105879573925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40725677658212141172765233 30544258243659105879573925)
          ·
            refine ⟨5727048420686082352420111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30544258243659105879573925 5727048420686082352420111)
            ·
              refine ⟨8590572631029123528630167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5727048420686082352420111 8590572631029123528630167)
              ·
                refine ⟨12885858946543685292945251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8590572631029123528630167 12885858946543685292945251)
                ·
                  refine ⟨19328788419815527939417877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12885858946543685292945251 19328788419815527939417877)
                  ·
                    refine ⟨906036957178852872160213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19328788419815527939417877 906036957178852872160213)
                    ·
                      rfl

theorem cell22_2646751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 6].length) (baseStart_2646751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646751 prefixEnd_2646751 := by exact prefixLift 2646751
  have htrace : WordTrace (prefixWord ++ tailWord_2646751) baseStart_2646751 baseEnd_2646751 := by
    simpa [prefixWord, tailWord_2646751, baseEnd_2646751] using wordTrace_append hprefix tailTrace_2646751
  have hstable : (prefixWord ++ tailWord_2646751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646751).length < 2 ^ (prefixWord ++ tailWord_2646751).sum := by decide
  have hdescent : baseEnd_2646751 < baseStart_2646751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646755 : List Nat := [1, 1, 1, 7, 1, 2, 2, 3, 4]
def baseStart_2646755 : Nat := 118140960795 + 2646755 * 2 ^ 59
def prefixEnd_2646755 : Nat := 4983230072969 + 3 ^ 40 * 2646755 * 2
def baseEnd_2646755 : Nat := 302012775486866065020067

theorem tailTrace_2646755 : CollatzResearch.WordTrace tailWord_2646755 prefixEnd_2646755 302012775486866065020067 := by
  unfold tailWord_2646755
  simp only [CollatzResearch.WordTrace]
  refine ⟨96535085526266139611181719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64356723684177426407454479 96535085526266139611181719)
  ·
    refine ⟨144802628289399209416772579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96535085526266139611181719 144802628289399209416772579)
    ·
      refine ⟨217203942434098814125158869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144802628289399209416772579 217203942434098814125158869)
      ·
        refine ⟨5090717400799190956058411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 217203942434098814125158869 5090717400799190956058411)
        ·
          refine ⟨7636076101198786434087617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5090717400799190956058411 7636076101198786434087617)
          ·
            refine ⟨5727057075899089825565713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7636076101198786434087617 5727057075899089825565713)
            ·
              refine ⟨4295292806924317369174285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5727057075899089825565713 4295292806924317369174285)
              ·
                refine ⟨1610734802596619013440357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4295292806924317369174285 1610734802596619013440357)
                ·
                  refine ⟨302012775486866065020067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1610734802596619013440357 302012775486866065020067)
                  ·
                    rfl

theorem cell22_2646755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3, 4].length) (baseStart_2646755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646755 prefixEnd_2646755 := by exact prefixLift 2646755
  have htrace : WordTrace (prefixWord ++ tailWord_2646755) baseStart_2646755 baseEnd_2646755 := by
    simpa [prefixWord, tailWord_2646755, baseEnd_2646755] using wordTrace_append hprefix tailTrace_2646755
  have hstable : (prefixWord ++ tailWord_2646755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646755).length < 2 ^ (prefixWord ++ tailWord_2646755).sum := by decide
  have hdescent : baseEnd_2646755 < baseStart_2646755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646766 : List Nat := [4, 1, 2, 1, 1, 4, 9]
def baseStart_2646766 : Nat := 118140960795 + 2646766 * 2 ^ 59
def prefixEnd_2646766 : Nat := 4983230072969 + 3 ^ 40 * 2646766 * 2
def baseEnd_2646766 : Nat := 33557114517977697519821

theorem tailTrace_2646766 : CollatzResearch.WordTrace tailWord_2646766 prefixEnd_2646766 33557114517977697519821 := by
  unfold tailWord_2646766
  simp only [CollatzResearch.WordTrace]
  refine ⟨12066935841153286061229019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64356991152817525659888101 12066935841153286061229019)
  ·
    refine ⟨18100403761729929091843529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12066935841153286061229019 18100403761729929091843529)
    ·
      refine ⟨13575302821297446818882647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18100403761729929091843529 13575302821297446818882647)
      ·
        refine ⟨20362954231946170228323971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13575302821297446818882647 20362954231946170228323971)
        ·
          refine ⟨30544431347919255342485957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20362954231946170228323971 30544431347919255342485957)
          ·
            refine ⟨5727080877734860376716117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30544431347919255342485957 5727080877734860376716117)
            ·
              refine ⟨33557114517977697519821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5727080877734860376716117 33557114517977697519821)
              ·
                rfl

theorem cell22_2646766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 9].length) (baseStart_2646766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646766 prefixEnd_2646766 := by exact prefixLift 2646766
  have htrace : WordTrace (prefixWord ++ tailWord_2646766) baseStart_2646766 baseEnd_2646766 := by
    simpa [prefixWord, tailWord_2646766, baseEnd_2646766] using wordTrace_append hprefix tailTrace_2646766
  have hstable : (prefixWord ++ tailWord_2646766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646766).length < 2 ^ (prefixWord ++ tailWord_2646766).sum := by decide
  have hdescent : baseEnd_2646766 < baseStart_2646766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646770 : List Nat := [3, 2, 1, 3, 1, 2, 3, 2, 2, 3]
def baseStart_2646770 : Nat := 118140960795 + 2646770 * 2 ^ 59
def prefixEnd_2646770 : Nat := 4983230072969 + 3 ^ 40 * 2646770 * 2
def baseEnd_2646770 : Nat := 906043461267143155935155

theorem tailTrace_2646770 : CollatzResearch.WordTrace tailWord_2646770 prefixEnd_2646770 906043461267143155935155 := by
  unfold tailWord_2646770
  simp only [CollatzResearch.WordTrace]
  refine ⟨24133908155302949293244441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64357088414141198115318509 24133908155302949293244441)
  ·
    refine ⟨18100431116477211969933331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24133908155302949293244441 18100431116477211969933331)
    ·
      refine ⟨27150646674715817954899997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18100431116477211969933331 27150646674715817954899997)
      ·
        refine ⟨10181492503018431733087499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27150646674715817954899997 10181492503018431733087499)
        ·
          refine ⟨15272238754527647599631249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10181492503018431733087499 15272238754527647599631249)
          ·
            refine ⟨11454179065895735699723437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15272238754527647599631249 11454179065895735699723437)
            ·
              refine ⟨4295317149710900887396289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11454179065895735699723437 4295317149710900887396289)
              ·
                refine ⟨3221487862283175665547217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4295317149710900887396289 3221487862283175665547217)
                ·
                  refine ⟨2416115896712381749160413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3221487862283175665547217 2416115896712381749160413)
                  ·
                    refine ⟨906043461267143155935155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2416115896712381749160413 906043461267143155935155)
                    ·
                      rfl

theorem cell22_2646770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_2646770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646770 prefixEnd_2646770 := by exact prefixLift 2646770
  have htrace : WordTrace (prefixWord ++ tailWord_2646770) baseStart_2646770 baseEnd_2646770 := by
    simpa [prefixWord, tailWord_2646770, baseEnd_2646770] using wordTrace_append hprefix tailTrace_2646770
  have hstable : (prefixWord ++ tailWord_2646770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646770).length < 2 ^ (prefixWord ++ tailWord_2646770).sum := by decide
  have hdescent : baseEnd_2646770 < baseStart_2646770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646772 : List Nat := [2, 6, 1, 1, 2, 1, 2, 1, 6]
def baseStart_2646772 : Nat := 118140960795 + 2646772 * 2 ^ 59
def prefixEnd_2646772 : Nat := 4983230072969 + 3 ^ 40 * 2646772 * 2
def baseEnd_2646772 : Nat := 302014715302671939128383

theorem tailTrace_2646772 : CollatzResearch.WordTrace tailWord_2646772 prefixEnd_2646772 302014715302671939128383 := by
  unfold tailWord_2646772
  simp only [CollatzResearch.WordTrace]
  refine ⟨48267852783602275757275285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64357137044803034343033713 48267852783602275757275285)
  ·
    refine ⟨2262555599231356676122279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 48267852783602275757275285 2262555599231356676122279)
    ·
      refine ⟨3393833398847035014183419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2262555599231356676122279 3393833398847035014183419)
      ·
        refine ⟨5090750098270552521275129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3393833398847035014183419 5090750098270552521275129)
        ·
          refine ⟨3818062573702914390956347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5090750098270552521275129 3818062573702914390956347)
          ·
            refine ⟨5727093860554371586434521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3818062573702914390956347 5727093860554371586434521)
            ·
              refine ⟨4295320395415778689825891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5727093860554371586434521 4295320395415778689825891)
              ·
                refine ⟨6442980593123668034738837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4295320395415778689825891 6442980593123668034738837)
                ·
                  refine ⟨302014715302671939128383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6442980593123668034738837 302014715302671939128383)
                  ·
                    rfl

theorem cell22_2646772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_2646772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646772 prefixEnd_2646772 := by exact prefixLift 2646772
  have htrace : WordTrace (prefixWord ++ tailWord_2646772) baseStart_2646772 baseEnd_2646772 := by
    simpa [prefixWord, tailWord_2646772, baseEnd_2646772] using wordTrace_append hprefix tailTrace_2646772
  have hstable : (prefixWord ++ tailWord_2646772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646772).length < 2 ^ (prefixWord ++ tailWord_2646772).sum := by decide
  have hdescent : baseEnd_2646772 < baseStart_2646772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646845 : List Nat := [1, 4, 1, 4, 2, 1, 1, 3, 5]
def baseStart_2646845 : Nat := 118140960795 + 2646845 * 2 ^ 59
def prefixEnd_2646845 : Nat := 4983230072969 + 3 ^ 40 * 2646845 * 2
def baseEnd_2646845 : Nat := 302023045099955986769975

theorem tailTrace_2646845 : CollatzResearch.WordTrace tailWord_2646845 prefixEnd_2646845 302023045099955986769975 := by
  unfold tailWord_2646845
  simp only [CollatzResearch.WordTrace]
  refine ⟨96538368095940084981957989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64358912063960056654638659 96538368095940084981957989)
  ·
    refine ⟨18100944017988765934117123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96538368095940084981957989 18100944017988765934117123)
    ·
      refine ⟨27151416026983148901175685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18100944017988765934117123 27151416026983148901175685)
      ·
        refine ⟨5090890505059340418970441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27151416026983148901175685 5090890505059340418970441)
        ·
          refine ⟨3818167878794505314227831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5090890505059340418970441 3818167878794505314227831)
          ·
            refine ⟨5727251818191757971341747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3818167878794505314227831 5727251818191757971341747)
            ·
              refine ⟨8590877727287636957012621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5727251818191757971341747 8590877727287636957012621)
              ·
                refine ⟨3221579147732863858879733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8590877727287636957012621 3221579147732863858879733)
                ·
                  refine ⟨302023045099955986769975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3221579147732863858879733 302023045099955986769975)
                  ·
                    rfl

theorem cell22_2646845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_2646845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646845 prefixEnd_2646845 := by exact prefixLift 2646845
  have htrace : WordTrace (prefixWord ++ tailWord_2646845) baseStart_2646845 baseEnd_2646845 := by
    simpa [prefixWord, tailWord_2646845, baseEnd_2646845] using wordTrace_append hprefix tailTrace_2646845
  have hstable : (prefixWord ++ tailWord_2646845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646845).length < 2 ^ (prefixWord ++ tailWord_2646845).sum := by decide
  have hdescent : baseEnd_2646845 < baseStart_2646845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646856 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 8]
def baseStart_2646856 : Nat := 118140960795 + 2646856 * 2 ^ 59
def prefixEnd_2646856 : Nat := 4983230072969 + 3 ^ 40 * 2646856 * 2
def baseEnd_2646856 : Nat := 302024300274889199428297

theorem tailTrace_2646856 : CollatzResearch.WordTrace tailWord_2646856 prefixEnd_2646856 302024300274889199428297 := by
  unfold tailWord_2646856
  simp only [CollatzResearch.WordTrace]
  refine ⟨48269384649450116930304211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64359179532600155907072281 48269384649450116930304211)
  ·
    refine ⟨72404076974175175395456317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48269384649450116930304211 72404076974175175395456317)
    ·
      refine ⟨27151528865315690773296119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72404076974175175395456317 27151528865315690773296119)
      ·
        refine ⟨40727293297973536159944179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27151528865315690773296119 40727293297973536159944179)
        ·
          refine ⟨61090939946960304239916269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40727293297973536159944179 61090939946960304239916269)
          ·
            refine ⟨22909102480110114089968601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61090939946960304239916269 22909102480110114089968601)
            ·
              refine ⟨17181826860082585567476451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22909102480110114089968601 17181826860082585567476451)
              ·
                refine ⟨25772740290123878351214677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17181826860082585567476451 25772740290123878351214677)
                ·
                  refine ⟨302024300274889199428297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25772740290123878351214677 302024300274889199428297)
                  ·
                    rfl

theorem cell22_2646856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 8].length) (baseStart_2646856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646856 prefixEnd_2646856 := by exact prefixLift 2646856
  have htrace : WordTrace (prefixWord ++ tailWord_2646856) baseStart_2646856 baseEnd_2646856 := by
    simpa [prefixWord, tailWord_2646856, baseEnd_2646856] using wordTrace_append hprefix tailTrace_2646856
  have hstable : (prefixWord ++ tailWord_2646856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646856).length < 2 ^ (prefixWord ++ tailWord_2646856).sum := by decide
  have hdescent : baseEnd_2646856 < baseStart_2646856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646858 : List Nat := [3, 1, 2, 1, 1, 1, 2, 6, 1, 4]
def baseStart_2646858 : Nat := 118140960795 + 2646858 * 2 ^ 59
def prefixEnd_2646858 : Nat := 4983230072969 + 3 ^ 40 * 2646858 * 2
def baseEnd_2646858 : Nat := 906073585465540259734885

theorem tailTrace_2646858 : CollatzResearch.WordTrace tailWord_2646858 prefixEnd_2646858 906073585465540259734885 := by
  unfold tailWord_2646858
  simp only [CollatzResearch.WordTrace]
  refine ⟨24134710561223247050545307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64359228163261992134787485 24134710561223247050545307)
  ·
    refine ⟨36202065841834870575817961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24134710561223247050545307 36202065841834870575817961)
    ·
      refine ⟨27151549381376152931863471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36202065841834870575817961 27151549381376152931863471)
      ·
        refine ⟨40727324072064229397795207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27151549381376152931863471 40727324072064229397795207)
        ·
          refine ⟨61090986108096344096692811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40727324072064229397795207 61090986108096344096692811)
          ·
            refine ⟨91636479162144516145039217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61090986108096344096692811 91636479162144516145039217)
            ·
              refine ⟨68727359371608387108779413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91636479162144516145039217 68727359371608387108779413)
              ·
                refine ⟨3221594970544143145724035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68727359371608387108779413 3221594970544143145724035)
                ·
                  refine ⟨4832392455816214718586053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3221594970544143145724035 4832392455816214718586053)
                  ·
                    refine ⟨906073585465540259734885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4832392455816214718586053 906073585465540259734885)
                    ·
                      rfl

theorem cell22_2646858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_2646858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646858 prefixEnd_2646858 := by exact prefixLift 2646858
  have htrace : WordTrace (prefixWord ++ tailWord_2646858) baseStart_2646858 baseEnd_2646858 := by
    simpa [prefixWord, tailWord_2646858, baseEnd_2646858] using wordTrace_append hprefix tailTrace_2646858
  have hstable : (prefixWord ++ tailWord_2646858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646858).length < 2 ^ (prefixWord ++ tailWord_2646858).sum := by decide
  have hdescent : baseEnd_2646858 < baseStart_2646858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646905 : List Nat := [1, 2, 1, 3, 2, 3, 2, 3, 2, 3]
def baseStart_2646905 : Nat := 118140960795 + 2646905 * 2 ^ 59
def prefixEnd_2646905 : Nat := 4983230072969 + 3 ^ 40 * 2646905 * 2
def baseEnd_2646905 : Nat := 906089674526047803809741

theorem tailTrace_2646905 : CollatzResearch.WordTrace tailWord_2646905 prefixEnd_2646905 906089674526047803809741 := by
  unfold tailWord_2646905
  simp only [CollatzResearch.WordTrace]
  refine ⟨96540556475722715229142169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64360370983815143486094779 96540556475722715229142169)
  ·
    refine ⟨72405417356792036421856627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96540556475722715229142169 72405417356792036421856627)
    ·
      refine ⟨108608126035188054632784941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72405417356792036421856627 108608126035188054632784941)
      ·
        refine ⟨40728047263195520487294353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108608126035188054632784941 40728047263195520487294353)
        ·
          refine ⟨30546035447396640365470765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40728047263195520487294353 30546035447396640365470765)
          ·
            refine ⟨11454763292773740137051537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30546035447396640365470765 11454763292773740137051537)
            ·
              refine ⟨8591072469580305102788653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11454763292773740137051537 8591072469580305102788653)
              ·
                refine ⟨3221652176092614413545745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8591072469580305102788653 3221652176092614413545745)
                ·
                  refine ⟨2416239132069460810159309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3221652176092614413545745 2416239132069460810159309)
                  ·
                    refine ⟨906089674526047803809741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2416239132069460810159309 906089674526047803809741)
                    ·
                      rfl

theorem cell22_2646905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2, 3].length) (baseStart_2646905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646905 prefixEnd_2646905 := by exact prefixLift 2646905
  have htrace : WordTrace (prefixWord ++ tailWord_2646905) baseStart_2646905 baseEnd_2646905 := by
    simpa [prefixWord, tailWord_2646905, baseEnd_2646905] using wordTrace_append hprefix tailTrace_2646905
  have hstable : (prefixWord ++ tailWord_2646905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646905).length < 2 ^ (prefixWord ++ tailWord_2646905).sum := by decide
  have hdescent : baseEnd_2646905 < baseStart_2646905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646920 : List Nat := [2, 1, 3, 3, 2, 1, 3, 1, 2, 4]
def baseStart_2646920 : Nat := 118140960795 + 2646920 * 2 ^ 59
def prefixEnd_2646920 : Nat := 4983230072969 + 3 ^ 40 * 2646920 * 2
def baseEnd_2646920 : Nat := 906094809332592764684695

theorem tailTrace_2646920 : CollatzResearch.WordTrace tailWord_2646920 prefixEnd_2646920 906094809332592764684695 := by
  unfold tailWord_2646920
  simp only [CollatzResearch.WordTrace]
  refine ⟨48270551785334186395469107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64360735713778915193958809 48270551785334186395469107)
  ·
    refine ⟨72405827678001279593203661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48270551785334186395469107 72405827678001279593203661)
    ·
      refine ⟨27152185379250479847451373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72405827678001279593203661 27152185379250479847451373)
      ·
        refine ⟨10182069517218929942794265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27152185379250479847451373 10182069517218929942794265)
        ·
          refine ⟨7636552137914197457095699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10182069517218929942794265 7636552137914197457095699)
          ·
            refine ⟨11454828206871296185643549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7636552137914197457095699 11454828206871296185643549)
            ·
              refine ⟨4295560577576736069616331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11454828206871296185643549 4295560577576736069616331)
              ·
                refine ⟨6443340866365104104424497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4295560577576736069616331 6443340866365104104424497)
                ·
                  refine ⟨4832505649773828078318373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6443340866365104104424497 4832505649773828078318373)
                  ·
                    refine ⟨906094809332592764684695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4832505649773828078318373 906094809332592764684695)
                    ·
                      rfl

theorem cell22_2646920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_2646920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646920 prefixEnd_2646920 := by exact prefixLift 2646920
  have htrace : WordTrace (prefixWord ++ tailWord_2646920) baseStart_2646920 baseEnd_2646920 := by
    simpa [prefixWord, tailWord_2646920, baseEnd_2646920] using wordTrace_append hprefix tailTrace_2646920
  have hstable : (prefixWord ++ tailWord_2646920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646920).length < 2 ^ (prefixWord ++ tailWord_2646920).sum := by decide
  have hdescent : baseEnd_2646920 < baseStart_2646920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646931 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 1, 8]
def baseStart_2646931 : Nat := 118140960795 + 2646931 * 2 ^ 59
def prefixEnd_2646931 : Nat := 4983230072969 + 3 ^ 40 * 2646931 * 2
def baseEnd_2646931 : Nat := 906098574857392402659661

theorem tailTrace_2646931 : CollatzResearch.WordTrace tailWord_2646931 prefixEnd_2646931 906098574857392402659661 := by
  unfold tailWord_2646931
  simp only [CollatzResearch.WordTrace]
  refine ⟨96541504773628521669588647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64361003182419014446392431 96541504773628521669588647)
  ·
    refine ⟨144812257160442782504382971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96541504773628521669588647 144812257160442782504382971)
    ·
      refine ⟨217218385740664173756574457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144812257160442782504382971 217218385740664173756574457)
      ·
        refine ⟨162913789305498130317430843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217218385740664173756574457 162913789305498130317430843)
        ·
          refine ⟨244370683958247195476146265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162913789305498130317430843 244370683958247195476146265)
          ·
            refine ⟨183278012968685396607109699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244370683958247195476146265 183278012968685396607109699)
            ·
              refine ⟨274917019453028094910664549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183278012968685396607109699 274917019453028094910664549)
              ·
                refine ⟨51546941147442767795749603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 274917019453028094910664549 51546941147442767795749603)
                ·
                  refine ⟨77320411721164151693624405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51546941147442767795749603 77320411721164151693624405)
                  ·
                    refine ⟨906098574857392402659661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77320411721164151693624405 906098574857392402659661)
                    ·
                      rfl

theorem cell22_2646931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 8].length) (baseStart_2646931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2646931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2646931 prefixEnd_2646931 := by exact prefixLift 2646931
  have htrace : WordTrace (prefixWord ++ tailWord_2646931) baseStart_2646931 baseEnd_2646931 := by
    simpa [prefixWord, tailWord_2646931, baseEnd_2646931] using wordTrace_append hprefix tailTrace_2646931
  have hstable : (prefixWord ++ tailWord_2646931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646931).length < 2 ^ (prefixWord ++ tailWord_2646931).sum := by decide
  have hdescent : baseEnd_2646931 < baseStart_2646931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647083 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 2, 6]
def baseStart_2647083 : Nat := 118140960795 + 2647083 * 2 ^ 59
def prefixEnd_2647083 : Nat := 4983230072969 + 3 ^ 40 * 2647083 * 2
def baseEnd_2647083 : Nat := 906150607563714672859195

theorem tailTrace_2647083 : CollatzResearch.WordTrace tailWord_2647083 prefixEnd_2647083 906150607563714672859195 := by
  unfold tailWord_2647083
  simp only [CollatzResearch.WordTrace]
  refine ⟨96547048669077851629121903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64364699112718567752747935 96547048669077851629121903)
  ·
    refine ⟨144820573003616777443682855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96547048669077851629121903 144820573003616777443682855)
    ·
      refine ⟨217230859505425166165524283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144820573003616777443682855 217230859505425166165524283)
      ·
        refine ⟨325846289258137749248286425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217230859505425166165524283 325846289258137749248286425)
        ·
          refine ⟨244384716943603311936214819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325846289258137749248286425 244384716943603311936214819)
          ·
            refine ⟨366577075415404967904322229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244384716943603311936214819 366577075415404967904322229)
            ·
              refine ⟨34366600820194215741030209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 366577075415404967904322229 34366600820194215741030209)
              ·
                refine ⟨25774950615145661805772657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34366600820194215741030209 25774950615145661805772657)
                ·
                  refine ⟨19331212961359246354329493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25774950615145661805772657 19331212961359246354329493)
                  ·
                    refine ⟨906150607563714672859195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19331212961359246354329493 906150607563714672859195)
                    ·
                      rfl

theorem cell22_2647083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 6].length) (baseStart_2647083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2647083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2647083 prefixEnd_2647083 := by exact prefixLift 2647083
  have htrace : WordTrace (prefixWord ++ tailWord_2647083) baseStart_2647083 baseEnd_2647083 := by
    simpa [prefixWord, tailWord_2647083, baseEnd_2647083] using wordTrace_append hprefix tailTrace_2647083
  have hstable : (prefixWord ++ tailWord_2647083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647083).length < 2 ^ (prefixWord ++ tailWord_2647083).sum := by decide
  have hdescent : baseEnd_2647083 < baseStart_2647083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647177 : List Nat := [1, 2, 1, 1, 4, 5, 1, 1, 6]
def baseStart_2647177 : Nat := 118140960795 + 2647177 * 2 ^ 59
def prefixEnd_2647177 : Nat := 4983230072969 + 3 ^ 40 * 2647177 * 2
def baseEnd_2647177 : Nat := 302060928561576587002969

theorem tailTrace_2647177 : CollatzResearch.WordTrace tailWord_2647177 prefixEnd_2647177 302060928561576587002969 := by
  unfold tailWord_2647177
  simp only [CollatzResearch.WordTrace]
  refine ⟨96550477130737305683043785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64366984753824870455362523 96550477130737305683043785)
  ·
    refine ⟨72412857848052979262282839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96550477130737305683043785 72412857848052979262282839)
    ·
      refine ⟨108619286772079468893424259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72412857848052979262282839 108619286772079468893424259)
      ·
        refine ⟨162928930158119203340136389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108619286772079468893424259 162928930158119203340136389)
        ·
          refine ⟨30549174404647350626275573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162928930158119203340136389 30549174404647350626275573)
          ·
            refine ⟨2863985100435689121213335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30549174404647350626275573 2863985100435689121213335)
            ·
              refine ⟨4295977650653533681820003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2863985100435689121213335 4295977650653533681820003)
              ·
                refine ⟨6443966475980300522730005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4295977650653533681820003 6443966475980300522730005)
                ·
                  refine ⟨302060928561576587002969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6443966475980300522730005 302060928561576587002969)
                  ·
                    rfl

theorem cell22_2647177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 6].length) (baseStart_2647177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2647177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2647177 prefixEnd_2647177 := by exact prefixLift 2647177
  have htrace : WordTrace (prefixWord ++ tailWord_2647177) baseStart_2647177 baseEnd_2647177 := by
    simpa [prefixWord, tailWord_2647177, baseEnd_2647177] using wordTrace_append hprefix tailTrace_2647177
  have hstable : (prefixWord ++ tailWord_2647177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647177).length < 2 ^ (prefixWord ++ tailWord_2647177).sum := by decide
  have hdescent : baseEnd_2647177 < baseStart_2647177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647205 : List Nat := [1, 3, 1, 2, 1, 4, 2, 8]
def baseStart_2647205 : Nat := 118140960795 + 2647205 * 2 ^ 59
def prefixEnd_2647205 : Nat := 4983230072969 + 3 ^ 40 * 2647205 * 2
def baseEnd_2647205 : Nat := 100688041184105224589869

theorem tailTrace_2647205 : CollatzResearch.WordTrace tailWord_2647205 prefixEnd_2647205 100688041184105224589869 := by
  unfold tailWord_2647205
  simp only [CollatzResearch.WordTrace]
  refine ⟨96551498374635866465063069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64367665583090577643375379 96551498374635866465063069)
  ·
    refine ⟨36206811890488449924398651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96551498374635866465063069 36206811890488449924398651)
    ·
      refine ⟨54310217835732674886597977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36206811890488449924398651 54310217835732674886597977)
      ·
        refine ⟨40732663376799506164948483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54310217835732674886597977 40732663376799506164948483)
        ·
          refine ⟨61098995065199259247422725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40732663376799506164948483 61098995065199259247422725)
          ·
            refine ⟨11456061574724861108891761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61098995065199259247422725 11456061574724861108891761)
            ·
              refine ⟨8592046181043645831668821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11456061574724861108891761 8592046181043645831668821)
              ·
                refine ⟨100688041184105224589869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8592046181043645831668821 100688041184105224589869)
                ·
                  rfl

theorem cell22_2647205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 8].length) (baseStart_2647205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2647205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2647205 prefixEnd_2647205 := by exact prefixLift 2647205
  have htrace : WordTrace (prefixWord ++ tailWord_2647205) baseStart_2647205 baseEnd_2647205 := by
    simpa [prefixWord, tailWord_2647205, baseEnd_2647205] using wordTrace_append hprefix tailTrace_2647205
  have hstable : (prefixWord ++ tailWord_2647205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647205).length < 2 ^ (prefixWord ++ tailWord_2647205).sum := by decide
  have hdescent : baseEnd_2647205 < baseStart_2647205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647237 : List Nat := [1, 3, 1, 1, 1, 1, 3, 5, 3, 3]
def baseStart_2647237 : Nat := 118140960795 + 2647237 * 2 ^ 59
def prefixEnd_2647237 : Nat := 4983230072969 + 3 ^ 40 * 2647237 * 2
def baseEnd_2647237 : Nat := 906203324910909604508723

theorem tailTrace_2647237 : CollatzResearch.WordTrace tailWord_2647237 prefixEnd_2647237 906203324910909604508723 := by
  unfold tailWord_2647237
  simp only [CollatzResearch.WordTrace]
  refine ⟨96552665510519935930227965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64368443673679957286818643 96552665510519935930227965)
  ·
    refine ⟨36207249566444975973835487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96552665510519935930227965 36207249566444975973835487)
    ·
      refine ⟨54310874349667463960753231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36207249566444975973835487 54310874349667463960753231)
      ·
        refine ⟨81466311524501195941129847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54310874349667463960753231 81466311524501195941129847)
        ·
          refine ⟨122199467286751793911694771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81466311524501195941129847 122199467286751793911694771)
          ·
            refine ⟨183299200930127690867542157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122199467286751793911694771 183299200930127690867542157)
            ·
              refine ⟨68737200348797884075328309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 183299200930127690867542157 68737200348797884075328309)
              ·
                refine ⟨6444112532699801632062029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68737200348797884075328309 6444112532699801632062029)
                ·
                  refine ⟨2416542199762425612023261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6444112532699801632062029 2416542199762425612023261)
                  ·
                    refine ⟨906203324910909604508723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2416542199762425612023261 906203324910909604508723)
                    ·
                      rfl

theorem cell22_2647237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3, 3].length) (baseStart_2647237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2647237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2647237 prefixEnd_2647237 := by exact prefixLift 2647237
  have htrace : WordTrace (prefixWord ++ tailWord_2647237) baseStart_2647237 baseEnd_2647237 := by
    simpa [prefixWord, tailWord_2647237, baseEnd_2647237] using wordTrace_append hprefix tailTrace_2647237
  have hstable : (prefixWord ++ tailWord_2647237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647237).length < 2 ^ (prefixWord ++ tailWord_2647237).sum := by decide
  have hdescent : baseEnd_2647237 < baseStart_2647237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647344 : List Nat := [2, 1, 1, 1, 2, 2, 4, 4, 2, 3]
def baseStart_2647344 : Nat := 118140960795 + 2647344 * 2 ^ 59
def prefixEnd_2647344 : Nat := 4983230072969 + 3 ^ 40 * 2647344 * 2
def baseEnd_2647344 : Nat := 906239953197596992083395

theorem tailTrace_2647344 : CollatzResearch.WordTrace tailWord_2647344 prefixEnd_2647344 906239953197596992083395 := by
  unfold tailWord_2647344
  simp only [CollatzResearch.WordTrace]
  refine ⟨48278284060566146602186543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64371045414088195469582057 48278284060566146602186543)
  ·
    refine ⟨72417426090849219903279815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48278284060566146602186543 72417426090849219903279815)
    ·
      refine ⟨108626139136273829854919723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72417426090849219903279815 108626139136273829854919723)
      ·
        refine ⟨162939208704410744782379585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108626139136273829854919723 162939208704410744782379585)
        ·
          refine ⟨122204406528308058586784689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162939208704410744782379585 122204406528308058586784689)
          ·
            refine ⟨91653304896231043940088517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122204406528308058586784689 91653304896231043940088517)
            ·
              refine ⟨17184994668043320738766597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91653304896231043940088517 17184994668043320738766597)
              ·
                refine ⟨3222186500258122638518737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17184994668043320738766597 3222186500258122638518737)
                ·
                  refine ⟨2416639875193591978889053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3222186500258122638518737 2416639875193591978889053)
                  ·
                    refine ⟨906239953197596992083395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2416639875193591978889053 906239953197596992083395)
                    ·
                      rfl

theorem cell22_2647344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 2, 3].length) (baseStart_2647344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2647344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2647344 prefixEnd_2647344 := by exact prefixLift 2647344
  have htrace : WordTrace (prefixWord ++ tailWord_2647344) baseStart_2647344 baseEnd_2647344 := by
    simpa [prefixWord, tailWord_2647344, baseEnd_2647344] using wordTrace_append hprefix tailTrace_2647344
  have hstable : (prefixWord ++ tailWord_2647344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647344).length < 2 ^ (prefixWord ++ tailWord_2647344).sum := by decide
  have hdescent : baseEnd_2647344 < baseStart_2647344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647417 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 1, 7]
def baseStart_2647417 : Nat := 118140960795 + 2647417 * 2 ^ 59
def prefixEnd_2647417 : Nat := 4983230072969 + 3 ^ 40 * 2647417 * 2
def baseEnd_2647417 : Nat := 906264942589449135008171

theorem tailTrace_2647417 : CollatzResearch.WordTrace tailWord_2647417 prefixEnd_2647417 906264942589449135008171 := by
  unfold tailWord_2647417
  simp only [CollatzResearch.WordTrace]
  refine ⟨96559230649867826671780505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64372820433245217781187003 96559230649867826671780505)
  ·
    refine ⟨72419422987400870003835379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96559230649867826671780505 72419422987400870003835379)
    ·
      refine ⟨108629134481101305005753069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72419422987400870003835379 108629134481101305005753069)
      ·
        refine ⟨40735925430412989377157401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108629134481101305005753069 40735925430412989377157401)
        ·
          refine ⟨30551944072809742032868051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40735925430412989377157401 30551944072809742032868051)
          ·
            refine ⟨45827916109214613049302077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30551944072809742032868051 45827916109214613049302077)
            ·
              refine ⟨17185468540955479893488279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45827916109214613049302077 17185468540955479893488279)
              ·
                refine ⟨25778202811433219840232419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17185468540955479893488279 25778202811433219840232419)
                ·
                  refine ⟨38667304217149829760348629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25778202811433219840232419 38667304217149829760348629)
                  ·
                    refine ⟨906264942589449135008171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38667304217149829760348629 906264942589449135008171)
                    ·
                      rfl

theorem cell22_2647417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 7].length) (baseStart_2647417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2647417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2647417 prefixEnd_2647417 := by exact prefixLift 2647417
  have htrace : WordTrace (prefixWord ++ tailWord_2647417) baseStart_2647417 baseEnd_2647417 := by
    simpa [prefixWord, tailWord_2647417, baseEnd_2647417] using wordTrace_append hprefix tailTrace_2647417
  have hstable : (prefixWord ++ tailWord_2647417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647417).length < 2 ^ (prefixWord ++ tailWord_2647417).sum := by decide
  have hdescent : baseEnd_2647417 < baseStart_2647417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647447 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 10]
def baseStart_2647447 : Nat := 118140960795 + 2647447 * 2 ^ 59
def prefixEnd_2647447 : Nat := 4983230072969 + 3 ^ 40 * 2647447 * 2
def baseEnd_2647447 : Nat := 302091737400846352252693

theorem tailTrace_2647447 : CollatzResearch.WordTrace tailWord_2647447 prefixEnd_2647447 302091737400846352252693 := by
  unfold tailWord_2647447
  simp only [CollatzResearch.WordTrace]
  refine ⟨96560324839759141795372595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64373549893172761196915063 96560324839759141795372595)
  ·
    refine ⟨144840487259638712693058893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96560324839759141795372595 144840487259638712693058893)
    ·
      refine ⟨54315182722364517259897085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144840487259638712693058893 54315182722364517259897085)
      ·
        refine ⟨20368193520886693972461407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54315182722364517259897085 20368193520886693972461407)
        ·
          refine ⟨30552290281330040958692111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20368193520886693972461407 30552290281330040958692111)
          ·
            refine ⟨45828435421995061438038167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30552290281330040958692111 45828435421995061438038167)
            ·
              refine ⟨68742653132992592157057251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45828435421995061438038167 68742653132992592157057251)
              ·
                refine ⟨103113979699488888235585877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68742653132992592157057251 103113979699488888235585877)
                ·
                  refine ⟨302091737400846352252693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 103113979699488888235585877 302091737400846352252693)
                  ·
                    rfl

theorem cell22_2647447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 10].length) (baseStart_2647447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2647447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2647447 prefixEnd_2647447 := by exact prefixLift 2647447
  have htrace : WordTrace (prefixWord ++ tailWord_2647447) baseStart_2647447 baseEnd_2647447 := by
    simpa [prefixWord, tailWord_2647447, baseEnd_2647447] using wordTrace_append hprefix tailTrace_2647447
  have hstable : (prefixWord ++ tailWord_2647447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647447).length < 2 ^ (prefixWord ++ tailWord_2647447).sum := by decide
  have hdescent : baseEnd_2647447 < baseStart_2647447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647498 : List Nat := [3, 1, 2, 1, 2, 5, 1, 3, 4]
def baseStart_2647498 : Nat := 118140960795 + 2647498 * 2 ^ 59
def prefixEnd_2647498 : Nat := 4983230072969 + 3 ^ 40 * 2647498 * 2
def baseEnd_2647498 : Nat := 302097556848263974577641

theorem tailTrace_2647498 : CollatzResearch.WordTrace tailWord_2647498 prefixEnd_2647498 302097556848263974577641 := by
  unfold tailWord_2647498
  simp only [CollatzResearch.WordTrace]
  refine ⟨24140546240643594376369787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64374789975049585003652765 24140546240643594376369787)
  ·
    refine ⟨36210819360965391564554681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24140546240643594376369787 36210819360965391564554681)
    ·
      refine ⟨27158114520724043673416011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36210819360965391564554681 27158114520724043673416011)
      ·
        refine ⟨40737171781086065510124017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27158114520724043673416011 40737171781086065510124017)
        ·
          refine ⟨30552878835814549132593013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40737171781086065510124017 30552878835814549132593013)
          ·
            refine ⟨2864332390857613981180595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30552878835814549132593013 2864332390857613981180595)
            ·
              refine ⟨4296498586286420971770893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2864332390857613981180595 4296498586286420971770893)
              ·
                refine ⟨1611186969857407864414085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4296498586286420971770893 1611186969857407864414085)
                ·
                  refine ⟨302097556848263974577641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1611186969857407864414085 302097556848263974577641)
                  ·
                    rfl

theorem cell22_2647498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3, 4].length) (baseStart_2647498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2647498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2647498 prefixEnd_2647498 := by exact prefixLift 2647498
  have htrace : WordTrace (prefixWord ++ tailWord_2647498) baseStart_2647498 baseEnd_2647498 := by
    simpa [prefixWord, tailWord_2647498, baseEnd_2647498] using wordTrace_append hprefix tailTrace_2647498
  have hstable : (prefixWord ++ tailWord_2647498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647498).length < 2 ^ (prefixWord ++ tailWord_2647498).sum := by decide
  have hdescent : baseEnd_2647498 < baseStart_2647498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647569 : List Nat := [1, 2, 2, 1, 1, 2, 4, 2, 2, 5]
def baseStart_2647569 : Nat := 118140960795 + 2647569 * 2 ^ 59
def prefixEnd_2647569 : Nat := 4983230072969 + 3 ^ 40 * 2647569 * 2
def baseEnd_2647569 : Nat := 906316975295771405207705

theorem tailTrace_2647569 : CollatzResearch.WordTrace tailWord_2647569 prefixEnd_2647569 906316975295771405207705 := by
  unfold tailWord_2647569
  simp only [CollatzResearch.WordTrace]
  refine ⟨96564774545317156631313761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64376516363544771087542507 96564774545317156631313761)
  ·
    refine ⟨72423580908987867473485321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96564774545317156631313761 72423580908987867473485321)
    ·
      refine ⟨54317685681740900605113991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72423580908987867473485321 54317685681740900605113991)
      ·
        refine ⟨81476528522611350907670987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54317685681740900605113991 81476528522611350907670987)
        ·
          refine ⟨122214792783917026361506481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81476528522611350907670987 122214792783917026361506481)
          ·
            refine ⟨91661094587937769771129861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122214792783917026361506481 91661094587937769771129861)
            ·
              refine ⟨17186455235238331832086849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91661094587937769771129861 17186455235238331832086849)
              ·
                refine ⟨12889841426428748874065137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17186455235238331832086849 12889841426428748874065137)
                ·
                  refine ⟨9667381069821561655548853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12889841426428748874065137 9667381069821561655548853)
                  ·
                    refine ⟨906316975295771405207705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9667381069821561655548853 906316975295771405207705)
                    ·
                      rfl

theorem cell22_2647569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_2647569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2647569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2647569 prefixEnd_2647569 := by exact prefixLift 2647569
  have htrace : WordTrace (prefixWord ++ tailWord_2647569) baseStart_2647569 baseEnd_2647569 := by
    simpa [prefixWord, tailWord_2647569, baseEnd_2647569] using wordTrace_append hprefix tailTrace_2647569
  have hstable : (prefixWord ++ tailWord_2647569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647569).length < 2 ^ (prefixWord ++ tailWord_2647569).sum := by decide
  have hdescent : baseEnd_2647569 < baseStart_2647569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647571 : List Nat := [1, 1, 1, 2, 1, 7, 2, 2, 5]
def baseStart_2647571 : Nat := 118140960795 + 2647571 * 2 ^ 59
def prefixEnd_2647571 : Nat := 4983230072969 + 3 ^ 40 * 2647571 * 2
def baseEnd_2647571 : Nat := 302105886645548022219233

theorem tailTrace_2647571 : CollatzResearch.WordTrace tailWord_2647571 prefixEnd_2647571 302105886645548022219233 := by
  unfold tailWord_2647571
  simp only [CollatzResearch.WordTrace]
  refine ⟨96564847491309910972886567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64376564994206607315257711 96564847491309910972886567)
  ·
    refine ⟨144847271236964866459329851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96564847491309910972886567 144847271236964866459329851)
    ·
      refine ⟨217270906855447299688994777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144847271236964866459329851 217270906855447299688994777)
      ·
        refine ⟨162953180141585474766746083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217270906855447299688994777 162953180141585474766746083)
        ·
          refine ⟨244429770212378212150119125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162953180141585474766746083 244429770212378212150119125)
          ·
            refine ⟨5728822739352614347268417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 244429770212378212150119125 5728822739352614347268417)
            ·
              refine ⟨4296617054514460760451313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5728822739352614347268417 4296617054514460760451313)
              ·
                refine ⟨3222462790885845570338485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4296617054514460760451313 3222462790885845570338485)
                ·
                  refine ⟨302105886645548022219233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3222462790885845570338485 302105886645548022219233)
                  ·
                    rfl

theorem cell22_2647571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 5].length) (baseStart_2647571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2647571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2647571 prefixEnd_2647571 := by exact prefixLift 2647571
  have htrace : WordTrace (prefixWord ++ tailWord_2647571) baseStart_2647571 baseEnd_2647571 := by
    simpa [prefixWord, tailWord_2647571, baseEnd_2647571] using wordTrace_append hprefix tailTrace_2647571
  have hstable : (prefixWord ++ tailWord_2647571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647571).length < 2 ^ (prefixWord ++ tailWord_2647571).sum := by decide
  have hdescent : baseEnd_2647571 < baseStart_2647571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647601 : List Nat := [1, 2, 2, 3, 1, 1, 1, 6, 1, 4]
def baseStart_2647601 : Nat := 118140960795 + 2647601 * 2 ^ 59
def prefixEnd_2647601 : Nat := 4983230072969 + 3 ^ 40 * 2647601 * 2
def baseEnd_2647601 : Nat := 906327929549733988407607

theorem tailTrace_2647601 : CollatzResearch.WordTrace tailWord_2647601 prefixEnd_2647601 906327929549733988407607 := by
  unfold tailWord_2647601
  simp only [CollatzResearch.WordTrace]
  refine ⟨96565941681201226096478657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64377294454134150730985771 96565941681201226096478657)
  ·
    refine ⟨72424456260900919572358993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96565941681201226096478657 72424456260900919572358993)
    ·
      refine ⟨54318342195675689679269245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72424456260900919572358993 54318342195675689679269245)
      ·
        refine ⟨20369378323378383629725967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54318342195675689679269245 20369378323378383629725967)
        ·
          refine ⟨30554067485067575444588951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20369378323378383629725967 30554067485067575444588951)
          ·
            refine ⟨45831101227601363166883427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30554067485067575444588951 45831101227601363166883427)
            ·
              refine ⟨68746651841402044750325141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45831101227601363166883427 68746651841402044750325141)
              ·
                refine ⟨3222499305065720847671491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68746651841402044750325141 3222499305065720847671491)
                ·
                  refine ⟨4833748957598581271507237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3222499305065720847671491 4833748957598581271507237)
                  ·
                    refine ⟨906327929549733988407607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4833748957598581271507237 906327929549733988407607)
                    ·
                      rfl

theorem cell22_2647601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_2647601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2647601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2647601 prefixEnd_2647601 := by exact prefixLift 2647601
  have htrace : WordTrace (prefixWord ++ tailWord_2647601) baseStart_2647601 baseEnd_2647601 := by
    simpa [prefixWord, tailWord_2647601, baseEnd_2647601] using wordTrace_append hprefix tailTrace_2647601
  have hstable : (prefixWord ++ tailWord_2647601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647601).length < 2 ^ (prefixWord ++ tailWord_2647601).sum := by decide
  have hdescent : baseEnd_2647601 < baseStart_2647601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647622 : List Nat := [6, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_2647622 : Nat := 118140960795 + 2647622 * 2 ^ 59
def prefixEnd_2647622 : Nat := 4983230072969 + 3 ^ 40 * 2647622 * 2
def baseEnd_2647622 : Nat := 302111706092965644544181

theorem tailTrace_2647622 : CollatzResearch.WordTrace tailWord_2647622 prefixEnd_2647622 302111706092965644544181 := by
  unfold tailWord_2647622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3017709612941410833843535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 64377805076083431121995413 3017709612941410833843535)
  ·
    refine ⟨4526564419412116250765303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3017709612941410833843535 4526564419412116250765303)
    ·
      refine ⟨6789846629118174376147955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4526564419412116250765303 6789846629118174376147955)
      ·
        refine ⟨10184769943677261564221933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6789846629118174376147955 10184769943677261564221933)
        ·
          refine ⟨3819288728878973086583225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10184769943677261564221933 3819288728878973086583225)
          ·
            refine ⟨2864466546659229814937419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3819288728878973086583225 2864466546659229814937419)
            ·
              refine ⟨4296699819988844722406129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2864466546659229814937419 4296699819988844722406129)
              ·
                refine ⟨3222524864991633541804597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4296699819988844722406129 3222524864991633541804597)
                ·
                  refine ⟨302111706092965644544181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3222524864991633541804597 302111706092965644544181)
                  ·
                    rfl

theorem cell22_2647622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_2647622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2647622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2647622 prefixEnd_2647622 := by exact prefixLift 2647622
  have htrace : WordTrace (prefixWord ++ tailWord_2647622) baseStart_2647622 baseEnd_2647622 := by
    simpa [prefixWord, tailWord_2647622, baseEnd_2647622] using wordTrace_append hprefix tailTrace_2647622
  have hstable : (prefixWord ++ tailWord_2647622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647622).length < 2 ^ (prefixWord ++ tailWord_2647622).sum := by decide
  have hdescent : baseEnd_2647622 < baseStart_2647622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647751 : List Nat := [1, 1, 4, 1, 1, 1, 4, 3, 6]
def baseStart_2647751 : Nat := 118140960795 + 2647751 * 2 ^ 59
def prefixEnd_2647751 : Nat := 4983230072969 + 3 ^ 40 * 2647751 * 2
def baseEnd_2647751 : Nat := 302126425871727865719049

theorem tailTrace_2647751 : CollatzResearch.WordTrace tailWord_2647751 prefixEnd_2647751 302126425871727865719049 := by
  unfold tailWord_2647751
  simp only [CollatzResearch.WordTrace]
  refine ⟨96571412630657801714439107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64380941753771867809626071 96571412630657801714439107)
  ·
    refine ⟨144857118945986702571658661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96571412630657801714439107 144857118945986702571658661)
    ·
      refine ⟨27160709802372506732185999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144857118945986702571658661 27160709802372506732185999)
      ·
        refine ⟨40741064703558760098278999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27160709802372506732185999 40741064703558760098278999)
        ·
          refine ⟨61111597055338140147418499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40741064703558760098278999 61111597055338140147418499)
          ·
            refine ⟨91667395583007210221127749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61111597055338140147418499 91667395583007210221127749)
            ·
              refine ⟨17187636671813851916461453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91667395583007210221127749 17187636671813851916461453)
              ·
                refine ⟨6445363751930194468673045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17187636671813851916461453 6445363751930194468673045)
                ·
                  refine ⟨302126425871727865719049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6445363751930194468673045 302126425871727865719049)
                  ·
                    rfl

theorem cell22_2647751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 6].length) (baseStart_2647751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2647751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2647751 prefixEnd_2647751 := by exact prefixLift 2647751
  have htrace : WordTrace (prefixWord ++ tailWord_2647751) baseStart_2647751 baseEnd_2647751 := by
    simpa [prefixWord, tailWord_2647751, baseEnd_2647751] using wordTrace_append hprefix tailTrace_2647751
  have hstable : (prefixWord ++ tailWord_2647751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647751).length < 2 ^ (prefixWord ++ tailWord_2647751).sum := by decide
  have hdescent : baseEnd_2647751 < baseStart_2647751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647858 : List Nat := [3, 2, 1, 1, 3, 2, 2, 1, 7]
def baseStart_2647858 : Nat := 118140960795 + 2647858 * 2 ^ 59
def prefixEnd_2647858 : Nat := 4983230072969 + 3 ^ 40 * 2647858 * 2
def baseEnd_2647858 : Nat := 302138635300623661577273

theorem tailTrace_2647858 : CollatzResearch.WordTrace tailWord_2647858 prefixEnd_2647858 302138635300623661577273 := by
  unfold tailWord_2647858
  simp only [CollatzResearch.WordTrace]
  refine ⟨24143828810317539747146057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64383543494180105992389485 24143828810317539747146057)
  ·
    refine ⟨18107871607738154810359543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24143828810317539747146057 18107871607738154810359543)
    ·
      refine ⟨27161807411607232215539315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18107871607738154810359543 27161807411607232215539315)
      ·
        refine ⟨40742711117410848323308973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27161807411607232215539315 40742711117410848323308973)
        ·
          refine ⟨15278516669029068121240865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40742711117410848323308973 15278516669029068121240865)
          ·
            refine ⟨11458887501771801090930649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15278516669029068121240865 11458887501771801090930649)
            ·
              refine ⟨8594165626328850818197987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11458887501771801090930649 8594165626328850818197987)
              ·
                refine ⟨12891248439493276227296981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8594165626328850818197987 12891248439493276227296981)
                ·
                  refine ⟨302138635300623661577273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12891248439493276227296981 302138635300623661577273)
                  ·
                    rfl

theorem cell22_2647858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_2647858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2647858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2647858 prefixEnd_2647858 := by exact prefixLift 2647858
  have htrace : WordTrace (prefixWord ++ tailWord_2647858) baseStart_2647858 baseEnd_2647858 := by
    simpa [prefixWord, tailWord_2647858, baseEnd_2647858] using wordTrace_append hprefix tailTrace_2647858
  have hstable : (prefixWord ++ tailWord_2647858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647858).length < 2 ^ (prefixWord ++ tailWord_2647858).sum := by decide
  have hdescent : baseEnd_2647858 < baseStart_2647858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647875 : List Nat := [1, 1, 1, 3, 1, 5, 4, 1, 5]
def baseStart_2647875 : Nat := 118140960795 + 2647875 * 2 ^ 59
def prefixEnd_2647875 : Nat := 4983230072969 + 3 ^ 40 * 2647875 * 2
def baseEnd_2647875 : Nat := 302140575116429535685589

theorem tailTrace_2647875 : CollatzResearch.WordTrace tailWord_2647875 prefixEnd_2647875 302140575116429535685589 := by
  unfold tailWord_2647875
  simp only [CollatzResearch.WordTrace]
  refine ⟨96575935282208570891953079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64383956854805713927968719 96575935282208570891953079)
  ·
    refine ⟨144863902923312856337929619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96575935282208570891953079 144863902923312856337929619)
    ·
      refine ⟨217295854384969284506894429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144863902923312856337929619 217295854384969284506894429)
      ·
        refine ⟨81485945394363481690085411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217295854384969284506894429 81485945394363481690085411)
        ·
          refine ⟨122228918091545222535128117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81485945394363481690085411 122228918091545222535128117)
          ·
            refine ⟨11458961071082364612668261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122228918091545222535128117 11458961071082364612668261)
            ·
              refine ⟨2148555200827943364875299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11458961071082364612668261 2148555200827943364875299)
              ·
                refine ⟨3222832801241915047312949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2148555200827943364875299 3222832801241915047312949)
                ·
                  refine ⟨302140575116429535685589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3222832801241915047312949 302140575116429535685589)
                  ·
                    rfl

theorem cell22_2647875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 5].length) (baseStart_2647875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2647875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2647875 prefixEnd_2647875 := by exact prefixLift 2647875
  have htrace : WordTrace (prefixWord ++ tailWord_2647875) baseStart_2647875 baseEnd_2647875 := by
    simpa [prefixWord, tailWord_2647875, baseEnd_2647875] using wordTrace_append hprefix tailTrace_2647875
  have hstable : (prefixWord ++ tailWord_2647875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647875).length < 2 ^ (prefixWord ++ tailWord_2647875).sum := by decide
  have hdescent : baseEnd_2647875 < baseStart_2647875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647933 : List Nat := [1, 4, 1, 1, 2, 1, 1, 4, 1, 6]
def baseStart_2647933 : Nat := 118140960795 + 2647933 * 2 ^ 59
def prefixEnd_2647933 : Nat := 4983230072969 + 3 ^ 40 * 2647933 * 2
def baseEnd_2647933 : Nat := 906441579934595789106589

theorem tailTrace_2647933 : CollatzResearch.WordTrace tailWord_2647933 prefixEnd_2647933 906441579934595789106589 := by
  unfold tailWord_2647933
  simp only [CollatzResearch.WordTrace]
  refine ⟨96578050715998446797564453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64385367143998964531709635 96578050715998446797564453)
  ·
    refine ⟨18108384509249708774543335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96578050715998446797564453 18108384509249708774543335)
    ·
      refine ⟨27162576763874563161815003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18108384509249708774543335 27162576763874563161815003)
      ·
        refine ⟨40743865145811844742722505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27162576763874563161815003 40743865145811844742722505)
        ·
          refine ⟨30557898859358883557041879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40743865145811844742722505 30557898859358883557041879)
          ·
            refine ⟨45836848289038325335562819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30557898859358883557041879 45836848289038325335562819)
            ·
              refine ⟨68755272433557488003344229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45836848289038325335562819 68755272433557488003344229)
              ·
                refine ⟨12891613581292029000627043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68755272433557488003344229 12891613581292029000627043)
                ·
                  refine ⟨19337420371938043500940565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12891613581292029000627043 19337420371938043500940565)
                  ·
                    refine ⟨906441579934595789106589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19337420371938043500940565 906441579934595789106589)
                    ·
                      rfl

theorem cell22_2647933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_2647933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2647933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2647933 prefixEnd_2647933 := by exact prefixLift 2647933
  have htrace : WordTrace (prefixWord ++ tailWord_2647933) baseStart_2647933 baseEnd_2647933 := by
    simpa [prefixWord, tailWord_2647933, baseEnd_2647933] using wordTrace_append hprefix tailTrace_2647933
  have hstable : (prefixWord ++ tailWord_2647933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647933).length < 2 ^ (prefixWord ++ tailWord_2647933).sum := by decide
  have hdescent : baseEnd_2647933 < baseStart_2647933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647937 : List Nat := [1, 2, 4, 4, 1, 1, 1, 2, 6]
def baseStart_2647937 : Nat := 118140960795 + 2647937 * 2 ^ 59
def prefixEnd_2647937 : Nat := 4983230072969 + 3 ^ 40 * 2647937 * 2
def baseEnd_2647937 : Nat := 302147649738780370668859

theorem tailTrace_2647937 : CollatzResearch.WordTrace tailWord_2647937 prefixEnd_2647937 302147649738780370668859 := by
  unfold tailWord_2647937
  simp only [CollatzResearch.WordTrace]
  refine ⟨96578196607983955480710065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64385464405322636987140043 96578196607983955480710065)
  ·
    refine ⟨72433647455987966610532549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96578196607983955480710065 72433647455987966610532549)
    ·
      refine ⟨13581308897997743739474853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72433647455987966610532549 13581308897997743739474853)
      ·
        refine ⟨2546495418374576951151535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13581308897997743739474853 2546495418374576951151535)
        ·
          refine ⟨3819743127561865426727303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2546495418374576951151535 3819743127561865426727303)
          ·
            refine ⟨5729614691342798140090955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3819743127561865426727303 5729614691342798140090955)
            ·
              refine ⟨8594422037014197210136433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5729614691342798140090955 8594422037014197210136433)
              ·
                refine ⟨6445816527760647907602325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8594422037014197210136433 6445816527760647907602325)
                ·
                  refine ⟨302147649738780370668859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6445816527760647907602325 302147649738780370668859)
                  ·
                    rfl

theorem cell22_2647937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 6].length) (baseStart_2647937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2647937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2647937 prefixEnd_2647937 := by exact prefixLift 2647937
  have htrace : WordTrace (prefixWord ++ tailWord_2647937) baseStart_2647937 baseEnd_2647937 := by
    simpa [prefixWord, tailWord_2647937, baseEnd_2647937] using wordTrace_append hprefix tailTrace_2647937
  have hstable : (prefixWord ++ tailWord_2647937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647937).length < 2 ^ (prefixWord ++ tailWord_2647937).sum := by decide
  have hdescent : baseEnd_2647937 < baseStart_2647937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647954 : List Nat := [3, 2, 3, 2, 1, 2, 2, 3, 4]
def baseStart_2647954 : Nat := 118140960795 + 2647954 * 2 ^ 59
def prefixEnd_2647954 : Nat := 4983230072969 + 3 ^ 40 * 2647954 * 2
def baseEnd_2647954 : Nat := 302149589554586244777175

theorem tailTrace_2647954 : CollatzResearch.WordTrace tailWord_2647954 prefixEnd_2647954 302149589554586244777175 := by
  unfold tailWord_2647954
  simp only [CollatzResearch.WordTrace]
  refine ⟨24144704162230591846019729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64385877765948244922719277 24144704162230591846019729)
  ·
    refine ⟨18108528121672943884514797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24144704162230591846019729 18108528121672943884514797)
    ·
      refine ⟨6790698045627353956693049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18108528121672943884514797 6790698045627353956693049)
      ·
        refine ⟨5093023534220515467519787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6790698045627353956693049 5093023534220515467519787)
        ·
          refine ⟨7639535301330773201279681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5093023534220515467519787 7639535301330773201279681)
          ·
            refine ⟨5729651475998079900959761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7639535301330773201279681 5729651475998079900959761)
            ·
              refine ⟨4297238606998559925719821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5729651475998079900959761 4297238606998559925719821)
              ·
                refine ⟨1611464477624459972144933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4297238606998559925719821 1611464477624459972144933)
                ·
                  refine ⟨302149589554586244777175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1611464477624459972144933 302149589554586244777175)
                  ·
                    rfl

theorem cell22_2647954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_2647954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2647954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2647954 prefixEnd_2647954 := by exact prefixLift 2647954
  have htrace : WordTrace (prefixWord ++ tailWord_2647954) baseStart_2647954 baseEnd_2647954 := by
    simpa [prefixWord, tailWord_2647954, baseEnd_2647954] using wordTrace_append hprefix tailTrace_2647954
  have hstable : (prefixWord ++ tailWord_2647954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647954).length < 2 ^ (prefixWord ++ tailWord_2647954).sum := by decide
  have hdescent : baseEnd_2647954 < baseStart_2647954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647997 : List Nat := [1, 4, 1, 2, 3, 1, 2, 2, 3, 3]
def baseStart_2647997 : Nat := 118140960795 + 2647997 * 2 ^ 59
def prefixEnd_2647997 : Nat := 4983230072969 + 3 ^ 40 * 2647997 * 2
def baseEnd_2647997 : Nat := 906463488442520955506393

theorem tailTrace_2647997 : CollatzResearch.WordTrace tailWord_2647997 prefixEnd_2647997 906463488442520955506393 := by
  unfold tailWord_2647997
  simp only [CollatzResearch.WordTrace]
  refine ⟨96580384987766585727894245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64386923325177723818596163 96580384987766585727894245)
  ·
    refine ⟨18108822185206234823980171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96580384987766585727894245 18108822185206234823980171)
    ·
      refine ⟨27163233277809352235970257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18108822185206234823980171 27163233277809352235970257)
      ·
        refine ⟨20372424958357014176977693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27163233277809352235970257 20372424958357014176977693)
        ·
          refine ⟨7639659359383880316366635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20372424958357014176977693 7639659359383880316366635)
          ·
            refine ⟨11459489039075820474549953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7639659359383880316366635 11459489039075820474549953)
            ·
              refine ⟨8594616779306865355912465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11459489039075820474549953 8594616779306865355912465)
              ·
                refine ⟨6445962584480149016934349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8594616779306865355912465 6445962584480149016934349)
                ·
                  refine ⟨2417235969180055881350381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6445962584480149016934349 2417235969180055881350381)
                  ·
                    refine ⟨906463488442520955506393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2417235969180055881350381 906463488442520955506393)
                    ·
                      rfl

theorem cell22_2647997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_2647997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2647997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2647997 prefixEnd_2647997 := by exact prefixLift 2647997
  have htrace : WordTrace (prefixWord ++ tailWord_2647997) baseStart_2647997 baseEnd_2647997 := by
    simpa [prefixWord, tailWord_2647997, baseEnd_2647997] using wordTrace_append hprefix tailTrace_2647997
  have hstable : (prefixWord ++ tailWord_2647997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647997).length < 2 ^ (prefixWord ++ tailWord_2647997).sum := by decide
  have hdescent : baseEnd_2647997 < baseStart_2647997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648031 : List Nat := [1, 1, 2, 3, 4, 2, 3, 2, 1, 3]
def baseStart_2648031 : Nat := 118140960795 + 2648031 * 2 ^ 59
def prefixEnd_2648031 : Nat := 4983230072969 + 3 ^ 40 * 2648031 * 2
def baseEnd_2648031 : Nat := 906475127337356200156289

theorem tailTrace_2648031 : CollatzResearch.WordTrace tailWord_2648031 prefixEnd_2648031 906475127337356200156289 := by
  unfold tailWord_2648031
  simp only [CollatzResearch.WordTrace]
  refine ⟨96581625069643409534631947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64387750046428939689754631 96581625069643409534631947)
  ·
    refine ⟨144872437604465114301947921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96581625069643409534631947 144872437604465114301947921)
    ·
      refine ⟨108654328203348835726460941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144872437604465114301947921 108654328203348835726460941)
      ·
        refine ⟨40745373076255813397422853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108654328203348835726460941 40745373076255813397422853)
        ·
          refine ⟨7639757451797965012016785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40745373076255813397422853 7639757451797965012016785)
          ·
            refine ⟨5729818088848473759012589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7639757451797965012016785 5729818088848473759012589)
            ·
              refine ⟨2148681783318177659629721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5729818088848473759012589 2148681783318177659629721)
              ·
                refine ⟨1611511337488633244722291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2148681783318177659629721 1611511337488633244722291)
                ·
                  refine ⟨2417267006232949867083437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1611511337488633244722291 2417267006232949867083437)
                  ·
                    refine ⟨906475127337356200156289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2417267006232949867083437 906475127337356200156289)
                    ·
                      rfl

theorem cell22_2648031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2, 1, 3].length) (baseStart_2648031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648031 prefixEnd_2648031 := by exact prefixLift 2648031
  have htrace : WordTrace (prefixWord ++ tailWord_2648031) baseStart_2648031 baseEnd_2648031 := by
    simpa [prefixWord, tailWord_2648031, baseEnd_2648031] using wordTrace_append hprefix tailTrace_2648031
  have hstable : (prefixWord ++ tailWord_2648031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648031).length < 2 ^ (prefixWord ++ tailWord_2648031).sum := by decide
  have hdescent : baseEnd_2648031 < baseStart_2648031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648040 : List Nat := [2, 1, 4, 1, 1, 1, 1, 4, 3, 4]
def baseStart_2648040 : Nat := 118140960795 + 2648040 * 2 ^ 59
def prefixEnd_2648040 : Nat := 4983230072969 + 3 ^ 40 * 2648040 * 2
def baseEnd_2648040 : Nat := 906478208221283176681261

theorem tailTrace_2648040 : CollatzResearch.WordTrace tailWord_2648040 prefixEnd_2648040 906478208221283176681261 := by
  unfold tailWord_2648040
  simp only [CollatzResearch.WordTrace]
  refine ⟨48290976663305402035854787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64387968884407202714473049 48290976663305402035854787)
  ·
    refine ⟨72436464994958103053782181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48290976663305402035854787 72436464994958103053782181)
    ·
      refine ⟨13581837186554644322584159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72436464994958103053782181 13581837186554644322584159)
      ·
        refine ⟨20372755779831966483876239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13581837186554644322584159 20372755779831966483876239)
        ·
          refine ⟨30559133669747949725814359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20372755779831966483876239 30559133669747949725814359)
          ·
            refine ⟨45838700504621924588721539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30559133669747949725814359 45838700504621924588721539)
            ·
              refine ⟨68758050756932886883082309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45838700504621924588721539 68758050756932886883082309)
              ·
                refine ⟨12892134516924916290577933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68758050756932886883082309 12892134516924916290577933)
                ·
                  refine ⟨4834550443846843608966725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12892134516924916290577933 4834550443846843608966725)
                  ·
                    refine ⟨906478208221283176681261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4834550443846843608966725 906478208221283176681261)
                    ·
                      rfl

theorem cell22_2648040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_2648040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648040 prefixEnd_2648040 := by exact prefixLift 2648040
  have htrace : WordTrace (prefixWord ++ tailWord_2648040) baseStart_2648040 baseEnd_2648040 := by
    simpa [prefixWord, tailWord_2648040, baseEnd_2648040] using wordTrace_append hprefix tailTrace_2648040
  have hstable : (prefixWord ++ tailWord_2648040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648040).length < 2 ^ (prefixWord ++ tailWord_2648040).sum := by decide
  have hdescent : baseEnd_2648040 < baseStart_2648040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648057 : List Nat := [1, 2, 1, 3, 1, 4, 3, 2, 1, 4]
def baseStart_2648057 : Nat := 118140960795 + 2648057 * 2 ^ 59
def prefixEnd_2648057 : Nat := 4983230072969 + 3 ^ 40 * 2648057 * 2
def baseEnd_2648057 : Nat := 906484027668700799006209

theorem tailTrace_2648057 : CollatzResearch.WordTrace tailWord_2648057 prefixEnd_2648057 906484027668700799006209 := by
  unfold tailWord_2648057
  simp only [CollatzResearch.WordTrace]
  refine ⟨96582573367549215975078425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64388382245032810650052283 96582573367549215975078425)
  ·
    refine ⟨72436930025661911981308819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96582573367549215975078425 72436930025661911981308819)
    ·
      refine ⟨108655395038492867971963229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72436930025661911981308819 108655395038492867971963229)
      ·
        refine ⟨40745773139434825489486211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108655395038492867971963229 40745773139434825489486211)
        ·
          refine ⟨61118659709152238234229317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40745773139434825489486211 61118659709152238234229317)
          ·
            refine ⟨11459748695466044668917997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61118659709152238234229317 11459748695466044668917997)
            ·
              refine ⟨4297405760799766750844249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11459748695466044668917997 4297405760799766750844249)
              ·
                refine ⟨3223054320599825063133187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4297405760799766750844249 3223054320599825063133187)
                ·
                  refine ⟨4834581480899737594699781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3223054320599825063133187 4834581480899737594699781)
                  ·
                    refine ⟨906484027668700799006209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4834581480899737594699781 906484027668700799006209)
                    ·
                      rfl

theorem cell22_2648057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 4].length) (baseStart_2648057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648057 prefixEnd_2648057 := by exact prefixLift 2648057
  have htrace : WordTrace (prefixWord ++ tailWord_2648057) baseStart_2648057 baseEnd_2648057 := by
    simpa [prefixWord, tailWord_2648057, baseEnd_2648057] using wordTrace_append hprefix tailTrace_2648057
  have hstable : (prefixWord ++ tailWord_2648057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648057).length < 2 ^ (prefixWord ++ tailWord_2648057).sum := by decide
  have hdescent : baseEnd_2648057 < baseStart_2648057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648072 : List Nat := [2, 1, 3, 2, 1, 2, 2, 5, 4]
def baseStart_2648072 : Nat := 118140960795 + 2648072 * 2 ^ 59
def prefixEnd_2648072 : Nat := 4983230072969 + 3 ^ 40 * 2648072 * 2
def baseEnd_2648072 : Nat := 302163054158415253293721

theorem tailTrace_2648072 : CollatzResearch.WordTrace tailWord_2648072 prefixEnd_2648072 302163054158415253293721 := by
  unfold tailWord_2648072
  simp only [CollatzResearch.WordTrace]
  refine ⟨48291560231247436768437235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64388746974996582357916313 48291560231247436768437235)
  ·
    refine ⟨72437340346871155152655853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48291560231247436768437235 72437340346871155152655853)
    ·
      refine ⟨27164002630076683182245945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72437340346871155152655853 27164002630076683182245945)
      ·
        refine ⟨20373001972557512386684459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27164002630076683182245945 20373001972557512386684459)
        ·
          refine ⟨30559502958836268580026689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20373001972557512386684459 30559502958836268580026689)
          ·
            refine ⟨22919627219127201435020017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30559502958836268580026689 22919627219127201435020017)
            ·
              refine ⟨17189720414345401076265013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22919627219127201435020017 17189720414345401076265013)
              ·
                refine ⟨1611536288844881350899845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17189720414345401076265013 1611536288844881350899845)
                ·
                  refine ⟨302163054158415253293721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1611536288844881350899845 302163054158415253293721)
                  ·
                    rfl

theorem cell22_2648072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5, 4].length) (baseStart_2648072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648072 prefixEnd_2648072 := by exact prefixLift 2648072
  have htrace : WordTrace (prefixWord ++ tailWord_2648072) baseStart_2648072 baseEnd_2648072 := by
    simpa [prefixWord, tailWord_2648072, baseEnd_2648072] using wordTrace_append hprefix tailTrace_2648072
  have hstable : (prefixWord ++ tailWord_2648072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648072).length < 2 ^ (prefixWord ++ tailWord_2648072).sum := by decide
  have hdescent : baseEnd_2648072 < baseStart_2648072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648149 : List Nat := [1, 3, 2, 2, 1, 4, 2, 1, 3, 3]
def baseStart_2648149 : Nat := 118140960795 + 2648149 * 2 ^ 59
def prefixEnd_2648149 : Nat := 4983230072969 + 3 ^ 40 * 2648149 * 2
def baseEnd_2648149 : Nat := 906515521148843225705927

theorem tailTrace_2648149 : CollatzResearch.WordTrace tailWord_2648149 prefixEnd_2648149 906515521148843225705927 := by
  unfold tailWord_2648149
  simp only [CollatzResearch.WordTrace]
  refine ⟨96585928883215915687427501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64390619255477277124951667 96585928883215915687427501)
  ·
    refine ⟨36219723331205968382785313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96585928883215915687427501 36219723331205968382785313)
    ·
      refine ⟨27164792498404476287088985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36219723331205968382785313 27164792498404476287088985)
      ·
        refine ⟨20373594373803357215316739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27164792498404476287088985 20373594373803357215316739)
        ·
          refine ⟨30560391560705035822975109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20373594373803357215316739 30560391560705035822975109)
          ·
            refine ⟨5730073417632194216807833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30560391560705035822975109 5730073417632194216807833)
            ·
              refine ⟨4297555063224145662605875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5730073417632194216807833 4297555063224145662605875)
              ·
                refine ⟨6446332594836218493908813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4297555063224145662605875 6446332594836218493908813)
                ·
                  refine ⟨2417374723063581935215805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6446332594836218493908813 2417374723063581935215805)
                  ·
                    refine ⟨906515521148843225705927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2417374723063581935215805 906515521148843225705927)
                    ·
                      rfl

theorem cell22_2648149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_2648149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648149 prefixEnd_2648149 := by exact prefixLift 2648149
  have htrace : WordTrace (prefixWord ++ tailWord_2648149) baseStart_2648149 baseEnd_2648149 := by
    simpa [prefixWord, tailWord_2648149, baseEnd_2648149] using wordTrace_append hprefix tailTrace_2648149
  have hstable : (prefixWord ++ tailWord_2648149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648149).length < 2 ^ (prefixWord ++ tailWord_2648149).sum := by decide
  have hdescent : baseEnd_2648149 < baseStart_2648149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648226 : List Nat := [3, 3, 1, 3, 1, 1, 3, 2, 1, 4]
def baseStart_2648226 : Nat := 118140960795 + 2648226 * 2 ^ 59
def prefixEnd_2648226 : Nat := 4983230072969 + 3 ^ 40 * 2648226 * 2
def baseEnd_2648226 : Nat := 906541879822440691530691

theorem tailTrace_2648226 : CollatzResearch.WordTrace tailWord_2648226 prefixEnd_2648226 906541879822440691530691 := by
  unfold tailWord_2648226
  simp only [CollatzResearch.WordTrace]
  refine ⟨24147184325984239459495133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64392491535957971891987021 24147184325984239459495133)
  ·
    refine ⟨9055194122244089797310675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24147184325984239459495133 9055194122244089797310675)
    ·
      refine ⟨13582791183366134695966013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9055194122244089797310675 13582791183366134695966013)
      ·
        refine ⟨5093546693762300510987255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13582791183366134695966013 5093546693762300510987255)
        ·
          refine ⟨7640320040643450766480883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5093546693762300510987255 7640320040643450766480883)
          ·
            refine ⟨11460480060965176149721325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7640320040643450766480883 11460480060965176149721325)
            ·
              refine ⟨4297680022861941056145497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11460480060965176149721325 4297680022861941056145497)
              ·
                refine ⟨3223260017146455792109123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4297680022861941056145497 3223260017146455792109123)
                ·
                  refine ⟨4834890025719683688163685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3223260017146455792109123 4834890025719683688163685)
                  ·
                    refine ⟨906541879822440691530691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4834890025719683688163685 906541879822440691530691)
                    ·
                      rfl

theorem cell22_2648226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_2648226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648226 prefixEnd_2648226 := by exact prefixLift 2648226
  have htrace : WordTrace (prefixWord ++ tailWord_2648226) baseStart_2648226 baseEnd_2648226 := by
    simpa [prefixWord, tailWord_2648226, baseEnd_2648226] using wordTrace_append hprefix tailTrace_2648226
  have hstable : (prefixWord ++ tailWord_2648226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648226).length < 2 ^ (prefixWord ++ tailWord_2648226).sum := by decide
  have hdescent : baseEnd_2648226 < baseStart_2648226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648252 : List Nat := [2, 2, 2, 3, 3, 10]
def baseStart_2648252 : Nat := 118140960795 + 2648252 * 2 ^ 59
def prefixEnd_2648252 : Nat := 4983230072969 + 3 ^ 40 * 2648252 * 2
def baseEnd_2648252 : Nat := 11191984940170188770131

theorem tailTrace_2648252 : CollatzResearch.WordTrace tailWord_2648252 prefixEnd_2648252 11191984940170188770131 := by
  unfold tailWord_2648252
  simp only [CollatzResearch.WordTrace]
  refine ⟨48294842800921382139213505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64393123734561842852284673 48294842800921382139213505)
  ·
    refine ⟨36221132100691036604410129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48294842800921382139213505 36221132100691036604410129)
    ·
      refine ⟨27165849075518277453307597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36221132100691036604410129 27165849075518277453307597)
      ·
        refine ⟨10187193403319354044990349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27165849075518277453307597 10187193403319354044990349)
        ·
          refine ⟨3820197526244757766871381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10187193403319354044990349 3820197526244757766871381)
          ·
            refine ⟨11191984940170188770131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3820197526244757766871381 11191984940170188770131)
            ·
              rfl

theorem cell22_2648252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 10].length) (baseStart_2648252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648252 prefixEnd_2648252 := by exact prefixLift 2648252
  have htrace : WordTrace (prefixWord ++ tailWord_2648252) baseStart_2648252 baseEnd_2648252 := by
    simpa [prefixWord, tailWord_2648252, baseEnd_2648252] using wordTrace_append hprefix tailTrace_2648252
  have hstable : (prefixWord ++ tailWord_2648252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648252).length < 2 ^ (prefixWord ++ tailWord_2648252).sum := by decide
  have hdescent : baseEnd_2648252 < baseStart_2648252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648256 : List Nat := [2, 1, 1, 2, 5, 2, 2, 2, 2, 3]
def baseStart_2648256 : Nat := 118140960795 + 2648256 * 2 ^ 59
def prefixEnd_2648256 : Nat := 4983230072969 + 3 ^ 40 * 2648256 * 2
def baseEnd_2648256 : Nat := 906552149435530613280599

theorem tailTrace_2648256 : CollatzResearch.WordTrace tailWord_2648256 prefixEnd_2648256 906552149435530613280599 := by
  unfold tailWord_2648256
  simp only [CollatzResearch.WordTrace]
  refine ⟨48294915746914136480786311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64393220995885515307715081 48294915746914136480786311)
  ·
    refine ⟨72442373620371204721179467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48294915746914136480786311 72442373620371204721179467)
    ·
      refine ⟨108663560430556807081769201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72442373620371204721179467 108663560430556807081769201)
      ·
        refine ⟨81497670322917605311326901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108663560430556807081769201 81497670322917605311326901)
        ·
          refine ⟨7640406592773525497936897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81497670322917605311326901 7640406592773525497936897)
          ·
            refine ⟨5730304944580144123452673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7640406592773525497936897 5730304944580144123452673)
            ·
              refine ⟨4297728708435108092589505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5730304944580144123452673 4297728708435108092589505)
              ·
                refine ⟨3223296531326331069442129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4297728708435108092589505 3223296531326331069442129)
                ·
                  refine ⟨2417472398494748302081597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3223296531326331069442129 2417472398494748302081597)
                  ·
                    refine ⟨906552149435530613280599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2417472398494748302081597 906552149435530613280599)
                    ·
                      rfl

theorem cell22_2648256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 2, 3].length) (baseStart_2648256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648256 prefixEnd_2648256 := by exact prefixLift 2648256
  have htrace : WordTrace (prefixWord ++ tailWord_2648256) baseStart_2648256 baseEnd_2648256 := by
    simpa [prefixWord, tailWord_2648256, baseEnd_2648256] using wordTrace_append hprefix tailTrace_2648256
  have hstable : (prefixWord ++ tailWord_2648256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648256).length < 2 ^ (prefixWord ++ tailWord_2648256).sum := by decide
  have hdescent : baseEnd_2648256 < baseStart_2648256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648314 : List Nat := [3, 1, 1, 1, 1, 5, 3, 2, 5]
def baseStart_2648314 : Nat := 118140960795 + 2648314 * 2 ^ 59
def prefixEnd_2648314 : Nat := 4983230072969 + 3 ^ 40 * 2648314 * 2
def baseEnd_2648314 : Nat := 302190668006945931776807

theorem tailTrace_2648314 : CollatzResearch.WordTrace tailWord_2648314 prefixEnd_2648314 302190668006945931776807 := by
  unfold tailWord_2648314
  simp only [CollatzResearch.WordTrace]
  refine ⟨24147986731904537216795999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64394631285078765911455997 24147986731904537216795999)
  ·
    refine ⟨36221980097856805825193999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24147986731904537216795999 36221980097856805825193999)
    ·
      refine ⟨54332970146785208737790999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36221980097856805825193999 54332970146785208737790999)
      ·
        refine ⟨81499455220177813106686499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54332970146785208737790999 81499455220177813106686499)
        ·
          refine ⟨122249182830266719660029749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81499455220177813106686499 122249182830266719660029749)
          ·
            refine ⟨11460860890337504968127789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122249182830266719660029749 11460860890337504968127789)
            ·
              refine ⟨4297822833876564363047921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11460860890337504968127789 4297822833876564363047921)
              ·
                refine ⟨3223367125407423272285941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4297822833876564363047921 3223367125407423272285941)
                ·
                  refine ⟨302190668006945931776807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3223367125407423272285941 302190668006945931776807)
                  ·
                    rfl

theorem cell22_2648314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 5].length) (baseStart_2648314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648314 prefixEnd_2648314 := by exact prefixLift 2648314
  have htrace : WordTrace (prefixWord ++ tailWord_2648314) baseStart_2648314 baseEnd_2648314 := by
    simpa [prefixWord, tailWord_2648314, baseEnd_2648314] using wordTrace_append hprefix tailTrace_2648314
  have hstable : (prefixWord ++ tailWord_2648314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648314).length < 2 ^ (prefixWord ++ tailWord_2648314).sum := by decide
  have hdescent : baseEnd_2648314 < baseStart_2648314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648318 : List Nat := [4, 2, 2, 1, 1, 1, 1, 6, 1, 3]
def baseStart_2648318 : Nat := 118140960795 + 2648318 * 2 ^ 59
def prefixEnd_2648318 : Nat := 4983230072969 + 3 ^ 40 * 2648318 * 2
def baseEnd_2648318 : Nat := 906573373302583118230409

theorem tailTrace_2648318 : CollatzResearch.WordTrace tailWord_2648318 prefixEnd_2648318 906573373302583118230409 := by
  unfold tailWord_2648318
  simp only [CollatzResearch.WordTrace]
  refine ⟨12074011602450457193791201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64394728546402438366886405 12074011602450457193791201)
  ·
    refine ⟨9055508701837842895343401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12074011602450457193791201 9055508701837842895343401)
    ·
      refine ⟨6791631526378382171507551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9055508701837842895343401 6791631526378382171507551)
      ·
        refine ⟨10187447289567573257261327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6791631526378382171507551 10187447289567573257261327)
        ·
          refine ⟨15281170934351359885891991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10187447289567573257261327 15281170934351359885891991)
          ·
            refine ⟨22921756401527039828837987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15281170934351359885891991 22921756401527039828837987)
            ·
              refine ⟨34382634602290559743256981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22921756401527039828837987 34382634602290559743256981)
              ·
                refine ⟨1611685996982369987965171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34382634602290559743256981 1611685996982369987965171)
                ·
                  refine ⟨2417528995473554981947757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1611685996982369987965171 2417528995473554981947757)
                  ·
                    refine ⟨906573373302583118230409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2417528995473554981947757 906573373302583118230409)
                    ·
                      rfl

theorem cell22_2648318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_2648318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648318 prefixEnd_2648318 := by exact prefixLift 2648318
  have htrace : WordTrace (prefixWord ++ tailWord_2648318) baseStart_2648318 baseEnd_2648318 := by
    simpa [prefixWord, tailWord_2648318, baseEnd_2648318] using wordTrace_append hprefix tailTrace_2648318
  have hstable : (prefixWord ++ tailWord_2648318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648318).length < 2 ^ (prefixWord ++ tailWord_2648318).sum := by decide
  have hdescent : baseEnd_2648318 < baseStart_2648318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648387 : List Nat := [1, 1, 1, 3, 1, 3, 3, 9]
def baseStart_2648387 : Nat := 118140960795 + 2648387 * 2 ^ 59
def prefixEnd_2648387 : Nat := 4983230072969 + 3 ^ 40 * 2648387 * 2
def baseEnd_2648387 : Nat := 100732999268076659806133

theorem tailTrace_2648387 : CollatzResearch.WordTrace tailWord_2648387 prefixEnd_2648387 100732999268076659806133 := by
  unfold tailWord_2648387
  simp only [CollatzResearch.WordTrace]
  refine ⟨96594609456353682334591415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64396406304235788223060943 96594609456353682334591415)
  ·
    refine ⟨144891914184530523501887123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96594609456353682334591415 144891914184530523501887123)
    ·
      refine ⟨217337871276795785252830685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144891914184530523501887123 217337871276795785252830685)
      ·
        refine ⟨81501701728798419469811507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217337871276795785252830685 81501701728798419469811507)
        ·
          refine ⟨122252552593197629204717261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81501701728798419469811507 122252552593197629204717261)
          ·
            refine ⟨45844707222449110951768973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122252552593197629204717261 45844707222449110951768973)
            ·
              refine ⟨17191765208418416606913365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45844707222449110951768973 17191765208418416606913365)
              ·
                refine ⟨100732999268076659806133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17191765208418416606913365 100732999268076659806133)
                ·
                  rfl

theorem cell22_2648387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 9].length) (baseStart_2648387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648387 prefixEnd_2648387 := by exact prefixLift 2648387
  have htrace : WordTrace (prefixWord ++ tailWord_2648387) baseStart_2648387 baseEnd_2648387 := by
    simpa [prefixWord, tailWord_2648387, baseEnd_2648387] using wordTrace_append hprefix tailTrace_2648387
  have hstable : (prefixWord ++ tailWord_2648387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648387).length < 2 ^ (prefixWord ++ tailWord_2648387).sum := by decide
  have hdescent : baseEnd_2648387 < baseStart_2648387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648391 : List Nat := [1, 1, 4, 1, 2, 2, 3, 3, 2, 3]
def baseStart_2648391 : Nat := 118140960795 + 2648391 * 2 ^ 59
def prefixEnd_2648391 : Nat := 4983230072969 + 3 ^ 40 * 2648391 * 2
def baseEnd_2648391 : Nat := 906598362694435261155185

theorem tailTrace_2648391 : CollatzResearch.WordTrace tailWord_2648391 prefixEnd_2648391 906598362694435261155185 := by
  unfold tailWord_2648391
  simp only [CollatzResearch.WordTrace]
  refine ⟨96594755348339191017737027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64396503565559460678491351 96594755348339191017737027)
  ·
    refine ⟨144892133022508786526605541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96594755348339191017737027 144892133022508786526605541)
    ·
      refine ⟨27167274941720397473738539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144892133022508786526605541 27167274941720397473738539)
      ·
        refine ⟨40750912412580596210607809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27167274941720397473738539 40750912412580596210607809)
        ·
          refine ⟨30563184309435447157955857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40750912412580596210607809 30563184309435447157955857)
          ·
            refine ⟨22922388232076585368466893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30563184309435447157955857 22922388232076585368466893)
            ·
              refine ⟨8595895587028719513175085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22922388232076585368466893 8595895587028719513175085)
              ·
                refine ⟨3223460845135769817440657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8595895587028719513175085 3223460845135769817440657)
                ·
                  refine ⟨2417595633851827363080493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3223460845135769817440657 2417595633851827363080493)
                  ·
                    refine ⟨906598362694435261155185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2417595633851827363080493 906598362694435261155185)
                    ·
                      rfl

theorem cell22_2648391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_2648391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648391 prefixEnd_2648391 := by exact prefixLift 2648391
  have htrace : WordTrace (prefixWord ++ tailWord_2648391) baseStart_2648391 baseEnd_2648391 := by
    simpa [prefixWord, tailWord_2648391, baseEnd_2648391] using wordTrace_append hprefix tailTrace_2648391
  have hstable : (prefixWord ++ tailWord_2648391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648391).length < 2 ^ (prefixWord ++ tailWord_2648391).sum := by decide
  have hdescent : baseEnd_2648391 < baseStart_2648391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648404 : List Nat := [2, 4, 1, 1, 2, 2, 2, 8]
def baseStart_2648404 : Nat := 118140960795 + 2648404 * 2 ^ 59
def prefixEnd_2648404 : Nat := 4983230072969 + 3 ^ 40 * 2648404 * 2
def baseEnd_2648404 : Nat := 100733645873345284508905

theorem tailTrace_2648404 : CollatzResearch.WordTrace tailWord_2648404 prefixEnd_2648404 100733645873345284508905 := by
  unfold tailWord_2648404
  simp only [CollatzResearch.WordTrace]
  refine ⟨48297614748646047118980133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64396819664861396158640177 48297614748646047118980133)
  ·
    refine ⟨9055802765371133834808775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48297614748646047118980133 9055802765371133834808775)
    ·
      refine ⟨13583704148056700752213163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9055802765371133834808775 13583704148056700752213163)
      ·
        refine ⟨20375556222085051128319745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13583704148056700752213163 20375556222085051128319745)
        ·
          refine ⟨15281667166563788346239809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20375556222085051128319745 15281667166563788346239809)
          ·
            refine ⟨11461250374922841259679857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15281667166563788346239809 11461250374922841259679857)
            ·
              refine ⟨8595937781192130944759893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11461250374922841259679857 8595937781192130944759893)
              ·
                refine ⟨100733645873345284508905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8595937781192130944759893 100733645873345284508905)
                ·
                  rfl

theorem cell22_2648404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 8].length) (baseStart_2648404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648404 prefixEnd_2648404 := by exact prefixLift 2648404
  have htrace : WordTrace (prefixWord ++ tailWord_2648404) baseStart_2648404 baseEnd_2648404 := by
    simpa [prefixWord, tailWord_2648404, baseEnd_2648404] using wordTrace_append hprefix tailTrace_2648404
  have hstable : (prefixWord ++ tailWord_2648404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648404).length < 2 ^ (prefixWord ++ tailWord_2648404).sum := by decide
  have hdescent : baseEnd_2648404 < baseStart_2648404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648434 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 2, 6]
def baseStart_2648434 : Nat := 118140960795 + 2648434 * 2 ^ 59
def prefixEnd_2648434 : Nat := 4983230072969 + 3 ^ 40 * 2648434 * 2
def baseEnd_2648434 : Nat := 906613082473197482330053

theorem tailTrace_2648434 : CollatzResearch.WordTrace tailWord_2648434 prefixEnd_2648434 906613082473197482330053 := by
  unfold tailWord_2648434
  simp only [CollatzResearch.WordTrace]
  refine ⟨24149080921795852340388089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64397549124788939574368237 24149080921795852340388089)
  ·
    refine ⟨18111810691346889255291067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24149080921795852340388089 18111810691346889255291067)
    ·
      refine ⟨27167716037020333882936601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18111810691346889255291067 27167716037020333882936601)
      ·
        refine ⟨20375787027765250412202451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27167716037020333882936601 20375787027765250412202451)
        ·
          refine ⟨30563680541647875618303677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20375787027765250412202451 30563680541647875618303677)
          ·
            refine ⟨11461380203117953356863879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30563680541647875618303677 11461380203117953356863879)
            ·
              refine ⟨17192070304676930035295819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11461380203117953356863879 17192070304676930035295819)
              ·
                refine ⟨25788105457015395052943729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17192070304676930035295819 25788105457015395052943729)
                ·
                  refine ⟨19341079092761546289707797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25788105457015395052943729 19341079092761546289707797)
                  ·
                    refine ⟨906613082473197482330053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19341079092761546289707797 906613082473197482330053)
                    ·
                      rfl

theorem cell22_2648434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_2648434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648434 prefixEnd_2648434 := by exact prefixLift 2648434
  have htrace : WordTrace (prefixWord ++ tailWord_2648434) baseStart_2648434 baseEnd_2648434 := by
    simpa [prefixWord, tailWord_2648434, baseEnd_2648434] using wordTrace_append hprefix tailTrace_2648434
  have hstable : (prefixWord ++ tailWord_2648434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648434).length < 2 ^ (prefixWord ++ tailWord_2648434).sum := by decide
  have hdescent : baseEnd_2648434 < baseStart_2648434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648618 : List Nat := [3, 1, 4, 1, 1, 2, 2, 3, 5]
def baseStart_2648618 : Nat := 118140960795 + 2648618 * 2 ^ 59
def prefixEnd_2648618 : Nat := 4983230072969 + 3 ^ 40 * 2648618 * 2
def baseEnd_2648618 : Nat := 302225356477827445243163

theorem tailTrace_2648618 : CollatzResearch.WordTrace tailWord_2648618 prefixEnd_2648618 302225356477827445243163 := by
  unfold tailWord_2648618
  simp only [CollatzResearch.WordTrace]
  refine ⟨24150758679629202196562627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64402023145677872524167005 24150758679629202196562627)
  ·
    refine ⟨36226138019443803294843941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24150758679629202196562627 36226138019443803294843941)
    ·
      refine ⟨6792400878645713117783239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36226138019443803294843941 6792400878645713117783239)
      ·
        refine ⟨10188601317968569676674859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6792400878645713117783239 10188601317968569676674859)
        ·
          refine ⟨15282901976952854515012289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10188601317968569676674859 15282901976952854515012289)
          ·
            refine ⟨11462176482714640886259217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15282901976952854515012289 11462176482714640886259217)
            ·
              refine ⟨8596632362035980664694413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11462176482714640886259217 8596632362035980664694413)
              ·
                refine ⟨3223737135763492749260405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8596632362035980664694413 3223737135763492749260405)
                ·
                  refine ⟨302225356477827445243163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3223737135763492749260405 302225356477827445243163)
                  ·
                    rfl

theorem cell22_2648618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 5].length) (baseStart_2648618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648618 prefixEnd_2648618 := by exact prefixLift 2648618
  have htrace : WordTrace (prefixWord ++ tailWord_2648618) baseStart_2648618 baseEnd_2648618 := by
    simpa [prefixWord, tailWord_2648618, baseEnd_2648618] using wordTrace_append hprefix tailTrace_2648618
  have hstable : (prefixWord ++ tailWord_2648618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648618).length < 2 ^ (prefixWord ++ tailWord_2648618).sum := by decide
  have hdescent : baseEnd_2648618 < baseStart_2648618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648631 : List Nat := [1, 1, 3, 1, 2, 3, 1, 3, 3, 4]
def baseStart_2648631 : Nat := 118140960795 + 2648631 * 2 ^ 59
def prefixEnd_2648631 : Nat := 4983230072969 + 3 ^ 40 * 2648631 * 2
def baseEnd_2648631 : Nat := 906680519599154635154449

theorem tailTrace_2648631 : CollatzResearch.WordTrace tailWord_2648631 prefixEnd_2648631 906680519599154635154449 := by
  unfold tailWord_2648631
  simp only [CollatzResearch.WordTrace]
  refine ⟨96603508867469712006473747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64402339244979808004315831 96603508867469712006473747)
  ·
    refine ⟨144905263301204568009710621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96603508867469712006473747 144905263301204568009710621)
    ·
      refine ⟨54339473737951713003641483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144905263301204568009710621 54339473737951713003641483)
      ·
        refine ⟨81509210606927569505462225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54339473737951713003641483 81509210606927569505462225)
        ·
          refine ⟨61131907955195677129096669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81509210606927569505462225 61131907955195677129096669)
          ·
            refine ⟨22924465483198378923411251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61131907955195677129096669 22924465483198378923411251)
            ·
              refine ⟨34386698224797568385116877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22924465483198378923411251 34386698224797568385116877)
              ·
                refine ⟨12895011834299088144418829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34386698224797568385116877 12895011834299088144418829)
                ·
                  refine ⟨4835629437862158054157061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12895011834299088144418829 4835629437862158054157061)
                  ·
                    refine ⟨906680519599154635154449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4835629437862158054157061 906680519599154635154449)
                    ·
                      rfl

theorem cell22_2648631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_2648631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648631 prefixEnd_2648631 := by exact prefixLift 2648631
  have htrace : WordTrace (prefixWord ++ tailWord_2648631) baseStart_2648631 baseEnd_2648631 := by
    simpa [prefixWord, tailWord_2648631, baseEnd_2648631] using wordTrace_append hprefix tailTrace_2648631
  have hstable : (prefixWord ++ tailWord_2648631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648631).length < 2 ^ (prefixWord ++ tailWord_2648631).sum := by decide
  have hdescent : baseEnd_2648631 < baseStart_2648631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648661 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 3, 5]
def baseStart_2648661 : Nat := 118140960795 + 2648661 * 2 ^ 59
def prefixEnd_2648661 : Nat := 4983230072969 + 3 ^ 40 * 2648661 * 2
def baseEnd_2648661 : Nat := 906690789212244556904357

theorem tailTrace_2648661 : CollatzResearch.WordTrace tailWord_2648661 prefixEnd_2648661 906690789212244556904357 := by
  unfold tailWord_2648661
  simp only [CollatzResearch.WordTrace]
  refine ⟨96604603057361027130065837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64403068704907351420043891 96604603057361027130065837)
  ·
    refine ⟨36226726146510385173774689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96604603057361027130065837 36226726146510385173774689)
    ·
      refine ⟨27170044609882788880331017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36226726146510385173774689 27170044609882788880331017)
      ·
        refine ⟨20377533457412091660248263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27170044609882788880331017 20377533457412091660248263)
        ·
          refine ⟨30566300186118137490372395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20377533457412091660248263 30566300186118137490372395)
          ·
            refine ⟨45849450279177206235558593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30566300186118137490372395 45849450279177206235558593)
            ·
              refine ⟨34387087709382904676668945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45849450279177206235558593 34387087709382904676668945)
              ·
                refine ⟨25790315782037178507501709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34387087709382904676668945 25790315782037178507501709)
                ·
                  refine ⟨9671368418263941940313141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25790315782037178507501709 9671368418263941940313141)
                  ·
                    refine ⟨906690789212244556904357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9671368418263941940313141 906690789212244556904357)
                    ·
                      rfl

theorem cell22_2648661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_2648661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648661 prefixEnd_2648661 := by exact prefixLift 2648661
  have htrace : WordTrace (prefixWord ++ tailWord_2648661) baseStart_2648661 baseEnd_2648661 := by
    simpa [prefixWord, tailWord_2648661, baseEnd_2648661] using wordTrace_append hprefix tailTrace_2648661
  have hstable : (prefixWord ++ tailWord_2648661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648661).length < 2 ^ (prefixWord ++ tailWord_2648661).sum := by decide
  have hdescent : baseEnd_2648661 < baseStart_2648661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648663 : List Nat := [1, 1, 3, 2, 2, 2, 1, 6, 4]
def baseStart_2648663 : Nat := 118140960795 + 2648663 * 2 ^ 59
def prefixEnd_2648663 : Nat := 4983230072969 + 3 ^ 40 * 2648663 * 2
def baseEnd_2648663 : Nat := 302230491284372406118117

theorem tailTrace_2648663 : CollatzResearch.WordTrace tailWord_2648663 prefixEnd_2648663 302230491284372406118117 := by
  unfold tailWord_2648663
  simp only [CollatzResearch.WordTrace]
  refine ⟨96604676003353781471638643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64403117335569187647759095 96604676003353781471638643)
  ·
    refine ⟨144907014005030672207457965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96604676003353781471638643 144907014005030672207457965)
    ·
      refine ⟨54340130251886502077796737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144907014005030672207457965 54340130251886502077796737)
      ·
        refine ⟨40755097688914876558347553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54340130251886502077796737 40755097688914876558347553)
        ·
          refine ⟨30566323266686157418760665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40755097688914876558347553 30566323266686157418760665)
          ·
            refine ⟨22924742450014618064070499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30566323266686157418760665 22924742450014618064070499)
            ·
              refine ⟨34387113675021927096105749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22924742450014618064070499 34387113675021927096105749)
              ·
                refine ⟨1611895953516652832629957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34387113675021927096105749 1611895953516652832629957)
                ·
                  refine ⟨302230491284372406118117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1611895953516652832629957 302230491284372406118117)
                  ·
                    rfl

theorem cell22_2648663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6, 4].length) (baseStart_2648663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648663 prefixEnd_2648663 := by exact prefixLift 2648663
  have htrace : WordTrace (prefixWord ++ tailWord_2648663) baseStart_2648663 baseEnd_2648663 := by
    simpa [prefixWord, tailWord_2648663, baseEnd_2648663] using wordTrace_append hprefix tailTrace_2648663
  have hstable : (prefixWord ++ tailWord_2648663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648663).length < 2 ^ (prefixWord ++ tailWord_2648663).sum := by decide
  have hdescent : baseEnd_2648663 < baseStart_2648663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648676 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 3, 6]
def baseStart_2648676 : Nat := 118140960795 + 2648676 * 2 ^ 59
def prefixEnd_2648676 : Nat := 4983230072969 + 3 ^ 40 * 2648676 * 2
def baseEnd_2648676 : Nat := 906695924018789517779311

theorem tailTrace_2648676 : CollatzResearch.WordTrace tailWord_2648676 prefixEnd_2648676 906695924018789517779311 := by
  unfold tailWord_2648676
  simp only [CollatzResearch.WordTrace]
  refine ⟨48302575076153342345930941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64403433434871123127907921 48302575076153342345930941)
  ·
    refine ⟨18113465653557503379724103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48302575076153342345930941 18113465653557503379724103)
    ·
      refine ⟨27170198480336255069586155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18113465653557503379724103 27170198480336255069586155)
      ·
        refine ⟨40755297720504382604379233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27170198480336255069586155 40755297720504382604379233)
        ·
          refine ⟨30566473290378286953284425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40755297720504382604379233 30566473290378286953284425)
          ·
            refine ⟨22924854967783715214963319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30566473290378286953284425 22924854967783715214963319)
            ·
              refine ⟨34387282451675572822444979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22924854967783715214963319 34387282451675572822444979)
              ·
                refine ⟨51580923677513359233667469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34387282451675572822444979 51580923677513359233667469)
                ·
                  refine ⟨19342846379067509712625301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51580923677513359233667469 19342846379067509712625301)
                  ·
                    refine ⟨906695924018789517779311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19342846379067509712625301 906695924018789517779311)
                    ·
                      rfl

theorem cell22_2648676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_2648676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648676 prefixEnd_2648676 := by exact prefixLift 2648676
  have htrace : WordTrace (prefixWord ++ tailWord_2648676) baseStart_2648676 baseEnd_2648676 := by
    simpa [prefixWord, tailWord_2648676, baseEnd_2648676] using wordTrace_append hprefix tailTrace_2648676
  have hstable : (prefixWord ++ tailWord_2648676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648676).length < 2 ^ (prefixWord ++ tailWord_2648676).sum := by decide
  have hdescent : baseEnd_2648676 < baseStart_2648676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648708 : List Nat := [2, 3, 2, 1, 3, 3, 8]
def baseStart_2648708 : Nat := 118140960795 + 2648708 * 2 ^ 59
def prefixEnd_2648708 : Nat := 4983230072969 + 3 ^ 40 * 2648708 * 2
def baseEnd_2648708 : Nat := 33581736232324151888119

theorem tailTrace_2648708 : CollatzResearch.WordTrace tailWord_2648708 prefixEnd_2648708 33581736232324151888119 := by
  unfold tailWord_2648708
  simp only [CollatzResearch.WordTrace]
  refine ⟨48303158644095377078513389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64404211525460502771351185 48303158644095377078513389)
  ·
    refine ⟨18113684491535766404442521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48303158644095377078513389 18113684491535766404442521)
    ·
      refine ⟨13585263368651824803331891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18113684491535766404442521 13585263368651824803331891)
      ·
        refine ⟨20377895052977737204997837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13585263368651824803331891 20377895052977737204997837)
        ·
          refine ⟨7641710644866651451874189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20377895052977737204997837 7641710644866651451874189)
          ·
            refine ⟨2865641491824994294452821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7641710644866651451874189 2865641491824994294452821)
            ·
              refine ⟨33581736232324151888119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2865641491824994294452821 33581736232324151888119)
              ·
                rfl

theorem cell22_2648708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 8].length) (baseStart_2648708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648708 prefixEnd_2648708 := by exact prefixLift 2648708
  have htrace : WordTrace (prefixWord ++ tailWord_2648708) baseStart_2648708 baseEnd_2648708 := by
    simpa [prefixWord, tailWord_2648708, baseEnd_2648708] using wordTrace_append hprefix tailTrace_2648708
  have hstable : (prefixWord ++ tailWord_2648708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648708).length < 2 ^ (prefixWord ++ tailWord_2648708).sum := by decide
  have hdescent : baseEnd_2648708 < baseStart_2648708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648815 : List Nat := [1, 1, 2, 1, 5, 2, 1, 5, 4]
def baseStart_2648815 : Nat := 118140960795 + 2648815 * 2 ^ 59
def prefixEnd_2648815 : Nat := 4983230072969 + 3 ^ 40 * 2648815 * 2
def baseEnd_2648815 : Nat := 302247835519813162851295

theorem tailTrace_2648815 : CollatzResearch.WordTrace tailWord_2648815 prefixEnd_2648815 302247835519813162851295 := by
  unfold tailWord_2648815
  simp only [CollatzResearch.WordTrace]
  refine ⟨96610219898803111431171899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64406813265868740954114599 96610219898803111431171899)
  ·
    refine ⟨144915329848204667146757849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96610219898803111431171899 144915329848204667146757849)
    ·
      refine ⟨108686497386153500360068387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144915329848204667146757849 108686497386153500360068387)
      ·
        refine ⟨163029746079230250540102581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108686497386153500360068387 163029746079230250540102581)
        ·
          refine ⟨15284038694927835988134617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 163029746079230250540102581 15284038694927835988134617)
          ·
            refine ⟨11463029021195876991100963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15284038694927835988134617 11463029021195876991100963)
            ·
              refine ⟨17194543531793815486651445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11463029021195876991100963 17194543531793815486651445)
              ·
                refine ⟨1611988456105670201873573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17194543531793815486651445 1611988456105670201873573)
                ·
                  refine ⟨302247835519813162851295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1611988456105670201873573 302247835519813162851295)
                  ·
                    rfl

theorem cell22_2648815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5, 4].length) (baseStart_2648815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648815 prefixEnd_2648815 := by exact prefixLift 2648815
  have htrace : WordTrace (prefixWord ++ tailWord_2648815) baseStart_2648815 baseEnd_2648815 := by
    simpa [prefixWord, tailWord_2648815, baseEnd_2648815] using wordTrace_append hprefix tailTrace_2648815
  have hstable : (prefixWord ++ tailWord_2648815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648815).length < 2 ^ (prefixWord ++ tailWord_2648815).sum := by decide
  have hdescent : baseEnd_2648815 < baseStart_2648815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648821 : List Nat := [1, 3, 6, 1, 1, 2, 1, 2, 5]
def baseStart_2648821 : Nat := 118140960795 + 2648821 * 2 ^ 59
def prefixEnd_2648821 : Nat := 4983230072969 + 3 ^ 40 * 2648821 * 2
def baseEnd_2648821 : Nat := 302248520160685824301289

theorem tailTrace_2648821 : CollatzResearch.WordTrace tailWord_2648821 prefixEnd_2648821 302248520160685824301289 := by
  unfold tailWord_2648821
  simp only [CollatzResearch.WordTrace]
  refine ⟨96610438736781374455890317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64406959157854249637260211 96610438736781374455890317)
  ·
    refine ⟨36228914526293015420958869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96610438736781374455890317 36228914526293015420958869)
    ·
      refine ⟨1698230368419985097857447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36228914526293015420958869 1698230368419985097857447)
      ·
        refine ⟨2547345552629977646786171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1698230368419985097857447 2547345552629977646786171)
        ·
          refine ⟨3821018328944966470179257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2547345552629977646786171 3821018328944966470179257)
          ·
            refine ⟨2865763746708724852634443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3821018328944966470179257 2865763746708724852634443)
            ·
              refine ⟨4298645620063087278951665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2865763746708724852634443 4298645620063087278951665)
              ·
                refine ⟨3223984215047315459213749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4298645620063087278951665 3223984215047315459213749)
                ·
                  refine ⟨302248520160685824301289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3223984215047315459213749 302248520160685824301289)
                  ·
                    rfl

theorem cell22_2648821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 5].length) (baseStart_2648821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648821 prefixEnd_2648821 := by exact prefixLift 2648821
  have htrace : WordTrace (prefixWord ++ tailWord_2648821) baseStart_2648821 baseEnd_2648821 := by
    simpa [prefixWord, tailWord_2648821, baseEnd_2648821] using wordTrace_append hprefix tailTrace_2648821
  have hstable : (prefixWord ++ tailWord_2648821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648821).length < 2 ^ (prefixWord ++ tailWord_2648821).sum := by decide
  have hdescent : baseEnd_2648821 < baseStart_2648821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648847 : List Nat := [1, 1, 2, 1, 1, 1, 9, 1, 2, 3]
def baseStart_2648847 : Nat := 118140960795 + 2648847 * 2 ^ 59
def prefixEnd_2648847 : Nat := 4983230072969 + 3 ^ 40 * 2648847 * 2
def baseEnd_2648847 : Nat := 906754460813402071753787

theorem tailTrace_2648847 : CollatzResearch.WordTrace tailWord_2648847 prefixEnd_2648847 906754460813402071753787 := by
  unfold tailWord_2648847
  simp only [CollatzResearch.WordTrace]
  refine ⟨96611387034687180896336795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64407591356458120597557863 96611387034687180896336795)
  ·
    refine ⟨144917080552030771344505193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96611387034687180896336795 144917080552030771344505193)
    ·
      refine ⟨108687810414023078508378895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144917080552030771344505193 108687810414023078508378895)
      ·
        refine ⟨163031715621034617762568343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108687810414023078508378895 163031715621034617762568343)
        ·
          refine ⟨244547573431551926643852515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163031715621034617762568343 244547573431551926643852515)
          ·
            refine ⟨366821360147327889965778773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244547573431551926643852515 366821360147327889965778773)
            ·
              refine ⟨2149343907113249355268235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 366821360147327889965778773 2149343907113249355268235)
              ·
                refine ⟨3224015860669874032902353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2149343907113249355268235 3224015860669874032902353)
                ·
                  refine ⟨2418011895502405524676765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3224015860669874032902353 2418011895502405524676765)
                  ·
                    refine ⟨906754460813402071753787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2418011895502405524676765 906754460813402071753787)
                    ·
                      rfl

theorem cell22_2648847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 2, 3].length) (baseStart_2648847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648847 prefixEnd_2648847 := by exact prefixLift 2648847
  have htrace : WordTrace (prefixWord ++ tailWord_2648847) baseStart_2648847 baseEnd_2648847 := by
    simpa [prefixWord, tailWord_2648847, baseEnd_2648847] using wordTrace_append hprefix tailTrace_2648847
  have hstable : (prefixWord ++ tailWord_2648847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648847).length < 2 ^ (prefixWord ++ tailWord_2648847).sum := by decide
  have hdescent : baseEnd_2648847 < baseStart_2648847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648858 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 2, 7]
def baseStart_2648858 : Nat := 118140960795 + 2648858 * 2 ^ 59
def prefixEnd_2648858 : Nat := 4983230072969 + 3 ^ 40 * 2648858 * 2
def baseEnd_2648858 : Nat := 906758226338201709728753

theorem tailTrace_2648858 : CollatzResearch.WordTrace tailWord_2648858 prefixEnd_2648858 906758226338201709728753 := by
  unfold tailWord_2648858
  simp only [CollatzResearch.WordTrace]
  refine ⟨24152947059411832443746807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64407858825098219849991485 24152947059411832443746807)
  ·
    refine ⟨36229420589117748665620211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24152947059411832443746807 36229420589117748665620211)
    ·
      refine ⟨54344130883676622998430317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36229420589117748665620211 54344130883676622998430317)
      ·
        refine ⟨20379049081378733624411369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54344130883676622998430317 20379049081378733624411369)
        ·
          refine ⟨15284286811034050218308527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20379049081378733624411369 15284286811034050218308527)
          ·
            refine ⟨22926430216551075327462791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15284286811034050218308527 22926430216551075327462791)
            ·
              refine ⟨34389645324826612991194187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22926430216551075327462791 34389645324826612991194187)
              ·
                refine ⟨51584467987239919486791281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34389645324826612991194187 51584467987239919486791281)
                ·
                  refine ⟨38688350990429939615093461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51584467987239919486791281 38688350990429939615093461)
                  ·
                    refine ⟨906758226338201709728753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38688350990429939615093461 906758226338201709728753)
                    ·
                      rfl

theorem cell22_2648858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_2648858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648858 prefixEnd_2648858 := by exact prefixLift 2648858
  have htrace : WordTrace (prefixWord ++ tailWord_2648858) baseStart_2648858 baseEnd_2648858 := by
    simpa [prefixWord, tailWord_2648858, baseEnd_2648858] using wordTrace_append hprefix tailTrace_2648858
  have hstable : (prefixWord ++ tailWord_2648858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648858).length < 2 ^ (prefixWord ++ tailWord_2648858).sum := by decide
  have hdescent : baseEnd_2648858 < baseStart_2648858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648860 : List Nat := [2, 2, 3, 1, 1, 3, 4, 6]
def baseStart_2648860 : Nat := 118140960795 + 2648860 * 2 ^ 59
def prefixEnd_2648860 : Nat := 4983230072969 + 3 ^ 40 * 2648860 * 2
def baseEnd_2648860 : Nat := 100750990108786041242083

theorem tailTrace_2648860 : CollatzResearch.WordTrace tailWord_2648860 prefixEnd_2648860 100750990108786041242083 := by
  unfold tailWord_2648860
  simp only [CollatzResearch.WordTrace]
  refine ⟨48305930591820042058280017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64407907455760056077706689 48305930591820042058280017)
  ·
    refine ⟨36229447943865031543710013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48305930591820042058280017 36229447943865031543710013)
    ·
      refine ⟨13586042978949386828891255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36229447943865031543710013 13586042978949386828891255)
      ·
        refine ⟨20379064468424080243336883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13586042978949386828891255 20379064468424080243336883)
        ·
          refine ⟨30568596702636120365005325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20379064468424080243336883 30568596702636120365005325)
          ·
            refine ⟨11463223763488545136876997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30568596702636120365005325 11463223763488545136876997)
            ·
              refine ⟨2149354455654102213164437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11463223763488545136876997 2149354455654102213164437)
              ·
                refine ⟨100750990108786041242083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2149354455654102213164437 100750990108786041242083)
                ·
                  rfl

theorem cell22_2648860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 6].length) (baseStart_2648860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648860 prefixEnd_2648860 := by exact prefixLift 2648860
  have htrace : WordTrace (prefixWord ++ tailWord_2648860) baseStart_2648860 baseEnd_2648860 := by
    simpa [prefixWord, tailWord_2648860, baseEnd_2648860] using wordTrace_append hprefix tailTrace_2648860
  have hstable : (prefixWord ++ tailWord_2648860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648860).length < 2 ^ (prefixWord ++ tailWord_2648860).sum := by decide
  have hdescent : baseEnd_2648860 < baseStart_2648860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648888 : List Nat := [2, 1, 2, 1, 3, 2, 1, 3, 7]
def baseStart_2648888 : Nat := 118140960795 + 2648888 * 2 ^ 59
def prefixEnd_2648888 : Nat := 4983230072969 + 3 ^ 40 * 2648888 * 2
def baseEnd_2648888 : Nat := 302256165317097210492887

theorem tailTrace_2648888 : CollatzResearch.WordTrace tailWord_2648888 prefixEnd_2648888 302256165317097210492887 := by
  unfold tailWord_2648888
  simp only [CollatzResearch.WordTrace]
  refine ⟨48306441213769322449289659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64408588285025763265719545 48306441213769322449289659)
  ·
    refine ⟨72459661820653983673934489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48306441213769322449289659 72459661820653983673934489)
    ·
      refine ⟨54344746365490487755450867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72459661820653983673934489 54344746365490487755450867)
      ·
        refine ⟨81517119548235731633176301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54344746365490487755450867 81517119548235731633176301)
        ·
          refine ⟨30568919830588399362441113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81517119548235731633176301 30568919830588399362441113)
          ·
            refine ⟨22926689872941299521830835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30568919830588399362441113 22926689872941299521830835)
            ·
              refine ⟨34390034809411949282746253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22926689872941299521830835 34390034809411949282746253)
              ·
                refine ⟨12896263053529480981029845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34390034809411949282746253 12896263053529480981029845)
                ·
                  refine ⟨302256165317097210492887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12896263053529480981029845 302256165317097210492887)
                  ·
                    rfl

theorem cell22_2648888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 7].length) (baseStart_2648888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648888 prefixEnd_2648888 := by exact prefixLift 2648888
  have htrace : WordTrace (prefixWord ++ tailWord_2648888) baseStart_2648888 baseEnd_2648888 := by
    simpa [prefixWord, tailWord_2648888, baseEnd_2648888] using wordTrace_append hprefix tailTrace_2648888
  have hstable : (prefixWord ++ tailWord_2648888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648888).length < 2 ^ (prefixWord ++ tailWord_2648888).sum := by decide
  have hdescent : baseEnd_2648888 < baseStart_2648888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648903 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 1, 7]
def baseStart_2648903 : Nat := 118140960795 + 2648903 * 2 ^ 59
def prefixEnd_2648903 : Nat := 4983230072969 + 3 ^ 40 * 2648903 * 2
def baseEnd_2648903 : Nat := 906773630757836592353615

theorem tailTrace_2648903 : CollatzResearch.WordTrace tailWord_2648903 prefixEnd_2648903 906773630757836592353615 := by
  unfold tailWord_2648903
  simp only [CollatzResearch.WordTrace]
  refine ⟨96613429522484302460375363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64408953014989534973583575 96613429522484302460375363)
  ·
    refine ⟨144920144283726453690563045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96613429522484302460375363 144920144283726453690563045)
    ·
      refine ⟨27172527053198710066980571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144920144283726453690563045 27172527053198710066980571)
      ·
        refine ⟨40758790579798065100470857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27172527053198710066980571 40758790579798065100470857)
        ·
          refine ⟨30569092934848548825353143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40758790579798065100470857 30569092934848548825353143)
          ·
            refine ⟨45853639402272823238029715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30569092934848548825353143 45853639402272823238029715)
            ·
              refine ⟨68780459103409234857044573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45853639402272823238029715 68780459103409234857044573)
              ·
                refine ⟨25792672163778463071391715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68780459103409234857044573 25792672163778463071391715)
                ·
                  refine ⟨38689008245667694607087573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25792672163778463071391715 38689008245667694607087573)
                  ·
                    refine ⟨906773630757836592353615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38689008245667694607087573 906773630757836592353615)
                    ·
                      rfl

theorem cell22_2648903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_2648903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648903 prefixEnd_2648903 := by exact prefixLift 2648903
  have htrace : WordTrace (prefixWord ++ tailWord_2648903) baseStart_2648903 baseEnd_2648903 := by
    simpa [prefixWord, tailWord_2648903, baseEnd_2648903] using wordTrace_append hprefix tailTrace_2648903
  have hstable : (prefixWord ++ tailWord_2648903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648903).length < 2 ^ (prefixWord ++ tailWord_2648903).sum := by decide
  have hdescent : baseEnd_2648903 < baseStart_2648903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648905 : List Nat := [1, 2, 1, 1, 2, 6, 1, 3, 5]
def baseStart_2648905 : Nat := 118140960795 + 2648905 * 2 ^ 59
def prefixEnd_2648905 : Nat := 4983230072969 + 3 ^ 40 * 2648905 * 2
def baseEnd_2648905 : Nat := 302258105132903084601203

theorem tailTrace_2648905 : CollatzResearch.WordTrace tailWord_2648905 prefixEnd_2648905 302258105132903084601203 := by
  unfold tailWord_2648905
  simp only [CollatzResearch.WordTrace]
  refine ⟨96613502468477056801948169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64409001645651371201298779 96613502468477056801948169)
  ·
    refine ⟨72460126851357792601461127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96613502468477056801948169 72460126851357792601461127)
    ·
      refine ⟨108690190277036688902191691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72460126851357792601461127 108690190277036688902191691)
      ·
        refine ⟨163035285415555033353287537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108690190277036688902191691 163035285415555033353287537)
        ·
          refine ⟨122276464061666275014965653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163035285415555033353287537 122276464061666275014965653)
          ·
            refine ⟨5731709252890606641326515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 122276464061666275014965653 5731709252890606641326515)
            ·
              refine ⟨8597563879335909961989773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5731709252890606641326515 8597563879335909961989773)
              ·
                refine ⟨3224086454750966235746165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8597563879335909961989773 3224086454750966235746165)
                ·
                  refine ⟨302258105132903084601203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3224086454750966235746165 302258105132903084601203)
                  ·
                    rfl

theorem cell22_2648905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 5].length) (baseStart_2648905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648905 prefixEnd_2648905 := by exact prefixLift 2648905
  have htrace : WordTrace (prefixWord ++ tailWord_2648905) baseStart_2648905 baseEnd_2648905 := by
    simpa [prefixWord, tailWord_2648905, baseEnd_2648905] using wordTrace_append hprefix tailTrace_2648905
  have hstable : (prefixWord ++ tailWord_2648905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648905).length < 2 ^ (prefixWord ++ tailWord_2648905).sum := by decide
  have hdescent : baseEnd_2648905 < baseStart_2648905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648965 : List Nat := [1, 3, 1, 1, 3, 3, 1, 3, 1, 5]
def baseStart_2648965 : Nat := 118140960795 + 2648965 * 2 ^ 59
def prefixEnd_2648965 : Nat := 4983230072969 + 3 ^ 40 * 2648965 * 2
def baseEnd_2648965 : Nat := 906794854624889097303425

theorem tailTrace_2648965 : CollatzResearch.WordTrace tailWord_2648965 prefixEnd_2648965 906794854624889097303425 := by
  unfold tailWord_2648965
  simp only [CollatzResearch.WordTrace]
  refine ⟨96615690848259687049132349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64410460565506458032754899 96615690848259687049132349)
  ·
    refine ⟨36230884068097382643424631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96615690848259687049132349 36230884068097382643424631)
    ·
      refine ⟨54346326102146073965136947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36230884068097382643424631 54346326102146073965136947)
      ·
        refine ⟨81519489153219110947705421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54346326102146073965136947 81519489153219110947705421)
        ·
          refine ⟨30569808432457166605389533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81519489153219110947705421 30569808432457166605389533)
          ·
            refine ⟨11463678162171437477021075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30569808432457166605389533 11463678162171437477021075)
            ·
              refine ⟨17195517243257156215531613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11463678162171437477021075 17195517243257156215531613)
              ·
                refine ⟨6448318966221433580824355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17195517243257156215531613 6448318966221433580824355)
                ·
                  refine ⟨9672478449332150371236533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6448318966221433580824355 9672478449332150371236533)
                  ·
                    refine ⟨906794854624889097303425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9672478449332150371236533 906794854624889097303425)
                    ·
                      rfl

theorem cell22_2648965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_2648965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648965 prefixEnd_2648965 := by exact prefixLift 2648965
  have htrace : WordTrace (prefixWord ++ tailWord_2648965) baseStart_2648965 baseEnd_2648965 := by
    simpa [prefixWord, tailWord_2648965, baseEnd_2648965] using wordTrace_append hprefix tailTrace_2648965
  have hstable : (prefixWord ++ tailWord_2648965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648965).length < 2 ^ (prefixWord ++ tailWord_2648965).sum := by decide
  have hdescent : baseEnd_2648965 < baseStart_2648965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648986 : List Nat := [3, 1, 1, 4, 3, 2, 2, 1, 1, 4]
def baseStart_2648986 : Nat := 118140960795 + 2648986 * 2 ^ 59
def prefixEnd_2648986 : Nat := 4983230072969 + 3 ^ 40 * 2648986 * 2
def baseEnd_2648986 : Nat := 906802043354052042528361

theorem tailTrace_2648986 : CollatzResearch.WordTrace tailWord_2648986 prefixEnd_2648986 906802043354052042528361 := by
  unfold tailWord_2648986
  simp only [CollatzResearch.WordTrace]
  refine ⟨24154114195295901908911703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64410971187455738423764541 24154114195295901908911703)
  ·
    refine ⟨36231171292943852863367555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24154114195295901908911703 36231171292943852863367555)
    ·
      refine ⟨54346756939415779295051333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36231171292943852863367555 54346756939415779295051333)
      ·
        refine ⟨10190016926140458617822125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54346756939415779295051333 10190016926140458617822125)
        ·
          refine ⟨3821256347302671981683297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10190016926140458617822125 3821256347302671981683297)
          ·
            refine ⟨2865942260477003986262473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3821256347302671981683297 2865942260477003986262473)
            ·
              refine ⟨2149456695357752989696855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2865942260477003986262473 2149456695357752989696855)
              ·
                refine ⟨3224185043036629484545283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2149456695357752989696855 3224185043036629484545283)
                ·
                  refine ⟨4836277564554944226817925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3224185043036629484545283 4836277564554944226817925)
                  ·
                    refine ⟨906802043354052042528361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4836277564554944226817925 906802043354052042528361)
                    ·
                      rfl

theorem cell22_2648986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 1, 4].length) (baseStart_2648986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648986 prefixEnd_2648986 := by exact prefixLift 2648986
  have htrace : WordTrace (prefixWord ++ tailWord_2648986) baseStart_2648986 baseEnd_2648986 := by
    simpa [prefixWord, tailWord_2648986, baseEnd_2648986] using wordTrace_append hprefix tailTrace_2648986
  have hstable : (prefixWord ++ tailWord_2648986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648986).length < 2 ^ (prefixWord ++ tailWord_2648986).sum := by decide
  have hdescent : baseEnd_2648986 < baseStart_2648986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648999 : List Nat := [1, 1, 6, 1, 3, 1, 1, 1, 4, 3]
def baseStart_2648999 : Nat := 118140960795 + 2648999 * 2 ^ 59
def prefixEnd_2648999 : Nat := 4983230072969 + 3 ^ 40 * 2648999 * 2
def baseEnd_2648999 : Nat := 906806493519724341953321

theorem tailTrace_2648999 : CollatzResearch.WordTrace tailWord_2648999 prefixEnd_2648999 906806493519724341953321 := by
  unfold tailWord_2648999
  simp only [CollatzResearch.WordTrace]
  refine ⟨96616930930136510855870051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64411287286757673903913367 96616930930136510855870051)
  ·
    refine ⟨144925396395204766283805077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96616930930136510855870051 144925396395204766283805077)
    ·
      refine ⟨6793377956025223419553363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 144925396395204766283805077 6793377956025223419553363)
      ·
        refine ⟨10190066934037835129330045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6793377956025223419553363 10190066934037835129330045)
        ·
          refine ⟨3821275100264188173498767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10190066934037835129330045 3821275100264188173498767)
          ·
            refine ⟨5731912650396282260248151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3821275100264188173498767 5731912650396282260248151)
            ·
              refine ⟨8597868975594423390372227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5731912650396282260248151 8597868975594423390372227)
              ·
                refine ⟨12896803463391635085558341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8597868975594423390372227 12896803463391635085558341)
                ·
                  refine ⟨2418150649385931578542189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12896803463391635085558341 2418150649385931578542189)
                  ·
                    refine ⟨906806493519724341953321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2418150649385931578542189 906806493519724341953321)
                    ·
                      rfl

theorem cell22_2648999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_2648999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2648999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2648999 prefixEnd_2648999 := by exact prefixLift 2648999
  have htrace : WordTrace (prefixWord ++ tailWord_2648999) baseStart_2648999 baseEnd_2648999 := by
    simpa [prefixWord, tailWord_2648999, baseEnd_2648999] using wordTrace_append hprefix tailTrace_2648999
  have hstable : (prefixWord ++ tailWord_2648999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648999).length < 2 ^ (prefixWord ++ tailWord_2648999).sum := by decide
  have hdescent : baseEnd_2648999 < baseStart_2648999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649085 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 8]
def baseStart_2649085 : Nat := 118140960795 + 2649085 * 2 ^ 59
def prefixEnd_2649085 : Nat := 4983230072969 + 3 ^ 40 * 2649085 * 2
def baseEnd_2649085 : Nat := 302278644359082928101019

theorem tailTrace_2649085 : CollatzResearch.WordTrace tailWord_2649085 prefixEnd_2649085 302278644359082928101019 := by
  unfold tailWord_2649085
  simp only [CollatzResearch.WordTrace]
  refine ⟨96620067607824947543500709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64413378405216631695667139 96620067607824947543500709)
  ·
    refine ⟨18116262676467177664406383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96620067607824947543500709 18116262676467177664406383)
    ·
      refine ⟨27174394014700766496609575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18116262676467177664406383 27174394014700766496609575)
      ·
        refine ⟨40761591022051149744914363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27174394014700766496609575 40761591022051149744914363)
        ·
          refine ⟨61142386533076724617371545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40761591022051149744914363 61142386533076724617371545)
          ·
            refine ⟨45856789899807543463028659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61142386533076724617371545 45856789899807543463028659)
            ·
              refine ⟨68785184849711315194542989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45856789899807543463028659 68785184849711315194542989)
              ·
                refine ⟨25794444318641743197953621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68785184849711315194542989 25794444318641743197953621)
                ·
                  refine ⟨302278644359082928101019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25794444318641743197953621 302278644359082928101019)
                  ·
                    rfl

theorem cell22_2649085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_2649085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2649085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2649085 prefixEnd_2649085 := by exact prefixLift 2649085
  have htrace : WordTrace (prefixWord ++ tailWord_2649085) baseStart_2649085 baseEnd_2649085 := by
    simpa [prefixWord, tailWord_2649085, baseEnd_2649085] using wordTrace_append hprefix tailTrace_2649085
  have hstable : (prefixWord ++ tailWord_2649085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649085).length < 2 ^ (prefixWord ++ tailWord_2649085).sum := by decide
  have hdescent : baseEnd_2649085 < baseStart_2649085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649119 : List Nat := [1, 1, 2, 4, 1, 4, 1, 4, 4]
def baseStart_2649119 : Nat := 118140960795 + 2649119 * 2 ^ 59
def prefixEnd_2649119 : Nat := 4983230072969 + 3 ^ 40 * 2649119 * 2
def baseEnd_2649119 : Nat := 302282523990694676317651

theorem tailTrace_2649119 : CollatzResearch.WordTrace tailWord_2649119 prefixEnd_2649119 302282523990694676317651 := by
  unfold tailWord_2649119
  simp only [CollatzResearch.WordTrace]
  refine ⟨96621307689701771350238411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64414205126467847566825607 96621307689701771350238411)
  ·
    refine ⟨144931961534552657025357617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96621307689701771350238411 144931961534552657025357617)
    ·
      refine ⟨108698971150914492769018213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144931961534552657025357617 108698971150914492769018213)
      ·
        refine ⟨20381057090796467394190915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108698971150914492769018213 20381057090796467394190915)
        ·
          refine ⟨30571585636194701091286373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20381057090796467394190915 30571585636194701091286373)
          ·
            refine ⟨5732172306786506454616195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30571585636194701091286373 5732172306786506454616195)
            ·
              refine ⟨8598258460179759681924293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5732172306786506454616195 8598258460179759681924293)
              ·
                refine ⟨1612173461283704940360805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8598258460179759681924293 1612173461283704940360805)
                ·
                  refine ⟨302282523990694676317651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1612173461283704940360805 302282523990694676317651)
                  ·
                    rfl

theorem cell22_2649119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4, 4].length) (baseStart_2649119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2649119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2649119 prefixEnd_2649119 := by exact prefixLift 2649119
  have htrace : WordTrace (prefixWord ++ tailWord_2649119) baseStart_2649119 baseEnd_2649119 := by
    simpa [prefixWord, tailWord_2649119, baseEnd_2649119] using wordTrace_append hprefix tailTrace_2649119
  have hstable : (prefixWord ++ tailWord_2649119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649119).length < 2 ^ (prefixWord ++ tailWord_2649119).sum := by decide
  have hdescent : baseEnd_2649119 < baseStart_2649119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649134 : List Nat := [4, 1, 3, 1, 1, 1, 4, 1, 1, 5]
def baseStart_2649134 : Nat := 118140960795 + 2649134 * 2 ^ 59
def prefixEnd_2649134 : Nat := 4983230072969 + 3 ^ 40 * 2649134 * 2
def baseEnd_2649134 : Nat := 906852706778628989827907

theorem tailTrace_2649134 : CollatzResearch.WordTrace tailWord_2649134 prefixEnd_2649134 906852706778628989827907 := by
  unfold tailWord_2649134
  simp only [CollatzResearch.WordTrace]
  refine ⟨12077731848080928614004307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64414569856431619274689637 12077731848080928614004307)
  ·
    refine ⟨18116597772121392921006461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12077731848080928614004307 18116597772121392921006461)
    ·
      refine ⟨6793724164545522345377423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18116597772121392921006461 6793724164545522345377423)
      ·
        refine ⟨10190586246818283518066135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6793724164545522345377423 10190586246818283518066135)
        ·
          refine ⟨15285879370227425277099203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10190586246818283518066135 15285879370227425277099203)
          ·
            refine ⟨22928819055341137915648805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15285879370227425277099203 22928819055341137915648805)
            ·
              refine ⟨4299153572876463359184151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22928819055341137915648805 4299153572876463359184151)
              ·
                refine ⟨6448730359314695038776227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4299153572876463359184151 6448730359314695038776227)
                ·
                  refine ⟨9673095538972042558164341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6448730359314695038776227 9673095538972042558164341)
                  ·
                    refine ⟨906852706778628989827907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9673095538972042558164341 906852706778628989827907)
                    ·
                      rfl

theorem cell22_2649134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_2649134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2649134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2649134 prefixEnd_2649134 := by exact prefixLift 2649134
  have htrace : WordTrace (prefixWord ++ tailWord_2649134) baseStart_2649134 baseEnd_2649134 := by
    simpa [prefixWord, tailWord_2649134, baseEnd_2649134] using wordTrace_append hprefix tailTrace_2649134
  have hstable : (prefixWord ++ tailWord_2649134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649134).length < 2 ^ (prefixWord ++ tailWord_2649134).sum := by decide
  have hdescent : baseEnd_2649134 < baseStart_2649134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649149 : List Nat := [1, 4, 1, 3, 1, 2, 3, 1, 2, 4]
def baseStart_2649149 : Nat := 118140960795 + 2649149 * 2 ^ 59
def prefixEnd_2649149 : Nat := 4983230072969 + 3 ^ 40 * 2649149 * 2
def baseEnd_2649149 : Nat := 906857841585173950702861

theorem tailTrace_2649149 : CollatzResearch.WordTrace tailWord_2649149 prefixEnd_2649149 906857841585173950702861 := by
  unfold tailWord_2649149
  simp only [CollatzResearch.WordTrace]
  refine ⟨96622401879593086473830501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64414934586395390982553667 96622401879593086473830501)
  ·
    refine ⟨18116700352423703713843219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96622401879593086473830501 18116700352423703713843219)
    ·
      refine ⟨27175050528635555570764829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18116700352423703713843219 27175050528635555570764829)
      ·
        refine ⟨10190643948238333339036811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27175050528635555570764829 10190643948238333339036811)
        ·
          refine ⟨15285965922357500008555217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10190643948238333339036811 15285965922357500008555217)
          ·
            refine ⟨11464474441768125006416413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15285965922357500008555217 11464474441768125006416413)
            ·
              refine ⟨4299177915663046877406155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11464474441768125006416413 4299177915663046877406155)
              ·
                refine ⟨6448766873494570316109233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4299177915663046877406155 6448766873494570316109233)
                ·
                  refine ⟨4836575155120927737081925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6448766873494570316109233 4836575155120927737081925)
                  ·
                    refine ⟨906857841585173950702861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4836575155120927737081925 906857841585173950702861)
                    ·
                      rfl

theorem cell22_2649149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_2649149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2649149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2649149 prefixEnd_2649149 := by exact prefixLift 2649149
  have htrace : WordTrace (prefixWord ++ tailWord_2649149) baseStart_2649149 baseEnd_2649149 := by
    simpa [prefixWord, tailWord_2649149, baseEnd_2649149] using wordTrace_append hprefix tailTrace_2649149
  have hstable : (prefixWord ++ tailWord_2649149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649149).length < 2 ^ (prefixWord ++ tailWord_2649149).sum := by decide
  have hdescent : baseEnd_2649149 < baseStart_2649149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649230 : List Nat := [4, 1, 1, 3, 2, 2, 3, 2, 1, 3]
def baseStart_2649230 : Nat := 118140960795 + 2649230 * 2 ^ 59
def prefixEnd_2649230 : Nat := 4983230072969 + 3 ^ 40 * 2649230 * 2
def baseEnd_2649230 : Nat := 906885569540516739427613

theorem tailTrace_2649230 : CollatzResearch.WordTrace tailWord_2649230 prefixEnd_2649230 906885569540516739427613 := by
  unfold tailWord_2649230
  simp only [CollatzResearch.WordTrace]
  refine ⟨12078169524037454663441143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64416904128199758205019429 12078169524037454663441143)
  ·
    refine ⟨18117254286056181995161715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12078169524037454663441143 18117254286056181995161715)
    ·
      refine ⟨27175881429084272992742573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18117254286056181995161715 27175881429084272992742573)
      ·
        refine ⟨10190955535906602372278465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27175881429084272992742573 10190955535906602372278465)
        ·
          refine ⟨7643216651929951779208849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10190955535906602372278465 7643216651929951779208849)
          ·
            refine ⟨5732412488947463834406637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7643216651929951779208849 5732412488947463834406637)
            ·
              refine ⟨2149654683355298937902489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5732412488947463834406637 2149654683355298937902489)
              ·
                refine ⟨1612241012516474203426867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2149654683355298937902489 1612241012516474203426867)
                ·
                  refine ⟨2418361518774711305140301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1612241012516474203426867 2418361518774711305140301)
                  ·
                    refine ⟨906885569540516739427613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2418361518774711305140301 906885569540516739427613)
                    ·
                      rfl

theorem cell22_2649230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_2649230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2649230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2649230 prefixEnd_2649230 := by exact prefixLift 2649230
  have htrace : WordTrace (prefixWord ++ tailWord_2649230) baseStart_2649230 baseEnd_2649230 := by
    simpa [prefixWord, tailWord_2649230, baseEnd_2649230] using wordTrace_append hprefix tailTrace_2649230
  have hstable : (prefixWord ++ tailWord_2649230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649230).length < 2 ^ (prefixWord ++ tailWord_2649230).sum := by decide
  have hdescent : baseEnd_2649230 < baseStart_2649230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649237 : List Nat := [1, 3, 2, 1, 1, 1, 2, 5, 6]
def baseStart_2649237 : Nat := 118140960795 + 2649237 * 2 ^ 59
def prefixEnd_2649237 : Nat := 4983230072969 + 3 ^ 40 * 2649237 * 2
def baseEnd_2649237 : Nat := 302295988594523684834197

theorem tailTrace_2649237 : CollatzResearch.WordTrace tailWord_2649237 prefixEnd_2649237 302295988594523684834197 := by
  unfold tailWord_2649237
  simp only [CollatzResearch.WordTrace]
  refine ⟨96625611503274277503033965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64417074335516185002022643 96625611503274277503033965)
  ·
    refine ⟨36234604313727854063637737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96625611503274277503033965 36234604313727854063637737)
    ·
      refine ⟨27175953235295890547728303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36234604313727854063637737 27175953235295890547728303)
      ·
        refine ⟨40763929852943835821592455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27175953235295890547728303 40763929852943835821592455)
        ·
          refine ⟨61145894779415753732388683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40763929852943835821592455 61145894779415753732388683)
          ·
            refine ⟨91718842169123630598583025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61145894779415753732388683 91718842169123630598583025)
            ·
              refine ⟨68789131626842722948937269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91718842169123630598583025 68789131626842722948937269)
              ·
                refine ⟨6448981090016505276462869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68789131626842722948937269 6448981090016505276462869)
                ·
                  refine ⟨302295988594523684834197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6448981090016505276462869 302295988594523684834197)
                  ·
                    rfl

theorem cell22_2649237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 6].length) (baseStart_2649237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2649237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2649237 prefixEnd_2649237 := by exact prefixLift 2649237
  have htrace : WordTrace (prefixWord ++ tailWord_2649237) baseStart_2649237 baseEnd_2649237 := by
    simpa [prefixWord, tailWord_2649237, baseEnd_2649237] using wordTrace_append hprefix tailTrace_2649237
  have hstable : (prefixWord ++ tailWord_2649237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649237).length < 2 ^ (prefixWord ++ tailWord_2649237).sum := by decide
  have hdescent : baseEnd_2649237 < baseStart_2649237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649267 : List Nat := [1, 1, 1, 2, 3, 2, 2, 3, 1, 6]
def baseStart_2649267 : Nat := 118140960795 + 2649267 * 2 ^ 59
def prefixEnd_2649267 : Nat := 4983230072969 + 3 ^ 40 * 2649267 * 2
def baseEnd_2649267 : Nat := 906898235396660976252499

theorem tailTrace_2649267 : CollatzResearch.WordTrace tailWord_2649267 prefixEnd_2649267 906898235396660976252499 := by
  unfold tailWord_2649267
  simp only [CollatzResearch.WordTrace]
  refine ⟨96626705693165592626626055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64417803795443728417750703 96626705693165592626626055)
  ·
    refine ⟨144940058539748388939939083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96626705693165592626626055 144940058539748388939939083)
    ·
      refine ⟨217410087809622583409908625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144940058539748388939939083 217410087809622583409908625)
      ·
        refine ⟨163057565857216937557431469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217410087809622583409908625 163057565857216937557431469)
        ·
          refine ⟨61146587196456351584036801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163057565857216937557431469 61146587196456351584036801)
          ·
            refine ⟨45859940397342263688027601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61146587196456351584036801 45859940397342263688027601)
            ·
              refine ⟨34394955298006697766020701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45859940397342263688027601 34394955298006697766020701)
              ·
                refine ⟨12898108236752511662257763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34394955298006697766020701 12898108236752511662257763)
                ·
                  refine ⟨19347162355128767493386645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12898108236752511662257763 19347162355128767493386645)
                  ·
                    refine ⟨906898235396660976252499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19347162355128767493386645 906898235396660976252499)
                    ·
                      rfl

theorem cell22_2649267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 6].length) (baseStart_2649267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2649267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2649267 prefixEnd_2649267 := by exact prefixLift 2649267
  have htrace : WordTrace (prefixWord ++ tailWord_2649267) baseStart_2649267 baseEnd_2649267 := by
    simpa [prefixWord, tailWord_2649267, baseEnd_2649267] using wordTrace_append hprefix tailTrace_2649267
  have hstable : (prefixWord ++ tailWord_2649267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649267).length < 2 ^ (prefixWord ++ tailWord_2649267).sum := by decide
  have hdescent : baseEnd_2649267 < baseStart_2649267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649297 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 2, 7]
def baseStart_2649297 : Nat := 118140960795 + 2649297 * 2 ^ 59
def prefixEnd_2649297 : Nat := 4983230072969 + 3 ^ 40 * 2649297 * 2
def baseEnd_2649297 : Nat := 906908505009750898002407

theorem tailTrace_2649297 : CollatzResearch.WordTrace tailWord_2649297 prefixEnd_2649297 906908505009750898002407 := by
  unfold tailWord_2649297
  simp only [CollatzResearch.WordTrace]
  refine ⟨96627799883056907750218145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64418533255371271833478763 96627799883056907750218145)
  ·
    refine ⟨72470849912292680812663609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96627799883056907750218145 72470849912292680812663609)
    ·
      refine ⟨54353137434219510609497707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72470849912292680812663609 54353137434219510609497707)
      ·
        refine ⟨81529706151329265914246561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54353137434219510609497707 81529706151329265914246561)
        ·
          refine ⟨61147279613496949435684921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81529706151329265914246561 61147279613496949435684921)
          ·
            refine ⟨45860459710122712076763691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61147279613496949435684921 45860459710122712076763691)
            ·
              refine ⟨68790689565184068115145537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45860459710122712076763691 68790689565184068115145537)
              ·
                refine ⟨51593017173888051086359153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68790689565184068115145537 51593017173888051086359153)
                ·
                  refine ⟨38694762880416038314769365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51593017173888051086359153 38694762880416038314769365)
                  ·
                    refine ⟨906908505009750898002407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38694762880416038314769365 906908505009750898002407)
                    ·
                      rfl

theorem cell22_2649297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_2649297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2649297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2649297 prefixEnd_2649297 := by exact prefixLift 2649297
  have htrace : WordTrace (prefixWord ++ tailWord_2649297) baseStart_2649297 baseEnd_2649297 := by
    simpa [prefixWord, tailWord_2649297, baseEnd_2649297] using wordTrace_append hprefix tailTrace_2649297
  have hstable : (prefixWord ++ tailWord_2649297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649297).length < 2 ^ (prefixWord ++ tailWord_2649297).sum := by decide
  have hdescent : baseEnd_2649297 < baseStart_2649297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649348 : List Nat := [2, 3, 2, 2, 2, 2, 2, 1, 3, 3]
def baseStart_2649348 : Nat := 118140960795 + 2649348 * 2 ^ 59
def prefixEnd_2649348 : Nat := 4983230072969 + 3 ^ 40 * 2649348 * 2
def baseEnd_2649348 : Nat := 906925963352003764977251

theorem tailTrace_2649348 : CollatzResearch.WordTrace tailWord_2649348 prefixEnd_2649348 906925963352003764977251 := by
  unfold tailWord_2649348
  simp only [CollatzResearch.WordTrace]
  refine ⟨48314830002936071730162349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64419773337248095640216465 48314830002936071730162349)
  ·
    refine ⟨18118061251101026898810881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48314830002936071730162349 18118061251101026898810881)
    ·
      refine ⟨13588545938325770174108161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18118061251101026898810881 13588545938325770174108161)
      ·
        refine ⟨10191409453744327630581121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13588545938325770174108161 10191409453744327630581121)
        ·
          refine ⟨7643557090308245722935841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10191409453744327630581121 7643557090308245722935841)
          ·
            refine ⟨5732667817731184292201881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7643557090308245722935841 5732667817731184292201881)
            ·
              refine ⟨4299500863298388219151411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5732667817731184292201881 4299500863298388219151411)
              ·
                refine ⟨6449251294947582328727117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4299500863298388219151411 6449251294947582328727117)
                ·
                  refine ⟨2418469235605343373272669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6449251294947582328727117 2418469235605343373272669)
                  ·
                    refine ⟨906925963352003764977251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2418469235605343373272669 906925963352003764977251)
                    ·
                      rfl

theorem cell22_2649348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_2649348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2649348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2649348 prefixEnd_2649348 := by exact prefixLift 2649348
  have htrace : WordTrace (prefixWord ++ tailWord_2649348) baseStart_2649348 baseEnd_2649348 := by
    simpa [prefixWord, tailWord_2649348, baseEnd_2649348] using wordTrace_append hprefix tailTrace_2649348
  have hstable : (prefixWord ++ tailWord_2649348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649348).length < 2 ^ (prefixWord ++ tailWord_2649348).sum := by decide
  have hdescent : baseEnd_2649348 < baseStart_2649348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649361 : List Nat := [1, 2, 2, 1, 1, 4, 5, 1, 5]
def baseStart_2649361 : Nat := 118140960795 + 2649361 * 2 ^ 59
def prefixEnd_2649361 : Nat := 4983230072969 + 3 ^ 40 * 2649361 * 2
def baseEnd_2649361 : Nat := 302310137839225354800737

theorem tailTrace_2649361 : CollatzResearch.WordTrace tailWord_2649361 prefixEnd_2649361 302310137839225354800737 := by
  unfold tailWord_2649361
  simp only [CollatzResearch.WordTrace]
  refine ⟨96630134154825046680547937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64420089436550031120365291 96630134154825046680547937)
  ·
    refine ⟨72472600616118785010410953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96630134154825046680547937 72472600616118785010410953)
    ·
      refine ⟨54354450462089088757808215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72472600616118785010410953 54354450462089088757808215)
      ·
        refine ⟨81531675693133633136712323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54354450462089088757808215 81531675693133633136712323)
        ·
          refine ⟨122297513539700449705068485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81531675693133633136712323 122297513539700449705068485)
          ·
            refine ⟨22930783788693834319700341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122297513539700449705068485 22930783788693834319700341)
            ·
              refine ⟨2149760980190046967471907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22930783788693834319700341 2149760980190046967471907)
              ·
                refine ⟨3224641470285070451207861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2149760980190046967471907 3224641470285070451207861)
                ·
                  refine ⟨302310137839225354800737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3224641470285070451207861 302310137839225354800737)
                  ·
                    rfl

theorem cell22_2649361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 5].length) (baseStart_2649361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2649361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2649361 prefixEnd_2649361 := by exact prefixLift 2649361
  have htrace : WordTrace (prefixWord ++ tailWord_2649361) baseStart_2649361 baseEnd_2649361 := by
    simpa [prefixWord, tailWord_2649361, baseEnd_2649361] using wordTrace_append hprefix tailTrace_2649361
  have hstable : (prefixWord ++ tailWord_2649361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649361).length < 2 ^ (prefixWord ++ tailWord_2649361).sum := by decide
  have hdescent : baseEnd_2649361 < baseStart_2649361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649434 : List Nat := [3, 1, 1, 2, 1, 2, 4, 8]
def baseStart_2649434 : Nat := 118140960795 + 2649434 * 2 ^ 59
def prefixEnd_2649434 : Nat := 4983230072969 + 3 ^ 40 * 2649434 * 2
def baseEnd_2649434 : Nat := 100772822545503134147443

theorem tailTrace_2649434 : CollatzResearch.WordTrace tailWord_2649434 prefixEnd_2649434 100772822545503134147443 := by
  unfold tailWord_2649434
  simp only [CollatzResearch.WordTrace]
  refine ⟨24158199170890145036988839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64421864455707053431970237 24158199170890145036988839)
  ·
    refine ⟨36237298756335217555483259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24158199170890145036988839 36237298756335217555483259)
    ·
      refine ⟨54355948134502826333224889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36237298756335217555483259 54355948134502826333224889)
      ·
        refine ⟨40766961100877119749918667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54355948134502826333224889 40766961100877119749918667)
        ·
          refine ⟨61150441651315679624878001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40766961100877119749918667 61150441651315679624878001)
          ·
            refine ⟨45862831238486759718658501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61150441651315679624878001 45862831238486759718658501)
            ·
              refine ⟨8599280857216267447248469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45862831238486759718658501 8599280857216267447248469)
              ·
                refine ⟨100772822545503134147443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8599280857216267447248469 100772822545503134147443)
                ·
                  rfl

theorem cell22_2649434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 8].length) (baseStart_2649434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2649434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2649434 prefixEnd_2649434 := by exact prefixLift 2649434
  have htrace : WordTrace (prefixWord ++ tailWord_2649434) baseStart_2649434 baseEnd_2649434 := by
    simpa [prefixWord, tailWord_2649434, baseEnd_2649434] using wordTrace_append hprefix tailTrace_2649434
  have hstable : (prefixWord ++ tailWord_2649434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649434).length < 2 ^ (prefixWord ++ tailWord_2649434).sum := by decide
  have hdescent : baseEnd_2649434 < baseStart_2649434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649511 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 4, 5]
def baseStart_2649511 : Nat := 118140960795 + 2649511 * 2 ^ 59
def prefixEnd_2649511 : Nat := 4983230072969 + 3 ^ 40 * 2649511 * 2
def baseEnd_2649511 : Nat := 906981761583125673151751

theorem tailTrace_2649511 : CollatzResearch.WordTrace tailWord_2649511 prefixEnd_2649511 906981761583125673151751 := by
  unfold tailWord_2649511
  simp only [CollatzResearch.WordTrace]
  refine ⟨96635605104281622298508387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64423736736187748199005591 96635605104281622298508387)
  ·
    refine ⟨144953407656422433447762581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96635605104281622298508387 144953407656422433447762581)
    ·
      refine ⟨6794690983894801567863871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 144953407656422433447762581 6794690983894801567863871)
      ·
        refine ⟨10192036475842202351795807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6794690983894801567863871 10192036475842202351795807)
        ·
          refine ⟨15288054713763303527693711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10192036475842202351795807 15288054713763303527693711)
          ·
            refine ⟨22932082070644955291540567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15288054713763303527693711 22932082070644955291540567)
            ·
              refine ⟨34398123105967432937310851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22932082070644955291540567 34398123105967432937310851)
              ·
                refine ⟨51597184658951149405966277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34398123105967432937310851 51597184658951149405966277)
                ·
                  refine ⟨9674472123553340513618677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51597184658951149405966277 9674472123553340513618677)
                  ·
                    refine ⟨906981761583125673151751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9674472123553340513618677 906981761583125673151751)
                    ·
                      rfl

theorem cell22_2649511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_2649511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2649511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2649511 prefixEnd_2649511 := by exact prefixLift 2649511
  have htrace : WordTrace (prefixWord ++ tailWord_2649511) baseStart_2649511 baseEnd_2649511 := by
    simpa [prefixWord, tailWord_2649511, baseEnd_2649511] using wordTrace_append hprefix tailTrace_2649511
  have hstable : (prefixWord ++ tailWord_2649511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649511).length < 2 ^ (prefixWord ++ tailWord_2649511).sum := by decide
  have hdescent : baseEnd_2649511 < baseStart_2649511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649517 : List Nat := [1, 5, 2, 2, 1, 1, 2, 4, 1, 3]
def baseStart_2649517 : Nat := 118140960795 + 2649517 * 2 ^ 59
def prefixEnd_2649517 : Nat := 4983230072969 + 3 ^ 40 * 2649517 * 2
def baseEnd_2649517 : Nat := 906983815505743657501733

theorem tailTrace_2649517 : CollatzResearch.WordTrace tailWord_2649517 prefixEnd_2649517 906983815505743657501733 := by
  unfold tailWord_2649517
  simp only [CollatzResearch.WordTrace]
  refine ⟨96635823942259885323226805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64423882628173256882151203 96635823942259885323226805)
  ·
    refine ⟨9059608494586864249052513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96635823942259885323226805 9059608494586864249052513)
    ·
      refine ⟨6794706370940148186789385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9059608494586864249052513 6794706370940148186789385)
      ·
        refine ⟨5096029778205111140092039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6794706370940148186789385 5096029778205111140092039)
        ·
          refine ⟨7644044667307666710138059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5096029778205111140092039 7644044667307666710138059)
          ·
            refine ⟨11466067000961500065207089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7644044667307666710138059 11466067000961500065207089)
            ·
              refine ⟨8599550250721125048905317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11466067000961500065207089 8599550250721125048905317)
              ·
                refine ⟨1612415672010210946669747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8599550250721125048905317 1612415672010210946669747)
                ·
                  refine ⟨2418623508015316420004621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1612415672010210946669747 2418623508015316420004621)
                  ·
                    refine ⟨906983815505743657501733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2418623508015316420004621 906983815505743657501733)
                    ·
                      rfl

theorem cell22_2649517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_2649517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2649517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2649517 prefixEnd_2649517 := by exact prefixLift 2649517
  have htrace : WordTrace (prefixWord ++ tailWord_2649517) baseStart_2649517 baseEnd_2649517 := by
    simpa [prefixWord, tailWord_2649517, baseEnd_2649517] using wordTrace_append hprefix tailTrace_2649517
  have hstable : (prefixWord ++ tailWord_2649517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649517).length < 2 ^ (prefixWord ++ tailWord_2649517).sum := by decide
  have hdescent : baseEnd_2649517 < baseStart_2649517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
