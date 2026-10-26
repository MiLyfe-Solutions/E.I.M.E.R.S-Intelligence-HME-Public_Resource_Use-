import V185TrunkScan22Chunk161

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1446450 : List Nat := [3, 2, 1, 1, 2, 1, 3, 5, 4]
def baseStart_1446450 : Nat := 118140960795 + 1446450 * 2 ^ 59
def prefixEnd_1446450 : Nat := 4983230072969 + 3 ^ 40 * 1446450 * 2
def baseEnd_1446450 : Nat := 165049798376882442538423

theorem tailTrace_1446450 : CollatzResearch.WordTrace tailWord_1446450 prefixEnd_1446450 165049798376882442538423 := by
  unfold tailWord_1446450
  simp only [CollatzResearch.WordTrace]
  refine ⟨13189091402441539709432201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35170910406510772558485869 13189091402441539709432201)
  ·
    refine ⟨9891818551831154782074151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13189091402441539709432201 9891818551831154782074151)
    ·
      refine ⟨14837727827746732173111227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9891818551831154782074151 14837727827746732173111227)
      ·
        refine ⟨22256591741620098259666841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14837727827746732173111227 22256591741620098259666841)
        ·
          refine ⟨16692443806215073694750131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22256591741620098259666841 16692443806215073694750131)
          ·
            refine ⟨25038665709322610542125197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16692443806215073694750131 25038665709322610542125197)
            ·
              refine ⟨9389499640995978953296949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25038665709322610542125197 9389499640995978953296949)
              ·
                refine ⟨880265591343373026871589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9389499640995978953296949 880265591343373026871589)
                ·
                  refine ⟨165049798376882442538423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 880265591343373026871589 165049798376882442538423)
                  ·
                    rfl

theorem cell22_1446450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_1446450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1446450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1446450 prefixEnd_1446450 := by exact prefixLift 1446450
  have htrace : WordTrace (prefixWord ++ tailWord_1446450) baseStart_1446450 baseEnd_1446450 := by
    simpa [prefixWord, tailWord_1446450, baseEnd_1446450] using wordTrace_append hprefix tailTrace_1446450
  have hstable : (prefixWord ++ tailWord_1446450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446450).length < 2 ^ (prefixWord ++ tailWord_1446450).sum := by decide
  have hdescent : baseEnd_1446450 < baseStart_1446450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446463 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 4, 4]
def baseStart_1446463 : Nat := 118140960795 + 1446463 * 2 ^ 59
def prefixEnd_1446463 : Nat := 4983230072969 + 3 ^ 40 * 1446463 * 2
def baseEnd_1446463 : Nat := 495153845296319627040229

theorem tailTrace_1446463 : CollatzResearch.WordTrace tailWord_1446463 prefixEnd_1446463 495153845296319627040229 := by
  unfold tailWord_1446463
  simp only [CollatzResearch.WordTrace]
  refine ⟨52756839758719062057952043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35171226505812708038634695 52756839758719062057952043)
  ·
    refine ⟨79135259638078593086928065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52756839758719062057952043 79135259638078593086928065)
    ·
      refine ⟨59351444728558944815196049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79135259638078593086928065 59351444728558944815196049)
      ·
        refine ⟨44513583546419208611397037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59351444728558944815196049 44513583546419208611397037)
        ·
          refine ⟨16692593829907203229273889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44513583546419208611397037 16692593829907203229273889)
          ·
            refine ⟨12519445372430402421955417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16692593829907203229273889 12519445372430402421955417)
            ·
              refine ⟨9389584029322801816466563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12519445372430402421955417 9389584029322801816466563)
              ·
                refine ⟨14084376043984202724699845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9389584029322801816466563 14084376043984202724699845)
                ·
                  refine ⟨2640820508247038010881221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14084376043984202724699845 2640820508247038010881221)
                  ·
                    refine ⟨495153845296319627040229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2640820508247038010881221 495153845296319627040229)
                    ·
                      rfl

theorem cell22_1446463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 4].length) (baseStart_1446463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1446463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1446463 prefixEnd_1446463 := by exact prefixLift 1446463
  have htrace : WordTrace (prefixWord ++ tailWord_1446463) baseStart_1446463 baseEnd_1446463 := by
    simpa [prefixWord, tailWord_1446463, baseEnd_1446463] using wordTrace_append hprefix tailTrace_1446463
  have hstable : (prefixWord ++ tailWord_1446463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446463).length < 2 ^ (prefixWord ++ tailWord_1446463).sum := by decide
  have hdescent : baseEnd_1446463 < baseStart_1446463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446574 : List Nat := [4, 1, 4, 1, 1, 2, 2, 2, 5]
def baseStart_1446574 : Nat := 118140960795 + 1446574 * 2 ^ 59
def prefixEnd_1446574 : Nat := 4983230072969 + 3 ^ 40 * 1446574 * 2
def baseEnd_1446574 : Nat := 165063947621584112504963

theorem tailTrace_1446574 : CollatzResearch.WordTrace tailWord_1446574 prefixEnd_1446574 165063947621584112504963 := by
  unfold tailWord_1446574
  simp only [CollatzResearch.WordTrace]
  refine ⟨6595111032664616001905347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35173925507544618676828517 6595111032664616001905347)
  ·
    refine ⟨9892666548996924002858021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6595111032664616001905347 9892666548996924002858021)
    ·
      refine ⟨1854874977936923250535879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9892666548996924002858021 1854874977936923250535879)
      ·
        refine ⟨2782312466905384875803819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1854874977936923250535879 2782312466905384875803819)
        ·
          refine ⟨4173468700358077313705729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2782312466905384875803819 4173468700358077313705729)
          ·
            refine ⟨3130101525268557985279297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4173468700358077313705729 3130101525268557985279297)
            ·
              refine ⟨2347576143951418488959473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3130101525268557985279297 2347576143951418488959473)
              ·
                refine ⟨1760682107963563866719605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2347576143951418488959473 1760682107963563866719605)
                ·
                  refine ⟨165063947621584112504963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1760682107963563866719605 165063947621584112504963)
                  ·
                    rfl

theorem cell22_1446574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_1446574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1446574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1446574 prefixEnd_1446574 := by exact prefixLift 1446574
  have htrace : WordTrace (prefixWord ++ tailWord_1446574) baseStart_1446574 baseEnd_1446574 := by
    simpa [prefixWord, tailWord_1446574, baseEnd_1446574] using wordTrace_append hprefix tailTrace_1446574
  have hstable : (prefixWord ++ tailWord_1446574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446574).length < 2 ^ (prefixWord ++ tailWord_1446574).sum := by decide
  have hdescent : baseEnd_1446574 < baseStart_1446574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446600 : List Nat := [2, 1, 3, 1, 2, 3, 1, 3, 1, 5]
def baseStart_1446600 : Nat := 118140960795 + 1446600 * 2 ^ 59
def prefixEnd_1446600 : Nat := 4983230072969 + 3 ^ 40 * 1446600 * 2
def baseEnd_1446600 : Nat := 495200743196096936364809

theorem tailTrace_1446600 : CollatzResearch.WordTrace tailWord_1446600 prefixEnd_1446600 495200743196096936364809 := by
  unfold tailWord_1446600
  simp only [CollatzResearch.WordTrace]
  refine ⟨26380918279611367227844627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35174557706148489637126169 26380918279611367227844627)
  ·
    refine ⟨39571377419417050841766941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26380918279611367227844627 39571377419417050841766941)
    ·
      refine ⟨14839266532281394065662603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39571377419417050841766941 14839266532281394065662603)
      ·
        refine ⟨22258899798422091098493905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14839266532281394065662603 22258899798422091098493905)
        ·
          refine ⟨16694174848816568323870429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22258899798422091098493905 16694174848816568323870429)
          ·
            refine ⟨6260315568306213121451411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16694174848816568323870429 6260315568306213121451411)
            ·
              refine ⟨9390473352459319682177117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6260315568306213121451411 9390473352459319682177117)
              ·
                refine ⟨3521427507172244880816419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9390473352459319682177117 3521427507172244880816419)
                ·
                  refine ⟨5282141260758367321224629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3521427507172244880816419 5282141260758367321224629)
                  ·
                    refine ⟨495200743196096936364809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5282141260758367321224629 495200743196096936364809)
                    ·
                      rfl

theorem cell22_1446600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_1446600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1446600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1446600 prefixEnd_1446600 := by exact prefixLift 1446600
  have htrace : WordTrace (prefixWord ++ tailWord_1446600) baseStart_1446600 baseEnd_1446600 := by
    simpa [prefixWord, tailWord_1446600, baseEnd_1446600] using wordTrace_append hprefix tailTrace_1446600
  have hstable : (prefixWord ++ tailWord_1446600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446600).length < 2 ^ (prefixWord ++ tailWord_1446600).sum := by decide
  have hdescent : baseEnd_1446600 < baseStart_1446600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446615 : List Nat := [1, 1, 3, 2, 1, 5, 1, 1, 1, 6]
def baseStart_1446615 : Nat := 118140960795 + 1446615 * 2 ^ 59
def prefixEnd_1446615 : Nat := 4983230072969 + 3 ^ 40 * 1446615 * 2
def baseEnd_1446615 : Nat := 495205878002641897239763

theorem tailTrace_1446615 : CollatzResearch.WordTrace tailWord_1446615 prefixEnd_1446615 495205878002641897239763 := by
  unfold tailWord_1446615
  simp only [CollatzResearch.WordTrace]
  refine ⟨52762383654168392017485299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35174922436112261344990199 52762383654168392017485299)
  ·
    refine ⟨79143575481252588026227949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52762383654168392017485299 79143575481252588026227949)
    ·
      refine ⟨29678840805469720509835481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79143575481252588026227949 29678840805469720509835481)
      ·
        refine ⟨22259130604102290382376611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29678840805469720509835481 22259130604102290382376611)
        ·
          refine ⟨33388695906153435573564917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22259130604102290382376611 33388695906153435573564917)
          ·
            refine ⟨3130190241201884585021711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33388695906153435573564917 3130190241201884585021711)
            ·
              refine ⟨4695285361802826877532567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3130190241201884585021711 4695285361802826877532567)
              ·
                refine ⟨7042928042704240316298851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4695285361802826877532567 7042928042704240316298851)
                ·
                  refine ⟨10564392064056360474448277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7042928042704240316298851 10564392064056360474448277)
                  ·
                    refine ⟨495205878002641897239763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10564392064056360474448277 495205878002641897239763)
                    ·
                      rfl

theorem cell22_1446615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_1446615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1446615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1446615 prefixEnd_1446615 := by exact prefixLift 1446615
  have htrace : WordTrace (prefixWord ++ tailWord_1446615) baseStart_1446615 baseEnd_1446615 := by
    simpa [prefixWord, tailWord_1446615, baseEnd_1446615] using wordTrace_append hprefix tailTrace_1446615
  have hstable : (prefixWord ++ tailWord_1446615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446615).length < 2 ^ (prefixWord ++ tailWord_1446615).sum := by decide
  have hdescent : baseEnd_1446615 < baseStart_1446615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446709 : List Nat := [1, 3, 3, 1, 3, 1, 4, 1, 5]
def baseStart_1446709 : Nat := 118140960795 + 1446709 * 2 ^ 59
def prefixEnd_1446709 : Nat := 4983230072969 + 3 ^ 40 * 1446709 * 2
def baseEnd_1446709 : Nat := 165079352041218995129825

theorem tailTrace_1446709 : CollatzResearch.WordTrace tailWord_1446709 prefixEnd_1446709 165079352041218995129825 := by
  unfold tailWord_1446709
  simp only [CollatzResearch.WordTrace]
  refine ⟨52765812115827846071407181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35177208077218564047604787 52765812115827846071407181)
  ·
    refine ⟨19787179543435442276777693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52765812115827846071407181 19787179543435442276777693)
    ·
      refine ⟨7420192328788290853791635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19787179543435442276777693 7420192328788290853791635)
      ·
        refine ⟨11130288493182436280687453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7420192328788290853791635 11130288493182436280687453)
        ·
          refine ⟨4173858184943413605257795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11130288493182436280687453 4173858184943413605257795)
          ·
            refine ⟨6260787277415120407886693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4173858184943413605257795 6260787277415120407886693)
            ·
              refine ⟨1173897614515335076478755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6260787277415120407886693 1173897614515335076478755)
              ·
                refine ⟨1760846421773002614718133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1173897614515335076478755 1760846421773002614718133)
                ·
                  refine ⟨165079352041218995129825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1760846421773002614718133 165079352041218995129825)
                  ·
                    rfl

theorem cell22_1446709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 5].length) (baseStart_1446709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1446709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1446709 prefixEnd_1446709 := by exact prefixLift 1446709
  have htrace : WordTrace (prefixWord ++ tailWord_1446709) baseStart_1446709 baseEnd_1446709 := by
    simpa [prefixWord, tailWord_1446709, baseEnd_1446709] using wordTrace_append hprefix tailTrace_1446709
  have hstable : (prefixWord ++ tailWord_1446709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446709).length < 2 ^ (prefixWord ++ tailWord_1446709).sum := by decide
  have hdescent : baseEnd_1446709 < baseStart_1446709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446720 : List Nat := [2, 1, 1, 2, 2, 1, 1, 6, 6]
def baseStart_1446720 : Nat := 118140960795 + 1446720 * 2 ^ 59
def prefixEnd_1446720 : Nat := 4983230072969 + 3 ^ 40 * 1446720 * 2
def baseEnd_1446720 : Nat := 165080607216152207788147

theorem tailTrace_1446720 : CollatzResearch.WordTrace tailWord_1446720 prefixEnd_1446720 165080607216152207788147 := by
  unfold tailWord_1446720
  simp only [CollatzResearch.WordTrace]
  refine ⟨26383106659393997475028807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35177475545858663300038409 26383106659393997475028807)
  ·
    refine ⟨39574659989090996212543211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26383106659393997475028807 39574659989090996212543211)
    ·
      refine ⟨59361989983636494318814817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39574659989090996212543211 59361989983636494318814817)
      ·
        refine ⟨44521492487727370739111113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59361989983636494318814817 44521492487727370739111113)
        ·
          refine ⟨33391119365795528054333335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44521492487727370739111113 33391119365795528054333335)
          ·
            refine ⟨50086679048693292081500003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33391119365795528054333335 50086679048693292081500003)
            ·
              refine ⟨75130018573039938122250005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50086679048693292081500003 75130018573039938122250005)
              ·
                refine ⟨3521719620611247099480469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75130018573039938122250005 3521719620611247099480469)
                ·
                  refine ⟨165080607216152207788147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3521719620611247099480469 165080607216152207788147)
                  ·
                    rfl

theorem cell22_1446720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 6].length) (baseStart_1446720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1446720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1446720 prefixEnd_1446720 := by exact prefixLift 1446720
  have htrace : WordTrace (prefixWord ++ tailWord_1446720) baseStart_1446720 baseEnd_1446720 := by
    simpa [prefixWord, tailWord_1446720, baseEnd_1446720] using wordTrace_append hprefix tailTrace_1446720
  have hstable : (prefixWord ++ tailWord_1446720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446720).length < 2 ^ (prefixWord ++ tailWord_1446720).sum := by decide
  have hdescent : baseEnd_1446720 < baseStart_1446720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446769 : List Nat := [1, 2, 2, 2, 1, 4, 2, 3, 2, 3]
def baseStart_1446769 : Nat := 118140960795 + 1446769 * 2 ^ 59
def prefixEnd_1446769 : Nat := 4983230072969 + 3 ^ 40 * 1446769 * 2
def baseEnd_1446769 : Nat := 495258595349836828889291

theorem tailTrace_1446769 : CollatzResearch.WordTrace tailWord_1446769 prefixEnd_1446769 495258595349836828889291 := by
  unfold tailWord_1446769
  simp only [CollatzResearch.WordTrace]
  refine ⟨52768000495610476318591361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35178666997073650879060907 52768000495610476318591361)
  ·
    refine ⟨39576000371707857238943521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52768000495610476318591361 39576000371707857238943521)
    ·
      refine ⟨29682000278780892929207641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39576000371707857238943521 29682000278780892929207641)
      ·
        refine ⟨22261500209085669696905731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29682000278780892929207641 22261500209085669696905731)
        ·
          refine ⟨33392250313628504545358597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22261500209085669696905731 33392250313628504545358597)
          ·
            refine ⟨6261046933805344602254737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33392250313628504545358597 6261046933805344602254737)
            ·
              refine ⟨4695785200354008451691053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6261046933805344602254737 4695785200354008451691053)
              ·
                refine ⟨1760919450132753169384145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4695785200354008451691053 1760919450132753169384145)
                ·
                  refine ⟨1320689587599564877038109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1760919450132753169384145 1320689587599564877038109)
                  ·
                    refine ⟨495258595349836828889291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1320689587599564877038109 495258595349836828889291)
                    ·
                      rfl

theorem cell22_1446769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2, 3].length) (baseStart_1446769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1446769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1446769 prefixEnd_1446769 := by exact prefixLift 1446769
  have htrace : WordTrace (prefixWord ++ tailWord_1446769) baseStart_1446769 baseEnd_1446769 := by
    simpa [prefixWord, tailWord_1446769, baseEnd_1446769] using wordTrace_append hprefix tailTrace_1446769
  have hstable : (prefixWord ++ tailWord_1446769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446769).length < 2 ^ (prefixWord ++ tailWord_1446769).sum := by decide
  have hdescent : baseEnd_1446769 < baseStart_1446769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446848 : List Nat := [2, 1, 1, 2, 3, 5, 1, 3, 1, 3]
def baseStart_1446848 : Nat := 118140960795 + 1446848 * 2 ^ 59
def prefixEnd_1446848 : Nat := 4983230072969 + 3 ^ 40 * 1446848 * 2
def baseEnd_1446848 : Nat := 495285638664306956164049

theorem tailTrace_1446848 : CollatzResearch.WordTrace tailWord_1446848 prefixEnd_1446848 495285638664306956164049 := by
  unfold tailWord_1446848
  simp only [CollatzResearch.WordTrace]
  refine ⟨26385440931162136405358599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35180587908216181873811465 26385440931162136405358599)
  ·
    refine ⟨39578161396743204608037899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26385440931162136405358599 39578161396743204608037899)
    ·
      refine ⟨59367242095114806912056849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39578161396743204608037899 59367242095114806912056849)
      ·
        refine ⟨44525431571336105184042637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59367242095114806912056849 44525431571336105184042637)
        ·
          refine ⟨16697036839251039444015989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44525431571336105184042637 16697036839251039444015989)
          ·
            refine ⟨1565347203679784947876499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16697036839251039444015989 1565347203679784947876499)
            ·
              refine ⟨2348020805519677421814749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1565347203679784947876499 2348020805519677421814749)
              ·
                refine ⟨880507802069879033180531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2348020805519677421814749 880507802069879033180531)
                ·
                  refine ⟨1320761703104818549770797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 880507802069879033180531 1320761703104818549770797)
                  ·
                    refine ⟨495285638664306956164049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1320761703104818549770797 495285638664306956164049)
                    ·
                      rfl

theorem cell22_1446848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3, 1, 3].length) (baseStart_1446848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1446848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1446848 prefixEnd_1446848 := by exact prefixLift 1446848
  have htrace : WordTrace (prefixWord ++ tailWord_1446848) baseStart_1446848 baseEnd_1446848 := by
    simpa [prefixWord, tailWord_1446848, baseEnd_1446848] using wordTrace_append hprefix tailTrace_1446848
  have hstable : (prefixWord ++ tailWord_1446848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446848).length < 2 ^ (prefixWord ++ tailWord_1446848).sum := by decide
  have hdescent : baseEnd_1446848 < baseStart_1446848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446919 : List Nat := [1, 1, 4, 3, 1, 1, 1, 4, 2, 4]
def baseStart_1446919 : Nat := 118140960795 + 1446919 * 2 ^ 59
def prefixEnd_1446919 : Nat := 4983230072969 + 3 ^ 40 * 1446919 * 2
def baseEnd_1446919 : Nat := 495309943415286437638831

theorem tailTrace_1446919 : CollatzResearch.WordTrace tailWord_1446919 prefixEnd_1446919 495309943415286437638831 := by
  unfold tailWord_1446919
  simp only [CollatzResearch.WordTrace]
  refine ⟨52773471445067051936551811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35182314296711367957701207 52773471445067051936551811)
  ·
    refine ⟨79160207167600577904827717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52773471445067051936551811 79160207167600577904827717)
    ·
      refine ⟨14842538843925108357155197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79160207167600577904827717 14842538843925108357155197)
      ·
        refine ⟨5565952066471915633933199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14842538843925108357155197 5565952066471915633933199)
        ·
          refine ⟨8348928099707873450899799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5565952066471915633933199 8348928099707873450899799)
          ·
            refine ⟨12523392149561810176349699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8348928099707873450899799 12523392149561810176349699)
            ·
              refine ⟨18785088224342715264524549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12523392149561810176349699 18785088224342715264524549)
              ·
                refine ⟨3522204042064259112098353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18785088224342715264524549 3522204042064259112098353)
                ·
                  refine ⟨2641653031548194334073765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3522204042064259112098353 2641653031548194334073765)
                  ·
                    refine ⟨495309943415286437638831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2641653031548194334073765 495309943415286437638831)
                    ·
                      rfl

theorem cell22_1446919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_1446919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1446919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1446919 prefixEnd_1446919 := by exact prefixLift 1446919
  have htrace : WordTrace (prefixWord ++ tailWord_1446919) baseStart_1446919 baseEnd_1446919 := by
    simpa [prefixWord, tailWord_1446919, baseEnd_1446919] using wordTrace_append hprefix tailTrace_1446919
  have hstable : (prefixWord ++ tailWord_1446919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446919).length < 2 ^ (prefixWord ++ tailWord_1446919).sum := by decide
  have hdescent : baseEnd_1446919 < baseStart_1446919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446923 : List Nat := [1, 1, 1, 1, 6, 4, 2, 2, 4]
def baseStart_1446923 : Nat := 118140960795 + 1446923 * 2 ^ 59
def prefixEnd_1446923 : Nat := 4983230072969 + 3 ^ 40 * 1446923 * 2
def baseEnd_1446923 : Nat := 165103770899010586846273

theorem tailTrace_1446923 : CollatzResearch.WordTrace tailWord_1446923 prefixEnd_1446923 165103770899010586846273 := by
  unfold tailWord_1446923
  simp only [CollatzResearch.WordTrace]
  refine ⟨52773617337052560619697423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35182411558035040413131615 52773617337052560619697423)
  ·
    refine ⟨79160426005578840929546135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52773617337052560619697423 79160426005578840929546135)
    ·
      refine ⟨118740639008368261394319203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79160426005578840929546135 118740639008368261394319203)
      ·
        refine ⟨178110958512552392091478805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118740639008368261394319203 178110958512552392091478805)
        ·
          refine ⟨8348951180275893379288069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 178110958512552392091478805 8348951180275893379288069)
          ·
            refine ⟨1565428346301730008616513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8348951180275893379288069 1565428346301730008616513)
            ·
              refine ⟨1174071259726297506462385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1565428346301730008616513 1174071259726297506462385)
              ·
                refine ⟨880553444794723129846789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1174071259726297506462385 880553444794723129846789)
                ·
                  refine ⟨165103770899010586846273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 880553444794723129846789 165103770899010586846273)
                  ·
                    rfl

theorem cell22_1446923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2, 4].length) (baseStart_1446923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1446923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1446923 prefixEnd_1446923 := by exact prefixLift 1446923
  have htrace : WordTrace (prefixWord ++ tailWord_1446923) baseStart_1446923 baseEnd_1446923 := by
    simpa [prefixWord, tailWord_1446923, baseEnd_1446923] using wordTrace_append hprefix tailTrace_1446923
  have hstable : (prefixWord ++ tailWord_1446923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446923).length < 2 ^ (prefixWord ++ tailWord_1446923).sum := by decide
  have hdescent : baseEnd_1446923 < baseStart_1446923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446983 : List Nat := [1, 1, 4, 1, 3, 2, 2, 4, 1, 3]
def baseStart_1446983 : Nat := 118140960795 + 1446983 * 2 ^ 59
def prefixEnd_1446983 : Nat := 4983230072969 + 3 ^ 40 * 1446983 * 2
def baseEnd_1446983 : Nat := 495331851923211604038635

theorem tailTrace_1446983 : CollatzResearch.WordTrace tailWord_1446983 prefixEnd_1446983 495331851923211604038635 := by
  unfold tailWord_1446983
  simp only [CollatzResearch.WordTrace]
  refine ⟨52775805716835190866881603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35183870477890127244587735 52775805716835190866881603)
  ·
    refine ⟨79163708575252786300322405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52775805716835190866881603 79163708575252786300322405)
    ·
      refine ⟨14843195357859897431310451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79163708575252786300322405 14843195357859897431310451)
      ·
        refine ⟨22264793036789846146965677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14843195357859897431310451 22264793036789846146965677)
        ·
          refine ⟨8349297388796192305112129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22264793036789846146965677 8349297388796192305112129)
          ·
            refine ⟨6261973041597144228834097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8349297388796192305112129 6261973041597144228834097)
            ·
              refine ⟨4696479781197858171625573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6261973041597144228834097 4696479781197858171625573)
              ·
                refine ⟨880589958974598407179795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4696479781197858171625573 880589958974598407179795)
                ·
                  refine ⟨1320884938461897610769693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 880589958974598407179795 1320884938461897610769693)
                  ·
                    refine ⟨495331851923211604038635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1320884938461897610769693 495331851923211604038635)
                    ·
                      rfl

theorem cell22_1446983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_1446983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1446983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1446983 prefixEnd_1446983 := by exact prefixLift 1446983
  have htrace : WordTrace (prefixWord ++ tailWord_1446983) baseStart_1446983 baseEnd_1446983 := by
    simpa [prefixWord, tailWord_1446983, baseEnd_1446983] using wordTrace_append hprefix tailTrace_1446983
  have hstable : (prefixWord ++ tailWord_1446983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446983).length < 2 ^ (prefixWord ++ tailWord_1446983).sum := by decide
  have hdescent : baseEnd_1446983 < baseStart_1446983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447009 : List Nat := [1, 2, 3, 1, 1, 2, 2, 3, 3, 4]
def baseStart_1447009 : Nat := 118140960795 + 1447009 * 2 ^ 59
def prefixEnd_1447009 : Nat := 4983230072969 + 3 ^ 40 * 1447009 * 2
def baseEnd_1447009 : Nat := 495340752254556202888555

theorem tailTrace_1447009 : CollatzResearch.WordTrace tailWord_1447009 prefixEnd_1447009 495340752254556202888555 := by
  unfold tailWord_1447009
  simp only [CollatzResearch.WordTrace]
  refine ⟨52776754014740997307328081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35184502676493998204885387 52776754014740997307328081)
  ·
    refine ⟨39582565511055747980496061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52776754014740997307328081 39582565511055747980496061)
    ·
      refine ⟨14843462066645905492686023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39582565511055747980496061 14843462066645905492686023)
      ·
        refine ⟨22265193099968858239029035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14843462066645905492686023 22265193099968858239029035)
        ·
          refine ⟨33397789649953287358543553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22265193099968858239029035 33397789649953287358543553)
          ·
            refine ⟨25048342237464965518907665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33397789649953287358543553 25048342237464965518907665)
            ·
              refine ⟨18786256678098724139180749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25048342237464965518907665 18786256678098724139180749)
              ·
                refine ⟨7044846254287021552192781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18786256678098724139180749 7044846254287021552192781)
                ·
                  refine ⟨2641817345357633082072293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7044846254287021552192781 2641817345357633082072293)
                  ·
                    refine ⟨495340752254556202888555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2641817345357633082072293 495340752254556202888555)
                    ·
                      rfl

theorem cell22_1447009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_1447009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1447009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1447009 prefixEnd_1447009 := by exact prefixLift 1447009
  have htrace : WordTrace (prefixWord ++ tailWord_1447009) baseStart_1447009 baseEnd_1447009 := by
    simpa [prefixWord, tailWord_1447009, baseEnd_1447009] using wordTrace_append hprefix tailTrace_1447009
  have hstable : (prefixWord ++ tailWord_1447009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447009).length < 2 ^ (prefixWord ++ tailWord_1447009).sum := by decide
  have hdescent : baseEnd_1447009 < baseStart_1447009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447026 : List Nat := [3, 2, 1, 2, 2, 1, 1, 5, 1, 4]
def baseStart_1447026 : Nat := 118140960795 + 1447026 * 2 ^ 59
def prefixEnd_1447026 : Nat := 4983230072969 + 3 ^ 40 * 1447026 * 2
def baseEnd_1447026 : Nat := 495346571701973825213503

theorem tailTrace_1447026 : CollatzResearch.WordTrace tailWord_1447026 prefixEnd_1447026 495346571701973825213503 := by
  unfold tailWord_1447026
  simp only [CollatzResearch.WordTrace]
  refine ⟨13194343513919852302674233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35184916037119606140464621 13194343513919852302674233)
  ·
    refine ⟨9895757635439889227005675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13194343513919852302674233 9895757635439889227005675)
    ·
      refine ⟨14843636453159833840508513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9895757635439889227005675 14843636453159833840508513)
      ·
        refine ⟨11132727339869875380381385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14843636453159833840508513 11132727339869875380381385)
        ·
          refine ⟨8349545504902406535286039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11132727339869875380381385 8349545504902406535286039)
          ·
            refine ⟨12524318257353609802929059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8349545504902406535286039 12524318257353609802929059)
            ·
              refine ⟨18786477386030414704393589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12524318257353609802929059 18786477386030414704393589)
              ·
                refine ⟨1761232254940351378536899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18786477386030414704393589 1761232254940351378536899)
                ·
                  refine ⟨2641848382410527067805349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1761232254940351378536899 2641848382410527067805349)
                  ·
                    refine ⟨495346571701973825213503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2641848382410527067805349 495346571701973825213503)
                    ·
                      rfl

theorem cell22_1447026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_1447026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1447026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1447026 prefixEnd_1447026 := by exact prefixLift 1447026
  have htrace : WordTrace (prefixWord ++ tailWord_1447026) baseStart_1447026 baseEnd_1447026 := by
    simpa [prefixWord, tailWord_1447026, baseEnd_1447026] using wordTrace_append hprefix tailTrace_1447026
  have hstable : (prefixWord ++ tailWord_1447026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447026).length < 2 ^ (prefixWord ++ tailWord_1447026).sum := by decide
  have hdescent : baseEnd_1447026 < baseStart_1447026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447041 : List Nat := [1, 2, 4, 2, 2, 1, 3, 1, 6]
def baseStart_1447041 : Nat := 118140960795 + 1447041 * 2 ^ 59
def prefixEnd_1447041 : Nat := 4983230072969 + 3 ^ 40 * 1447041 * 2
def baseEnd_1447041 : Nat := 165117235502839595362819

theorem tailTrace_1447041 : CollatzResearch.WordTrace tailWord_1447041 prefixEnd_1447041 165117235502839595362819 := by
  unfold tailWord_1447041
  simp only [CollatzResearch.WordTrace]
  refine ⟨52777921150625066772492977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35185280767083377848328651 52777921150625066772492977)
  ·
    refine ⟨39583440862968800079369733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52777921150625066772492977 39583440862968800079369733)
    ·
      refine ⟨7421895161806650014881825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39583440862968800079369733 7421895161806650014881825)
      ·
        refine ⟨5566421371354987511161369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7421895161806650014881825 5566421371354987511161369)
        ·
          refine ⟨4174816028516240633371027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5566421371354987511161369 4174816028516240633371027)
          ·
            refine ⟨6262224042774360950056541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4174816028516240633371027 6262224042774360950056541)
            ·
              refine ⟨2348334016040385356271203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6262224042774360950056541 2348334016040385356271203)
              ·
                refine ⟨3522501024060578034406805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2348334016040385356271203 3522501024060578034406805)
                ·
                  refine ⟨165117235502839595362819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3522501024060578034406805 165117235502839595362819)
                  ·
                    rfl

theorem cell22_1447041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 6].length) (baseStart_1447041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1447041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1447041 prefixEnd_1447041 := by exact prefixLift 1447041
  have htrace : WordTrace (prefixWord ++ tailWord_1447041) baseStart_1447041 baseEnd_1447041 := by
    simpa [prefixWord, tailWord_1447041, baseEnd_1447041] using wordTrace_append hprefix tailTrace_1447041
  have hstable : (prefixWord ++ tailWord_1447041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447041).length < 2 ^ (prefixWord ++ tailWord_1447041).sum := by decide
  have hdescent : baseEnd_1447041 < baseStart_1447041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447069 : List Nat := [1, 4, 2, 1, 1, 2, 1, 10]
def baseStart_1447069 : Nat := 118140960795 + 1447069 * 2 ^ 59
def prefixEnd_1447069 : Nat := 4983230072969 + 3 ^ 40 * 1447069 * 2
def baseEnd_1447069 : Nat := 55040143497859560709819

theorem tailTrace_1447069 : CollatzResearch.WordTrace tailWord_1447069 prefixEnd_1447069 55040143497859560709819 := by
  unfold tailWord_1447069
  simp only [CollatzResearch.WordTrace]
  refine ⟨52778942394523627554512261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35185961596349085036341507 52778942394523627554512261)
  ·
    refine ⟨9896051698973180166471049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52778942394523627554512261 9896051698973180166471049)
    ·
      refine ⟨7422038774229885124853287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9896051698973180166471049 7422038774229885124853287)
      ·
        refine ⟨11133058161344827687279931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7422038774229885124853287 11133058161344827687279931)
        ·
          refine ⟨16699587242017241530919897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11133058161344827687279931 16699587242017241530919897)
          ·
            refine ⟨12524690431512931148189923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16699587242017241530919897 12524690431512931148189923)
            ·
              refine ⟨18787035647269396722284885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12524690431512931148189923 18787035647269396722284885)
              ·
                refine ⟨55040143497859560709819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18787035647269396722284885 55040143497859560709819)
                ·
                  rfl

theorem cell22_1447069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 10].length) (baseStart_1447069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1447069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1447069 prefixEnd_1447069 := by exact prefixLift 1447069
  have htrace : WordTrace (prefixWord ++ tailWord_1447069) baseStart_1447069 baseEnd_1447069 := by
    simpa [prefixWord, tailWord_1447069, baseEnd_1447069] using wordTrace_append hprefix tailTrace_1447069
  have hstable : (prefixWord ++ tailWord_1447069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447069).length < 2 ^ (prefixWord ++ tailWord_1447069).sum := by decide
  have hdescent : baseEnd_1447069 < baseStart_1447069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447129 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 3, 7]
def baseStart_1447129 : Nat := 118140960795 + 1447129 * 2 ^ 59
def prefixEnd_1447129 : Nat := 4983230072969 + 3 ^ 40 * 1447129 * 2
def baseEnd_1447129 : Nat := 495381830706915889888187

theorem tailTrace_1447129 : CollatzResearch.WordTrace tailWord_1447129 prefixEnd_1447129 495381830706915889888187 := by
  unfold tailWord_1447129
  simp only [CollatzResearch.WordTrace]
  refine ⟨52781130774306257801696441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35187420516204171867797627 52781130774306257801696441)
  ·
    refine ⟨39585848080729693351272331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52781130774306257801696441 39585848080729693351272331)
    ·
      refine ⟨59378772121094540026908497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39585848080729693351272331 59378772121094540026908497)
      ·
        refine ⟨44534079090820905020181373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59378772121094540026908497 44534079090820905020181373)
        ·
          refine ⟨16700279659057839382568015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44534079090820905020181373 16700279659057839382568015)
          ·
            refine ⟨25050419488586759073852023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16700279659057839382568015 25050419488586759073852023)
            ·
              refine ⟨37575629232880138610778035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25050419488586759073852023 37575629232880138610778035)
              ·
                refine ⟨56363443849320207916167053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37575629232880138610778035 56363443849320207916167053)
                ·
                  refine ⟨21136291443495077968562645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56363443849320207916167053 21136291443495077968562645)
                  ·
                    refine ⟨495381830706915889888187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21136291443495077968562645 495381830706915889888187)
                    ·
                      rfl

theorem cell22_1447129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 7].length) (baseStart_1447129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1447129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1447129 prefixEnd_1447129 := by exact prefixLift 1447129
  have htrace : WordTrace (prefixWord ++ tailWord_1447129) baseStart_1447129 baseEnd_1447129 := by
    simpa [prefixWord, tailWord_1447129, baseEnd_1447129] using wordTrace_append hprefix tailTrace_1447129
  have hstable : (prefixWord ++ tailWord_1447129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447129).length < 2 ^ (prefixWord ++ tailWord_1447129).sum := by decide
  have hdescent : baseEnd_1447129 < baseStart_1447129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447146 : List Nat := [3, 1, 3, 1, 1, 3, 1, 2, 2, 5]
def baseStart_1447146 : Nat := 118140960795 + 1447146 * 2 ^ 59
def prefixEnd_1447146 : Nat := 4983230072969 + 3 ^ 40 * 1447146 * 2
def baseEnd_1447146 : Nat := 495387650154333512213135

theorem tailTrace_1447146 : CollatzResearch.WordTrace tailWord_1447146 prefixEnd_1447146 495387650154333512213135 := by
  unfold tailWord_1447146
  simp only [CollatzResearch.WordTrace]
  refine ⟨13195437703811167426266323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35187833876829779803376861 13195437703811167426266323)
  ·
    refine ⟨19793156555716751139399485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13195437703811167426266323 19793156555716751139399485)
    ·
      refine ⟨7422433708393781677274807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19793156555716751139399485 7422433708393781677274807)
      ·
        refine ⟨11133650562590672515912211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7422433708393781677274807 11133650562590672515912211)
        ·
          refine ⟨16700475843886008773868317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11133650562590672515912211 16700475843886008773868317)
          ·
            refine ⟨6262678441457253290200619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16700475843886008773868317 6262678441457253290200619)
            ·
              refine ⟨9394017662185879935300929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6262678441457253290200619 9394017662185879935300929)
              ·
                refine ⟨7045513246639409951475697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9394017662185879935300929 7045513246639409951475697)
                ·
                  refine ⟨5284134934979557463606773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7045513246639409951475697 5284134934979557463606773)
                  ·
                    refine ⟨495387650154333512213135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5284134934979557463606773 495387650154333512213135)
                    ·
                      rfl

theorem cell22_1447146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_1447146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1447146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1447146 prefixEnd_1447146 := by exact prefixLift 1447146
  have htrace : WordTrace (prefixWord ++ tailWord_1447146) baseStart_1447146 baseEnd_1447146 := by
    simpa [prefixWord, tailWord_1447146, baseEnd_1447146] using wordTrace_append hprefix tailTrace_1447146
  have hstable : (prefixWord ++ tailWord_1447146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447146).length < 2 ^ (prefixWord ++ tailWord_1447146).sum := by decide
  have hdescent : baseEnd_1447146 < baseStart_1447146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447148 : List Nat := [2, 2, 1, 1, 2, 6, 1, 2, 5]
def baseStart_1447148 : Nat := 118140960795 + 1447148 * 2 ^ 59
def prefixEnd_1447148 : Nat := 4983230072969 + 3 ^ 40 * 1447148 * 2
def baseEnd_1447148 : Nat := 165129444931735391221043

theorem tailTrace_1447148 : CollatzResearch.WordTrace tailWord_1447148 prefixEnd_1447148 165129444931735391221043 := by
  unfold tailWord_1447148
  simp only [CollatzResearch.WordTrace]
  refine ⟨26390911880618712023319049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35187882507491616031092065 26390911880618712023319049)
  ·
    refine ⟨19793183910464034017489287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26390911880618712023319049 19793183910464034017489287)
    ·
      refine ⟨29689775865696051026233931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19793183910464034017489287 29689775865696051026233931)
      ·
        refine ⟨44534663798544076539350897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29689775865696051026233931 44534663798544076539350897)
        ·
          refine ⟨33400997848908057404513173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44534663798544076539350897 33400997848908057404513173)
          ·
            refine ⟨1565671774167565190836555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33400997848908057404513173 1565671774167565190836555)
            ·
              refine ⟨2348507661251347786254833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1565671774167565190836555 2348507661251347786254833)
              ·
                refine ⟨1761380745938510839691125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2348507661251347786254833 1761380745938510839691125)
                ·
                  refine ⟨165129444931735391221043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1761380745938510839691125 165129444931735391221043)
                  ·
                    rfl

theorem cell22_1447148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 5].length) (baseStart_1447148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1447148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1447148 prefixEnd_1447148 := by exact prefixLift 1447148
  have htrace : WordTrace (prefixWord ++ tailWord_1447148) baseStart_1447148 baseEnd_1447148 := by
    simpa [prefixWord, tailWord_1447148, baseEnd_1447148] using wordTrace_append hprefix tailTrace_1447148
  have hstable : (prefixWord ++ tailWord_1447148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447148).length < 2 ^ (prefixWord ++ tailWord_1447148).sum := by decide
  have hdescent : baseEnd_1447148 < baseStart_1447148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447159 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 10]
def baseStart_1447159 : Nat := 118140960795 + 1447159 * 2 ^ 59
def prefixEnd_1447159 : Nat := 4983230072969 + 3 ^ 40 * 1447159 * 2
def baseEnd_1447159 : Nat := 165130700106668603879365

theorem tailTrace_1447159 : CollatzResearch.WordTrace tailWord_1447159 prefixEnd_1447159 165130700106668603879365 := by
  unfold tailWord_1447159
  simp only [CollatzResearch.WordTrace]
  refine ⟨52782224964197572925288531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35188149976131715283525687 52782224964197572925288531)
  ·
    refine ⟨79173337446296359387932797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52782224964197572925288531 79173337446296359387932797)
    ·
      refine ⟨29690001542361134770474799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79173337446296359387932797 29690001542361134770474799)
      ·
        refine ⟨44535002313541702155712199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29690001542361134770474799 44535002313541702155712199)
        ·
          refine ⟨66802503470312553233568299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44535002313541702155712199 66802503470312553233568299)
          ·
            refine ⟨100203755205468829850352449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66802503470312553233568299 100203755205468829850352449)
            ·
              refine ⟨75152816404101622387764337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100203755205468829850352449 75152816404101622387764337)
              ·
                refine ⟨56364612303076216790823253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75152816404101622387764337 56364612303076216790823253)
                ·
                  refine ⟨165130700106668603879365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 56364612303076216790823253 165130700106668603879365)
                  ·
                    rfl

theorem cell22_1447159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 10].length) (baseStart_1447159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1447159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1447159 prefixEnd_1447159 := by exact prefixLift 1447159
  have htrace : WordTrace (prefixWord ++ tailWord_1447159) baseStart_1447159 baseEnd_1447159 := by
    simpa [prefixWord, tailWord_1447159, baseEnd_1447159] using wordTrace_append hprefix tailTrace_1447159
  have hstable : (prefixWord ++ tailWord_1447159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447159).length < 2 ^ (prefixWord ++ tailWord_1447159).sum := by decide
  have hdescent : baseEnd_1447159 < baseStart_1447159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447186 : List Nat := [3, 2, 4, 2, 1, 2, 1, 3, 1, 3]
def baseStart_1447186 : Nat := 118140960795 + 1447186 * 2 ^ 59
def prefixEnd_1447186 : Nat := 4983230072969 + 3 ^ 40 * 1447186 * 2
def baseEnd_1447186 : Nat := 495401342971786741213013

theorem tailTrace_1447186 : CollatzResearch.WordTrace tailWord_1447186 prefixEnd_1447186 495401342971786741213013 := by
  unfold tailWord_1447186
  simp only [CollatzResearch.WordTrace]
  refine ⟨13195802433774939134130353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35188806490066504357680941 13195802433774939134130353)
  ·
    refine ⟨9896851825331204350597765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13195802433774939134130353 9896851825331204350597765)
    ·
      refine ⟨1855659717249600815737081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9896851825331204350597765 1855659717249600815737081)
      ·
        refine ⟨1391744787937200611802811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1855659717249600815737081 1391744787937200611802811)
        ·
          refine ⟨2087617181905800917704217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1391744787937200611802811 2087617181905800917704217)
          ·
            refine ⟨1565712886429350688278163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2087617181905800917704217 1565712886429350688278163)
            ·
              refine ⟨2348569329644026032417245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1565712886429350688278163 2348569329644026032417245)
              ·
                refine ⟨880713498616509762156467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2348569329644026032417245 880713498616509762156467)
                ·
                  refine ⟨1321070247924764643234701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 880713498616509762156467 1321070247924764643234701)
                  ·
                    refine ⟨495401342971786741213013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1321070247924764643234701 495401342971786741213013)
                    ·
                      rfl

theorem cell22_1447186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_1447186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1447186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1447186 prefixEnd_1447186 := by exact prefixLift 1447186
  have htrace : WordTrace (prefixWord ++ tailWord_1447186) baseStart_1447186 baseEnd_1447186 := by
    simpa [prefixWord, tailWord_1447186, baseEnd_1447186] using wordTrace_append hprefix tailTrace_1447186
  have hstable : (prefixWord ++ tailWord_1447186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447186).length < 2 ^ (prefixWord ++ tailWord_1447186).sum := by decide
  have hdescent : baseEnd_1447186 < baseStart_1447186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447191 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 3, 5]
def baseStart_1447191 : Nat := 118140960795 + 1447191 * 2 ^ 59
def prefixEnd_1447191 : Nat := 4983230072969 + 3 ^ 40 * 1447191 * 2
def baseEnd_1447191 : Nat := 495403054573968394837997

theorem tailTrace_1447191 : CollatzResearch.WordTrace tailWord_1447191 prefixEnd_1447191 495403054573968394837997 := by
  unfold tailWord_1447191
  simp only [CollatzResearch.WordTrace]
  refine ⟨52783392100081642390453427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35188928066721094926968951 52783392100081642390453427)
  ·
    refine ⟨79175088150122463585680141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52783392100081642390453427 79175088150122463585680141)
    ·
      refine ⟨29690658056295923844630053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79175088150122463585680141 29690658056295923844630053)
      ·
        refine ⟨5566998385555485720868135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29690658056295923844630053 5566998385555485720868135)
        ·
          refine ⟨8350497578333228581302203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5566998385555485720868135 8350497578333228581302203)
          ·
            refine ⟨12525746367499842871953305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8350497578333228581302203 12525746367499842871953305)
            ·
              refine ⟨9394309775624882153964979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12525746367499842871953305 9394309775624882153964979)
              ·
                refine ⟨14091464663437323230947469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9394309775624882153964979 14091464663437323230947469)
                ·
                  refine ⟨5284299248788996211605301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14091464663437323230947469 5284299248788996211605301)
                  ·
                    refine ⟨495403054573968394837997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5284299248788996211605301 495403054573968394837997)
                    ·
                      rfl

theorem cell22_1447191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_1447191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1447191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1447191 prefixEnd_1447191 := by exact prefixLift 1447191
  have htrace : WordTrace (prefixWord ++ tailWord_1447191) baseStart_1447191 baseEnd_1447191 := by
    simpa [prefixWord, tailWord_1447191, baseEnd_1447191] using wordTrace_append hprefix tailTrace_1447191
  have hstable : (prefixWord ++ tailWord_1447191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447191).length < 2 ^ (prefixWord ++ tailWord_1447191).sum := by decide
  have hdescent : baseEnd_1447191 < baseStart_1447191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447210 : List Nat := [3, 1, 4, 2, 1, 3, 1, 1, 6]
def baseStart_1447210 : Nat := 118140960795 + 1447210 * 2 ^ 59
def prefixEnd_1447210 : Nat := 4983230072969 + 3 ^ 40 * 1447210 * 2
def baseEnd_1447210 : Nat := 165136519554086226204313

theorem tailTrace_1447210 : CollatzResearch.WordTrace tailWord_1447210 prefixEnd_1447210 165136519554086226204313 := by
  unfold tailWord_1447210
  simp only [CollatzResearch.WordTrace]
  refine ⟨13196021271753202158848771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35189390058008539090263389 13196021271753202158848771)
  ·
    refine ⟨19794031907629803238273157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13196021271753202158848771 19794031907629803238273157)
    ·
      refine ⟨3711380982680588107176217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19794031907629803238273157 3711380982680588107176217)
      ·
        refine ⟨2783535737010441080382163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3711380982680588107176217 2783535737010441080382163)
        ·
          refine ⟨4175303605515661620573245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2783535737010441080382163 4175303605515661620573245)
          ·
            refine ⟨1565738852068373107714967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4175303605515661620573245 1565738852068373107714967)
            ·
              refine ⟨2348608278102559661572451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1565738852068373107714967 2348608278102559661572451)
              ·
                refine ⟨3522912417153839492358677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2348608278102559661572451 3522912417153839492358677)
                ·
                  refine ⟨165136519554086226204313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3522912417153839492358677 165136519554086226204313)
                  ·
                    rfl

theorem cell22_1447210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 6].length) (baseStart_1447210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1447210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1447210 prefixEnd_1447210 := by exact prefixLift 1447210
  have htrace : WordTrace (prefixWord ++ tailWord_1447210) baseStart_1447210 baseEnd_1447210 := by
    simpa [prefixWord, tailWord_1447210, baseEnd_1447210] using wordTrace_append hprefix tailTrace_1447210
  have hstable : (prefixWord ++ tailWord_1447210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447210).length < 2 ^ (prefixWord ++ tailWord_1447210).sum := by decide
  have hdescent : baseEnd_1447210 < baseStart_1447210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447221 : List Nat := [1, 3, 3, 1, 2, 2, 1, 9]
def baseStart_1447221 : Nat := 118140960795 + 1447221 * 2 ^ 59
def prefixEnd_1447221 : Nat := 4983230072969 + 3 ^ 40 * 1447221 * 2
def baseEnd_1447221 : Nat := 55045924909673146287545

theorem tailTrace_1447221 : CollatzResearch.WordTrace tailWord_1447221 prefixEnd_1447221 55045924909673146287545 := by
  unfold tailWord_1447221
  simp only [CollatzResearch.WordTrace]
  refine ⟨52784486289972957514045517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35189657526648638342697011 52784486289972957514045517)
  ·
    refine ⟨19794182358739859067767069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52784486289972957514045517 19794182358739859067767069)
    ·
      refine ⟨7422818384527447150412651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19794182358739859067767069 7422818384527447150412651)
      ·
        refine ⟨11134227576791170725618977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7422818384527447150412651 11134227576791170725618977)
        ·
          refine ⟨8350670682593378044214233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11134227576791170725618977 8350670682593378044214233)
          ·
            refine ⟨6263003011945033533160675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8350670682593378044214233 6263003011945033533160675)
            ·
              refine ⟨9394504517917550299741013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6263003011945033533160675 9394504517917550299741013)
              ·
                refine ⟨55045924909673146287545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9394504517917550299741013 55045924909673146287545)
                ·
                  rfl

theorem cell22_1447221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 9].length) (baseStart_1447221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1447221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1447221 prefixEnd_1447221 := by exact prefixLift 1447221
  have htrace : WordTrace (prefixWord ++ tailWord_1447221) baseStart_1447221 baseEnd_1447221 := by
    simpa [prefixWord, tailWord_1447221, baseEnd_1447221] using wordTrace_append hprefix tailTrace_1447221
  have hstable : (prefixWord ++ tailWord_1447221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447221).length < 2 ^ (prefixWord ++ tailWord_1447221).sum := by decide
  have hdescent : baseEnd_1447221 < baseStart_1447221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447229 : List Nat := [1, 4, 1, 5, 2, 1, 1, 2, 1, 4]
def baseStart_1447229 : Nat := 118140960795 + 1447229 * 2 ^ 59
def prefixEnd_1447229 : Nat := 4983230072969 + 3 ^ 40 * 1447229 * 2
def baseEnd_1447229 : Nat := 495416062750548962387881

theorem tailTrace_1447229 : CollatzResearch.WordTrace tailWord_1447229 prefixEnd_1447229 495416062750548962387881 := by
  unfold tailWord_1447229
  simp only [CollatzResearch.WordTrace]
  refine ⟨52784778073943974880336741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35189852049295983253557827 52784778073943974880336741)
  ·
    refine ⟨9897145888864495290063139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52784778073943974880336741 9897145888864495290063139)
    ·
      refine ⟨14845718833296742935094709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9897145888864495290063139 14845718833296742935094709)
      ·
        refine ⟨1391786140621569650165129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14845718833296742935094709 1391786140621569650165129)
        ·
          refine ⟨1043839605466177237623847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1391786140621569650165129 1043839605466177237623847)
          ·
            refine ⟨1565759408199265856435771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043839605466177237623847 1565759408199265856435771)
            ·
              refine ⟨2348639112298898784653657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1565759408199265856435771 2348639112298898784653657)
              ·
                refine ⟨1761479334224174088490243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2348639112298898784653657 1761479334224174088490243)
                ·
                  refine ⟨2642219001336261132735365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1761479334224174088490243 2642219001336261132735365)
                  ·
                    refine ⟨495416062750548962387881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2642219001336261132735365 495416062750548962387881)
                    ·
                      rfl

theorem cell22_1447229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_1447229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1447229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1447229 prefixEnd_1447229 := by exact prefixLift 1447229
  have htrace : WordTrace (prefixWord ++ tailWord_1447229) baseStart_1447229 baseEnd_1447229 := by
    simpa [prefixWord, tailWord_1447229, baseEnd_1447229] using wordTrace_append hprefix tailTrace_1447229
  have hstable : (prefixWord ++ tailWord_1447229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447229).length < 2 ^ (prefixWord ++ tailWord_1447229).sum := by decide
  have hdescent : baseEnd_1447229 < baseStart_1447229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447281 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 1, 7]
def baseStart_1447281 : Nat := 118140960795 + 1447281 * 2 ^ 59
def prefixEnd_1447281 : Nat := 4983230072969 + 3 ^ 40 * 1447281 * 2
def baseEnd_1447281 : Nat := 495433863413238160087721

theorem tailTrace_1447281 : CollatzResearch.WordTrace tailWord_1447281 prefixEnd_1447281 495433863413238160087721 := by
  unfold tailWord_1447281
  simp only [CollatzResearch.WordTrace]
  refine ⟨52786674669755587761229697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35191116446503725174153131 52786674669755587761229697)
  ·
    refine ⟨39590006002316690820922273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52786674669755587761229697 39590006002316690820922273)
    ·
      refine ⟨29692504501737518115691705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39590006002316690820922273 29692504501737518115691705)
      ·
        refine ⟨22269378376303138586768779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29692504501737518115691705 22269378376303138586768779)
        ·
          refine ⟨33404067564454707880153169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22269378376303138586768779 33404067564454707880153169)
          ·
            refine ⟨25053050673341030910114877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33404067564454707880153169 25053050673341030910114877)
            ·
              refine ⟨9394894002502886591293079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25053050673341030910114877 9394894002502886591293079)
              ·
                refine ⟨14092341003754329886939619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9394894002502886591293079 14092341003754329886939619)
                ·
                  refine ⟨21138511505631494830409429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14092341003754329886939619 21138511505631494830409429)
                  ·
                    refine ⟨495433863413238160087721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21138511505631494830409429 495433863413238160087721)
                    ·
                      rfl

theorem cell22_1447281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_1447281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1447281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1447281 prefixEnd_1447281 := by exact prefixLift 1447281
  have htrace : WordTrace (prefixWord ++ tailWord_1447281) baseStart_1447281 baseEnd_1447281 := by
    simpa [prefixWord, tailWord_1447281, baseEnd_1447281] using wordTrace_append hprefix tailTrace_1447281
  have hstable : (prefixWord ++ tailWord_1447281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447281).length < 2 ^ (prefixWord ++ tailWord_1447281).sum := by decide
  have hdescent : baseEnd_1447281 < baseStart_1447281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447313 : List Nat := [1, 2, 2, 1, 1, 1, 2, 7, 1, 4]
def baseStart_1447313 : Nat := 118140960795 + 1447313 * 2 ^ 59
def prefixEnd_1447313 : Nat := 4983230072969 + 3 ^ 40 * 1447313 * 2
def baseEnd_1447313 : Nat := 495444817667200743287623

theorem tailTrace_1447313 : CollatzResearch.WordTrace tailWord_1447313 prefixEnd_1447313 495444817667200743287623 := by
  unfold tailWord_1447313
  simp only [CollatzResearch.WordTrace]
  refine ⟨52787841805639657226394593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35191894537093104817596395 52787841805639657226394593)
  ·
    refine ⟨39590881354229742919795945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52787841805639657226394593 39590881354229742919795945)
    ·
      refine ⟨29693161015672307189846959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39590881354229742919795945 29693161015672307189846959)
      ·
        refine ⟨44539741523508460784770439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29693161015672307189846959 44539741523508460784770439)
        ·
          refine ⟨66809612285262691177155659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44539741523508460784770439 66809612285262691177155659)
          ·
            refine ⟨100214418427894036765733489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66809612285262691177155659 100214418427894036765733489)
            ·
              refine ⟨75160813820920527574300117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100214418427894036765733489 75160813820920527574300117)
              ·
                refine ⟨1761581573927824865022659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 75160813820920527574300117 1761581573927824865022659)
                ·
                  refine ⟨2642372360891737297533989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1761581573927824865022659 2642372360891737297533989)
                  ·
                    refine ⟨495444817667200743287623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2642372360891737297533989 495444817667200743287623)
                    ·
                      rfl

theorem cell22_1447313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_1447313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1447313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1447313 prefixEnd_1447313 := by exact prefixLift 1447313
  have htrace : WordTrace (prefixWord ++ tailWord_1447313) baseStart_1447313 baseEnd_1447313 := by
    simpa [prefixWord, tailWord_1447313, baseEnd_1447313] using wordTrace_append hprefix tailTrace_1447313
  have hstable : (prefixWord ++ tailWord_1447313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447313).length < 2 ^ (prefixWord ++ tailWord_1447313).sum := by decide
  have hdescent : baseEnd_1447313 < baseStart_1447313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447328 : List Nat := [2, 1, 1, 4, 1, 2, 4, 1, 6]
def baseStart_1447328 : Nat := 118140960795 + 1447328 * 2 ^ 59
def prefixEnd_1447328 : Nat := 4983230072969 + 3 ^ 40 * 1447328 * 2
def baseEnd_1447328 : Nat := 165149984157915234720859

theorem tailTrace_1447328 : CollatzResearch.WordTrace tailWord_1447328 prefixEnd_1447328 165149984157915234720859 := by
  unfold tailWord_1447328
  simp only [CollatzResearch.WordTrace]
  refine ⟨26394194450292657394095319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35192259267056876525460425 26394194450292657394095319)
  ·
    refine ⟨39591291675438986091142979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26394194450292657394095319 39591291675438986091142979)
    ·
      refine ⟨59386937513158479136714469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39591291675438986091142979 59386937513158479136714469)
      ·
        refine ⟨11135050783717214838133963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59386937513158479136714469 11135050783717214838133963)
        ·
          refine ⟨16702576175575822257200945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11135050783717214838133963 16702576175575822257200945)
          ·
            refine ⟨12526932131681866692900709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16702576175575822257200945 12526932131681866692900709)
            ·
              refine ⟨2348799774690350004918883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12526932131681866692900709 2348799774690350004918883)
              ·
                refine ⟨3523199662035525007378325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2348799774690350004918883 3523199662035525007378325)
                ·
                  refine ⟨165149984157915234720859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3523199662035525007378325 165149984157915234720859)
                  ·
                    rfl

theorem cell22_1447328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 6].length) (baseStart_1447328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1447328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1447328 prefixEnd_1447328 := by exact prefixLift 1447328
  have htrace : WordTrace (prefixWord ++ tailWord_1447328) baseStart_1447328 baseEnd_1447328 := by
    simpa [prefixWord, tailWord_1447328, baseEnd_1447328] using wordTrace_append hprefix tailTrace_1447328
  have hstable : (prefixWord ++ tailWord_1447328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447328).length < 2 ^ (prefixWord ++ tailWord_1447328).sum := by decide
  have hdescent : baseEnd_1447328 < baseStart_1447328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447430 : List Nat := [6, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_1447430 : Nat := 118140960795 + 1447430 * 2 ^ 59
def prefixEnd_1447430 : Nat := 4983230072969 + 3 ^ 40 * 1447430 * 2
def baseEnd_1447430 : Nat := 165161623052750479370755

theorem tailTrace_1447430 : CollatzResearch.WordTrace tailWord_1447430 prefixEnd_1447430 165161623052750479370755 := by
  unfold tailWord_1447430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1649753410819243319012617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35194739430810524138935829 1649753410819243319012617)
  ·
    refine ⟨1237315058114432489259463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1649753410819243319012617 1237315058114432489259463)
    ·
      refine ⟨1855972587171648733889195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1237315058114432489259463 1855972587171648733889195)
      ·
        refine ⟨2783958880757473100833793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1855972587171648733889195 2783958880757473100833793)
        ·
          refine ⟨2087969160568104825625345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2783958880757473100833793 2087969160568104825625345)
          ·
            refine ⟨1565976870426078619219009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2087969160568104825625345 1565976870426078619219009)
            ·
              refine ⟨1174482652819558964414257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1565976870426078619219009 1174482652819558964414257)
              ·
                refine ⟨880861989614669223310693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1174482652819558964414257 880861989614669223310693)
                ·
                  refine ⟨165161623052750479370755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 880861989614669223310693 165161623052750479370755)
                  ·
                    rfl

theorem cell22_1447430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_1447430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1447430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1447430 prefixEnd_1447430 := by exact prefixLift 1447430
  have htrace : WordTrace (prefixWord ++ tailWord_1447430) baseStart_1447430 baseEnd_1447430 := by
    simpa [prefixWord, tailWord_1447430, baseEnd_1447430] using wordTrace_append hprefix tailTrace_1447430
  have hstable : (prefixWord ++ tailWord_1447430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447430).length < 2 ^ (prefixWord ++ tailWord_1447430).sum := by decide
  have hdescent : baseEnd_1447430 < baseStart_1447430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447433 : List Nat := [1, 2, 1, 1, 3, 1, 4, 2, 2, 5]
def baseStart_1447433 : Nat := 118140960795 + 1447433 * 2 ^ 59
def prefixEnd_1447433 : Nat := 4983230072969 + 3 ^ 40 * 1447433 * 2
def baseEnd_1447433 : Nat := 495485896119560430287255

theorem tailTrace_1447433 : CollatzResearch.WordTrace tailWord_1447433 prefixEnd_1447433 495485896119560430287255 := by
  unfold tailWord_1447433
  simp only [CollatzResearch.WordTrace]
  refine ⟨52792218565204917720762953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35194812376803278480508635 52792218565204917720762953)
  ·
    refine ⟨39594163923903688290572215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52792218565204917720762953 39594163923903688290572215)
    ·
      refine ⟨59391245885855532435858323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39594163923903688290572215 59391245885855532435858323)
      ·
        refine ⟨89086868828783298653787485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59391245885855532435858323 89086868828783298653787485)
        ·
          refine ⟨33407575810793736995170307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89086868828783298653787485 33407575810793736995170307)
          ·
            refine ⟨50111363716190605492755461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33407575810793736995170307 50111363716190605492755461)
            ·
              refine ⟨9395880696785738529891649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50111363716190605492755461 9395880696785738529891649)
              ·
                refine ⟨7046910522589303897418737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9395880696785738529891649 7046910522589303897418737)
                ·
                  refine ⟨5285182891941977923064053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7046910522589303897418737 5285182891941977923064053)
                  ·
                    refine ⟨495485896119560430287255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5285182891941977923064053 495485896119560430287255)
                    ·
                      rfl

theorem cell22_1447433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 5].length) (baseStart_1447433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1447433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1447433 prefixEnd_1447433 := by exact prefixLift 1447433
  have htrace : WordTrace (prefixWord ++ tailWord_1447433) baseStart_1447433 baseEnd_1447433 := by
    simpa [prefixWord, tailWord_1447433, baseEnd_1447433] using wordTrace_append hprefix tailTrace_1447433
  have hstable : (prefixWord ++ tailWord_1447433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447433).length < 2 ^ (prefixWord ++ tailWord_1447433).sum := by decide
  have hdescent : baseEnd_1447433 < baseStart_1447433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447525 : List Nat := [1, 3, 1, 3, 3, 2, 1, 8]
def baseStart_1447525 : Nat := 118140960795 + 1447525 * 2 ^ 59
def prefixEnd_1447525 : Nat := 4983230072969 + 3 ^ 40 * 1447525 * 2
def baseEnd_1447525 : Nat := 55057487733300317442997

theorem tailTrace_1447525 : CollatzResearch.WordTrace tailWord_1447525 prefixEnd_1447525 55057487733300317442997 := by
  unfold tailWord_1447525
  simp only [CollatzResearch.WordTrace]
  refine ⟨52795574080871617433112029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35197049387247744955408019 52795574080871617433112029)
  ·
    refine ⟨19798340280326856537417011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52795574080871617433112029 19798340280326856537417011)
    ·
      refine ⟨29697510420490284806125517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19798340280326856537417011 29697510420490284806125517)
      ·
        refine ⟨11136566407683856802297069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29697510420490284806125517 11136566407683856802297069)
        ·
          refine ⟨4176212402881446300861401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11136566407683856802297069 4176212402881446300861401)
          ·
            refine ⟨3132159302161084725646051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4176212402881446300861401 3132159302161084725646051)
            ·
              refine ⟨4698238953241627088469077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3132159302161084725646051 4698238953241627088469077)
              ·
                refine ⟨55057487733300317442997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4698238953241627088469077 55057487733300317442997)
                ·
                  rfl

theorem cell22_1447525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 8].length) (baseStart_1447525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1447525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1447525 prefixEnd_1447525 := by exact prefixLift 1447525
  have htrace : WordTrace (prefixWord ++ tailWord_1447525) baseStart_1447525 baseEnd_1447525 := by
    simpa [prefixWord, tailWord_1447525, baseEnd_1447525] using wordTrace_append hprefix tailTrace_1447525
  have hstable : (prefixWord ++ tailWord_1447525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447525).length < 2 ^ (prefixWord ++ tailWord_1447525).sum := by decide
  have hdescent : baseEnd_1447525 < baseStart_1447525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447542 : List Nat := [5, 1, 1, 2, 2, 3, 8]
def baseStart_1447542 : Nat := 118140960795 + 1447542 * 2 ^ 59
def prefixEnd_1447542 : Nat := 4983230072969 + 3 ^ 40 * 1447542 * 2
def baseEnd_1447542 : Nat := 18352711446189647381923

theorem tailTrace_1447542 : CollatzResearch.WordTrace tailWord_1447542 prefixEnd_1447542 18352711446189647381923 := by
  unfold tailWord_1447542
  simp only [CollatzResearch.WordTrace]
  refine ⟨3299762132613126833530055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35197462747873352890987253 3299762132613126833530055)
  ·
    refine ⟨4949643198919690250295083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3299762132613126833530055 4949643198919690250295083)
    ·
      refine ⟨7424464798379535375442625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4949643198919690250295083 7424464798379535375442625)
      ·
        refine ⟨5568348598784651531581969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7424464798379535375442625 5568348598784651531581969)
        ·
          refine ⟨4176261449088488648686477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5568348598784651531581969 4176261449088488648686477)
          ·
            refine ⟨1566098043408183243257429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4176261449088488648686477 1566098043408183243257429)
            ·
              refine ⟨18352711446189647381923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1566098043408183243257429 18352711446189647381923)
              ·
                rfl

theorem cell22_1447542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 8].length) (baseStart_1447542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1447542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1447542 prefixEnd_1447542 := by exact prefixLift 1447542
  have htrace : WordTrace (prefixWord ++ tailWord_1447542) baseStart_1447542 baseEnd_1447542 := by
    simpa [prefixWord, tailWord_1447542, baseEnd_1447542] using wordTrace_append hprefix tailTrace_1447542
  have hstable : (prefixWord ++ tailWord_1447542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447542).length < 2 ^ (prefixWord ++ tailWord_1447542).sum := by decide
  have hdescent : baseEnd_1447542 < baseStart_1447542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447615 : List Nat := [1, 1, 2, 2, 2, 3, 2, 3, 6]
def baseStart_1447615 : Nat := 118140960795 + 1447615 * 2 ^ 59
def prefixEnd_1447615 : Nat := 4983230072969 + 3 ^ 40 * 1447615 * 2
def baseEnd_1447615 : Nat := 165182732812990874078899

theorem tailTrace_1447615 : CollatzResearch.WordTrace tailWord_1447615 prefixEnd_1447615 165182732812990874078899 := by
  unfold tailWord_1447615
  simp only [CollatzResearch.WordTrace]
  refine ⟨52798856650545562803888299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35199237767030375202592199 52798856650545562803888299)
  ·
    refine ⟨79198284975818344205832449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52798856650545562803888299 79198284975818344205832449)
    ·
      refine ⟨59398713731863758154374337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79198284975818344205832449 59398713731863758154374337)
      ·
        refine ⟨44549035298897818615780753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59398713731863758154374337 44549035298897818615780753)
        ·
          refine ⟨33411776474173363961835565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44549035298897818615780753 33411776474173363961835565)
          ·
            refine ⟨12529416177815011485688337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33411776474173363961835565 12529416177815011485688337)
            ·
              refine ⟨9397062133361258614266253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12529416177815011485688337 9397062133361258614266253)
              ·
                refine ⟨3523898300010471980349845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9397062133361258614266253 3523898300010471980349845)
                ·
                  refine ⟨165182732812990874078899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3523898300010471980349845 165182732812990874078899)
                  ·
                    rfl

theorem cell22_1447615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 6].length) (baseStart_1447615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1447615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1447615 prefixEnd_1447615 := by exact prefixLift 1447615
  have htrace : WordTrace (prefixWord ++ tailWord_1447615) baseStart_1447615 baseEnd_1447615 := by
    simpa [prefixWord, tailWord_1447615, baseEnd_1447615] using wordTrace_append hprefix tailTrace_1447615
  have hstable : (prefixWord ++ tailWord_1447615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447615).length < 2 ^ (prefixWord ++ tailWord_1447615).sum := by decide
  have hdescent : baseEnd_1447615 < baseStart_1447615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447647 : List Nat := [1, 1, 2, 3, 2, 2, 2, 2, 4, 3]
def baseStart_1447647 : Nat := 118140960795 + 1447647 * 2 ^ 59
def prefixEnd_1447647 : Nat := 4983230072969 + 3 ^ 40 * 1447647 * 2
def baseEnd_1447647 : Nat := 495559152692935205436599

theorem tailTrace_1447647 : CollatzResearch.WordTrace tailWord_1447647 prefixEnd_1447647 495559152692935205436599 := by
  unfold tailWord_1447647
  simp only [CollatzResearch.WordTrace]
  refine ⟨52800023786429632269053195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35200015857619754846035463 52800023786429632269053195)
  ·
    refine ⟨79200035679644448403579793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52800023786429632269053195 79200035679644448403579793)
    ·
      refine ⟨59400026759733336302684845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79200035679644448403579793 59400026759733336302684845)
      ·
        refine ⟨22275010034900001113506817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59400026759733336302684845 22275010034900001113506817)
        ·
          refine ⟨16706257526175000835130113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22275010034900001113506817 16706257526175000835130113)
          ·
            refine ⟨12529693144631250626347585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16706257526175000835130113 12529693144631250626347585)
            ·
              refine ⟨9397269858473437969760689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12529693144631250626347585 9397269858473437969760689)
              ·
                refine ⟨7047952393855078477320517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9397269858473437969760689 7047952393855078477320517)
                ·
                  refine ⟨1321491073847827214497597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7047952393855078477320517 1321491073847827214497597)
                  ·
                    refine ⟨495559152692935205436599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1321491073847827214497597 495559152692935205436599)
                    ·
                      rfl

theorem cell22_1447647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4, 3].length) (baseStart_1447647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1447647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1447647 prefixEnd_1447647 := by exact prefixLift 1447647
  have htrace : WordTrace (prefixWord ++ tailWord_1447647) baseStart_1447647 baseEnd_1447647 := by
    simpa [prefixWord, tailWord_1447647, baseEnd_1447647] using wordTrace_append hprefix tailTrace_1447647
  have hstable : (prefixWord ++ tailWord_1447647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447647).length < 2 ^ (prefixWord ++ tailWord_1447647).sum := by decide
  have hdescent : baseEnd_1447647 < baseStart_1447647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447662 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 4, 4]
def baseStart_1447662 : Nat := 118140960795 + 1447662 * 2 ^ 59
def prefixEnd_1447662 : Nat := 4983230072969 + 3 ^ 40 * 1447662 * 2
def baseEnd_1447662 : Nat := 495564287499480166311553

theorem tailTrace_1447662 : CollatzResearch.WordTrace tailWord_1447662 prefixEnd_1447662 495564287499480166311553 := by
  unfold tailWord_1447662
  simp only [CollatzResearch.WordTrace]
  refine ⟨6600071360171911228856155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35200380587583526553899493 6600071360171911228856155)
  ·
    refine ⟨9900107040257866843284233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6600071360171911228856155 9900107040257866843284233)
    ·
      refine ⟨7425080280193400132463175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9900107040257866843284233 7425080280193400132463175)
      ·
        refine ⟨11137620420290100198694763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7425080280193400132463175 11137620420290100198694763)
        ·
          refine ⟨16706430630435150298042145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11137620420290100198694763 16706430630435150298042145)
          ·
            refine ⟨12529822972826362723531609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16706430630435150298042145 12529822972826362723531609)
            ·
              refine ⟨9397367229619772042648707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12529822972826362723531609 9397367229619772042648707)
              ·
                refine ⟨14096050844429658063973061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9397367229619772042648707 14096050844429658063973061)
                ·
                  refine ⟨2643009533330560886994949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14096050844429658063973061 2643009533330560886994949)
                  ·
                    refine ⟨495564287499480166311553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2643009533330560886994949 495564287499480166311553)
                    ·
                      rfl

theorem cell22_1447662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_1447662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1447662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1447662 prefixEnd_1447662 := by exact prefixLift 1447662
  have htrace : WordTrace (prefixWord ++ tailWord_1447662) baseStart_1447662 baseEnd_1447662 := by
    simpa [prefixWord, tailWord_1447662, baseEnd_1447662] using wordTrace_append hprefix tailTrace_1447662
  have hstable : (prefixWord ++ tailWord_1447662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447662).length < 2 ^ (prefixWord ++ tailWord_1447662).sum := by decide
  have hdescent : baseEnd_1447662 < baseStart_1447662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447812 : List Nat := [2, 3, 2, 1, 1, 1, 2, 10]
def baseStart_1447812 : Nat := 118140960795 + 1447812 * 2 ^ 59
def prefixEnd_1447812 : Nat := 4983230072969 + 3 ^ 40 * 1447812 * 2
def baseEnd_1447812 : Nat := 55068403951658863895677

theorem tailTrace_1447812 : CollatzResearch.WordTrace tailWord_1447812 prefixEnd_1447812 55068403951658863895677 := by
  unfold tailWord_1447812
  simp only [CollatzResearch.WordTrace]
  refine ⟨26403020915415932724404845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35204027887221243632539793 26403020915415932724404845)
  ·
    refine ⟨9901132843280974771651817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26403020915415932724404845 9901132843280974771651817)
    ·
      refine ⟨7425849632460731078738863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9901132843280974771651817 7425849632460731078738863)
      ·
        refine ⟨11138774448691096618108295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7425849632460731078738863 11138774448691096618108295)
        ·
          refine ⟨16708161673036644927162443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11138774448691096618108295 16708161673036644927162443)
          ·
            refine ⟨25062242509554967390743665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16708161673036644927162443 25062242509554967390743665)
            ·
              refine ⟨18796681882166225543057749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25062242509554967390743665 18796681882166225543057749)
              ·
                refine ⟨55068403951658863895677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18796681882166225543057749 55068403951658863895677)
                ·
                  rfl

theorem cell22_1447812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 10].length) (baseStart_1447812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1447812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1447812 prefixEnd_1447812 := by exact prefixLift 1447812
  have htrace : WordTrace (prefixWord ++ tailWord_1447812) baseStart_1447812 baseEnd_1447812 := by
    simpa [prefixWord, tailWord_1447812, baseEnd_1447812] using wordTrace_append hprefix tailTrace_1447812
  have hstable : (prefixWord ++ tailWord_1447812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447812).length < 2 ^ (prefixWord ++ tailWord_1447812).sum := by decide
  have hdescent : baseEnd_1447812 < baseStart_1447812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447818 : List Nat := [3, 1, 2, 4, 2, 1, 2, 3, 4]
def baseStart_1447818 : Nat := 118140960795 + 1447818 * 2 ^ 59
def prefixEnd_1447818 : Nat := 4983230072969 + 3 ^ 40 * 1447818 * 2
def baseEnd_1447818 : Nat := 165205896495849253137025

theorem tailTrace_1447818 : CollatzResearch.WordTrace tailWord_1447818 prefixEnd_1447818 165205896495849253137025 := by
  unfold tailWord_1447818
  simp only [CollatzResearch.WordTrace]
  refine ⟨13201565167202532118382027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35204173779206752315685405 13201565167202532118382027)
  ·
    refine ⟨19802347750803798177573041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13201565167202532118382027 19802347750803798177573041)
    ·
      refine ⟨14851760813102848633179781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19802347750803798177573041 14851760813102848633179781)
      ·
        refine ⟨2784705152456784118721209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14851760813102848633179781 2784705152456784118721209)
        ·
          refine ⟨2088528864342588089040907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2784705152456784118721209 2088528864342588089040907)
          ·
            refine ⟨3132793296513882133561361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2088528864342588089040907 3132793296513882133561361)
            ·
              refine ⟨2349594972385411600171021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3132793296513882133561361 2349594972385411600171021)
              ·
                refine ⟨881098114644529350064133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2349594972385411600171021 881098114644529350064133)
                ·
                  refine ⟨165205896495849253137025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 881098114644529350064133 165205896495849253137025)
                  ·
                    rfl

theorem cell22_1447818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3, 4].length) (baseStart_1447818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1447818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1447818 prefixEnd_1447818 := by exact prefixLift 1447818
  have htrace : WordTrace (prefixWord ++ tailWord_1447818) baseStart_1447818 baseEnd_1447818 := by
    simpa [prefixWord, tailWord_1447818, baseEnd_1447818] using wordTrace_append hprefix tailTrace_1447818
  have hstable : (prefixWord ++ tailWord_1447818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447818).length < 2 ^ (prefixWord ++ tailWord_1447818).sum := by decide
  have hdescent : baseEnd_1447818 < baseStart_1447818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447861 : List Nat := [1, 3, 3, 2, 1, 2, 2, 2, 3, 3]
def baseStart_1447861 : Nat := 118140960795 + 1447861 * 2 ^ 59
def prefixEnd_1447861 : Nat := 4983230072969 + 3 ^ 40 * 1447861 * 2
def baseEnd_1447861 : Nat := 495632409266309980585943

theorem tailTrace_1447861 : CollatzResearch.WordTrace tailWord_1447861 prefixEnd_1447861 495632409266309980585943 := by
  unfold tailWord_1447861
  simp only [CollatzResearch.WordTrace]
  refine ⟨52807829007654346817343437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35205219338436231211562291 52807829007654346817343437)
  ·
    refine ⟨19802935877870380056503789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52807829007654346817343437 19802935877870380056503789)
    ·
      refine ⟨7426100954201392521188921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19802935877870380056503789 7426100954201392521188921)
      ·
        refine ⟨5569575715651044390891691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7426100954201392521188921 5569575715651044390891691)
        ·
          refine ⟨8354363573476566586337537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5569575715651044390891691 8354363573476566586337537)
          ·
            refine ⟨6265772680107424939753153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8354363573476566586337537 6265772680107424939753153)
            ·
              refine ⟨4699329510080568704814865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6265772680107424939753153 4699329510080568704814865)
              ·
                refine ⟨3524497132560426528611149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4699329510080568704814865 3524497132560426528611149)
                ·
                  refine ⟨1321686424710159948229181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3524497132560426528611149 1321686424710159948229181)
                  ·
                    refine ⟨495632409266309980585943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1321686424710159948229181 495632409266309980585943)
                    ·
                      rfl

theorem cell22_1447861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_1447861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1447861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1447861 prefixEnd_1447861 := by exact prefixLift 1447861
  have htrace : WordTrace (prefixWord ++ tailWord_1447861) baseStart_1447861 baseEnd_1447861 := by
    simpa [prefixWord, tailWord_1447861, baseEnd_1447861] using wordTrace_append hprefix tailTrace_1447861
  have hstable : (prefixWord ++ tailWord_1447861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447861).length < 2 ^ (prefixWord ++ tailWord_1447861).sum := by decide
  have hdescent : baseEnd_1447861 < baseStart_1447861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447921 : List Nat := [1, 2, 2, 2, 5, 1, 1, 1, 3, 4]
def baseStart_1447921 : Nat := 118140960795 + 1447921 * 2 ^ 59
def prefixEnd_1447921 : Nat := 4983230072969 + 3 ^ 40 * 1447921 * 2
def baseEnd_1447921 : Nat := 495652948492489824085759

theorem tailTrace_1447921 : CollatzResearch.WordTrace tailWord_1447921 prefixEnd_1447921 495652948492489824085759 := by
  unfold tailWord_1447921
  simp only [CollatzResearch.WordTrace]
  refine ⟨52810017387436977064527617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35206678258291318043018411 52810017387436977064527617)
  ·
    refine ⟨39607513040577732798395713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52810017387436977064527617 39607513040577732798395713)
    ·
      refine ⟨29705634780433299598796785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39607513040577732798395713 29705634780433299598796785)
      ·
        refine ⟨22279226085324974699097589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29705634780433299598796785 22279226085324974699097589)
        ·
          refine ⟨2088677445499216378040399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22279226085324974699097589 2088677445499216378040399)
          ·
            refine ⟨3133016168248824567060599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2088677445499216378040399 3133016168248824567060599)
            ·
              refine ⟨4699524252373236850590899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3133016168248824567060599 4699524252373236850590899)
              ·
                refine ⟨7049286378559855275886349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4699524252373236850590899 7049286378559855275886349)
                ·
                  refine ⟨2643482391959945728457381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7049286378559855275886349 2643482391959945728457381)
                  ·
                    refine ⟨495652948492489824085759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2643482391959945728457381 495652948492489824085759)
                    ·
                      rfl

theorem cell22_1447921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_1447921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1447921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1447921 prefixEnd_1447921 := by exact prefixLift 1447921
  have htrace : WordTrace (prefixWord ++ tailWord_1447921) baseStart_1447921 baseEnd_1447921 := by
    simpa [prefixWord, tailWord_1447921, baseEnd_1447921] using wordTrace_append hprefix tailTrace_1447921
  have hstable : (prefixWord ++ tailWord_1447921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447921).length < 2 ^ (prefixWord ++ tailWord_1447921).sum := by decide
  have hdescent : baseEnd_1447921 < baseStart_1447921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447996 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 5, 3]
def baseStart_1447996 : Nat := 118140960795 + 1447996 * 2 ^ 59
def prefixEnd_1447996 : Nat := 4983230072969 + 3 ^ 40 * 1447996 * 2
def baseEnd_1447996 : Nat := 495678622525214628460529

theorem tailTrace_1447996 : CollatzResearch.WordTrace tailWord_1447996 prefixEnd_1447996 495678622525214628460529 := by
  unfold tailWord_1447996
  simp only [CollatzResearch.WordTrace]
  refine ⟨26406376431082632436753921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35208501908110176582338561 26406376431082632436753921)
  ·
    refine ⟨19804782323311974327565441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26406376431082632436753921 19804782323311974327565441)
    ·
      refine ⟨14853586742483980745674081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19804782323311974327565441 14853586742483980745674081)
      ·
        refine ⟨11140190056862985559255561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14853586742483980745674081 11140190056862985559255561)
        ·
          refine ⟨8355142542647239169441671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11140190056862985559255561 8355142542647239169441671)
          ·
            refine ⟨12532713813970858754162507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8355142542647239169441671 12532713813970858754162507)
            ·
              refine ⟨18799070720956288131243761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12532713813970858754162507 18799070720956288131243761)
              ·
                refine ⟨14099303040717216098432821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18799070720956288131243761 14099303040717216098432821)
                ·
                  refine ⟨1321809660067239009228077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14099303040717216098432821 1321809660067239009228077)
                  ·
                    refine ⟨495678622525214628460529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1321809660067239009228077 495678622525214628460529)
                    ·
                      rfl

theorem cell22_1447996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_1447996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1447996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1447996 prefixEnd_1447996 := by exact prefixLift 1447996
  have htrace : WordTrace (prefixWord ++ tailWord_1447996) baseStart_1447996 baseEnd_1447996 := by
    simpa [prefixWord, tailWord_1447996, baseEnd_1447996] using wordTrace_append hprefix tailTrace_1447996
  have hstable : (prefixWord ++ tailWord_1447996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447996).length < 2 ^ (prefixWord ++ tailWord_1447996).sum := by decide
  have hdescent : baseEnd_1447996 < baseStart_1447996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448009 : List Nat := [1, 2, 1, 1, 2, 2, 5, 1, 7]
def baseStart_1448009 : Nat := 118140960795 + 1448009 * 2 ^ 59
def prefixEnd_1448009 : Nat := 4983230072969 + 3 ^ 40 * 1448009 * 2
def baseEnd_1448009 : Nat := 165227690896962309295163

theorem tailTrace_1448009 : CollatzResearch.WordTrace tailWord_1448009 prefixEnd_1448009 165227690896962309295163 := by
  unfold tailWord_1448009
  simp only [CollatzResearch.WordTrace]
  refine ⟨52813227011118168093731081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35208818007412112062487387 52813227011118168093731081)
  ·
    refine ⟨39609920258338626070298311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52813227011118168093731081 39609920258338626070298311)
    ·
      refine ⟨59414880387507939105447467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39609920258338626070298311 59414880387507939105447467)
      ·
        refine ⟨89122320581261908658171201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59414880387507939105447467 89122320581261908658171201)
        ·
          refine ⟨66841740435946431493628401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89122320581261908658171201 66841740435946431493628401)
          ·
            refine ⟨50131305326959823620221301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66841740435946431493628401 50131305326959823620221301)
            ·
              refine ⟨4699809874402483464395747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50131305326959823620221301 4699809874402483464395747)
              ·
                refine ⟨7049714811603725196593621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4699809874402483464395747 7049714811603725196593621)
                ·
                  refine ⟨165227690896962309295163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7049714811603725196593621 165227690896962309295163)
                  ·
                    rfl

theorem cell22_1448009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 7].length) (baseStart_1448009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448009 prefixEnd_1448009 := by exact prefixLift 1448009
  have htrace : WordTrace (prefixWord ++ tailWord_1448009) baseStart_1448009 baseEnd_1448009 := by
    simpa [prefixWord, tailWord_1448009, baseEnd_1448009] using wordTrace_append hprefix tailTrace_1448009
  have hstable : (prefixWord ++ tailWord_1448009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448009).length < 2 ^ (prefixWord ++ tailWord_1448009).sum := by decide
  have hdescent : baseEnd_1448009 < baseStart_1448009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448071 : List Nat := [1, 1, 4, 2, 1, 1, 5, 1, 6]
def baseStart_1448071 : Nat := 118140960795 + 1448071 * 2 ^ 59
def prefixEnd_1448071 : Nat := 4983230072969 + 3 ^ 40 * 1448071 * 2
def baseEnd_1448071 : Nat := 165234765519313144278433

theorem tailTrace_1448071 : CollatzResearch.WordTrace tailWord_1448071 prefixEnd_1448071 165234765519313144278433 := by
  unfold tailWord_1448071
  simp only [CollatzResearch.WordTrace]
  refine ⟨52815488336893552682488067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35210325557929035121658711 52815488336893552682488067)
  ·
    refine ⟨79223232505340329023732101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52815488336893552682488067 79223232505340329023732101)
    ·
      refine ⟨14854356094751311691949769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79223232505340329023732101 14854356094751311691949769)
      ·
        refine ⟨11140767071063483768962327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14854356094751311691949769 11140767071063483768962327)
        ·
          refine ⟨16711150606595225653443491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11140767071063483768962327 16711150606595225653443491)
          ·
            refine ⟨25066725909892838480165237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16711150606595225653443491 25066725909892838480165237)
            ·
              refine ⟨2350005554052453607515491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25066725909892838480165237 2350005554052453607515491)
              ·
                refine ⟨3525008331078680411273237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2350005554052453607515491 3525008331078680411273237)
                ·
                  refine ⟨165234765519313144278433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3525008331078680411273237 165234765519313144278433)
                  ·
                    rfl

theorem cell22_1448071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 6].length) (baseStart_1448071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448071 prefixEnd_1448071 := by exact prefixLift 1448071
  have htrace : WordTrace (prefixWord ++ tailWord_1448071) baseStart_1448071 baseEnd_1448071 := by
    simpa [prefixWord, tailWord_1448071, baseEnd_1448071] using wordTrace_append hprefix tailTrace_1448071
  have hstable : (prefixWord ++ tailWord_1448071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448071).length < 2 ^ (prefixWord ++ tailWord_1448071).sum := by decide
  have hdescent : baseEnd_1448071 < baseStart_1448071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448161 : List Nat := [1, 2, 3, 1, 3, 1, 2, 2, 7]
def baseStart_1448161 : Nat := 118140960795 + 1448161 * 2 ^ 59
def prefixEnd_1448161 : Nat := 4983230072969 + 3 ^ 40 * 1448161 * 2
def baseEnd_1448161 : Nat := 165245035132403066028341

theorem tailTrace_1448161 : CollatzResearch.WordTrace tailWord_1448161 prefixEnd_1448161 165245035132403066028341 := by
  unfold tailWord_1448161
  simp only [CollatzResearch.WordTrace]
  refine ⟨52818770906567498053264337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35212513937711665368842891 52818770906567498053264337)
  ·
    refine ⟨39614078179925623539948253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52818770906567498053264337 39614078179925623539948253)
    ·
      refine ⟨14855279317472108827480595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39614078179925623539948253 14855279317472108827480595)
      ·
        refine ⟨22282918976208163241220893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14855279317472108827480595 22282918976208163241220893)
        ·
          refine ⟨8356094616078061215457835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22282918976208163241220893 8356094616078061215457835)
          ·
            refine ⟨12534141924117091823186753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8356094616078061215457835 12534141924117091823186753)
            ·
              refine ⟨9400606443087818867390065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12534141924117091823186753 9400606443087818867390065)
              ·
                refine ⟨7050454832315864150542549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9400606443087818867390065 7050454832315864150542549)
                ·
                  refine ⟨165245035132403066028341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7050454832315864150542549 165245035132403066028341)
                  ·
                    rfl

theorem cell22_1448161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 7].length) (baseStart_1448161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448161 prefixEnd_1448161 := by exact prefixLift 1448161
  have htrace : WordTrace (prefixWord ++ tailWord_1448161) baseStart_1448161 baseEnd_1448161 := by
    simpa [prefixWord, tailWord_1448161, baseEnd_1448161] using wordTrace_append hprefix tailTrace_1448161
  have hstable : (prefixWord ++ tailWord_1448161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448161).length < 2 ^ (prefixWord ++ tailWord_1448161).sum := by decide
  have hdescent : baseEnd_1448161 < baseStart_1448161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448178 : List Nat := [3, 2, 1, 3, 2, 2, 1, 1, 7]
def baseStart_1448178 : Nat := 118140960795 + 1448178 * 2 ^ 59
def prefixEnd_1448178 : Nat := 4983230072969 + 3 ^ 40 * 1448178 * 2
def baseEnd_1448178 : Nat := 165246974948208940136657

theorem tailTrace_1448178 : CollatzResearch.WordTrace tailWord_1448178 prefixEnd_1448178 165246974948208940136657 := by
  unfold tailWord_1448178
  simp only [CollatzResearch.WordTrace]
  refine ⟨13204847736876477489158297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35212927298337273304422125 13204847736876477489158297)
  ·
    refine ⟨9903635802657358116868723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13204847736876477489158297 9903635802657358116868723)
    ·
      refine ⟨14855453703986037175303085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9903635802657358116868723 14855453703986037175303085)
      ·
        refine ⟨5570795138994763940738657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14855453703986037175303085 5570795138994763940738657)
        ·
          refine ⟨4178096354246072955553993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5570795138994763940738657 4178096354246072955553993)
          ·
            refine ⟨3133572265684554716665495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4178096354246072955553993 3133572265684554716665495)
            ·
              refine ⟨4700358398526832074998243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3133572265684554716665495 4700358398526832074998243)
              ·
                refine ⟨7050537597790248112497365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4700358398526832074998243 7050537597790248112497365)
                ·
                  refine ⟨165246974948208940136657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7050537597790248112497365 165246974948208940136657)
                  ·
                    rfl

theorem cell22_1448178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_1448178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448178 prefixEnd_1448178 := by exact prefixLift 1448178
  have htrace : WordTrace (prefixWord ++ tailWord_1448178) baseStart_1448178 baseEnd_1448178 := by
    simpa [prefixWord, tailWord_1448178, baseEnd_1448178] using wordTrace_append hprefix tailTrace_1448178
  have hstable : (prefixWord ++ tailWord_1448178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448178).length < 2 ^ (prefixWord ++ tailWord_1448178).sum := by decide
  have hdescent : baseEnd_1448178 < baseStart_1448178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448182 : List Nat := [5, 1, 1, 1, 1, 1, 4, 4, 1, 3]
def baseStart_1448182 : Nat := 118140960795 + 1448182 * 2 ^ 59
def prefixEnd_1448182 : Nat := 4983230072969 + 3 ^ 40 * 1448182 * 2
def baseEnd_1448182 : Nat := 495742294126372143309959

theorem tailTrace_1448182 : CollatzResearch.WordTrace tailWord_1448182 prefixEnd_1448182 495742294126372143309959 := by
  unfold tailWord_1448182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3301221052468213664986175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35213024559660945759852533 3301221052468213664986175)
  ·
    refine ⟨4951831578702320497479263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3301221052468213664986175 4951831578702320497479263)
    ·
      refine ⟨7427747368053480746218895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4951831578702320497479263 7427747368053480746218895)
      ·
        refine ⟨11141621052080221119328343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7427747368053480746218895 11141621052080221119328343)
        ·
          refine ⟨16712431578120331678992515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11141621052080221119328343 16712431578120331678992515)
          ·
            refine ⟨25068647367180497518488773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16712431578120331678992515 25068647367180497518488773)
            ·
              refine ⟨4700371381346343284716645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25068647367180497518488773 4700371381346343284716645)
              ·
                refine ⟨881319634002439365884371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4700371381346343284716645 881319634002439365884371)
                ·
                  refine ⟨1321979451003659048826557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 881319634002439365884371 1321979451003659048826557)
                  ·
                    refine ⟨495742294126372143309959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1321979451003659048826557 495742294126372143309959)
                    ·
                      rfl

theorem cell22_1448182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_1448182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448182 prefixEnd_1448182 := by exact prefixLift 1448182
  have htrace : WordTrace (prefixWord ++ tailWord_1448182) baseStart_1448182 baseEnd_1448182 := by
    simpa [prefixWord, tailWord_1448182, baseEnd_1448182] using wordTrace_append hprefix tailTrace_1448182
  have hstable : (prefixWord ++ tailWord_1448182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448182).length < 2 ^ (prefixWord ++ tailWord_1448182).sum := by decide
  have hdescent : baseEnd_1448182 < baseStart_1448182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448255 : List Nat := [1, 1, 2, 2, 4, 1, 3, 3, 2, 3]
def baseStart_1448255 : Nat := 118140960795 + 1448255 * 2 ^ 59
def prefixEnd_1448255 : Nat := 4983230072969 + 3 ^ 40 * 1448255 * 2
def baseEnd_1448255 : Nat := 495767283518224286234735

theorem tailTrace_1448255 : CollatzResearch.WordTrace tailWord_1448255 prefixEnd_1448255 495767283518224286234735 := by
  unfold tailWord_1448255
  simp only [CollatzResearch.WordTrace]
  refine ⟨52822199368226952107186219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35214799578817968071457479 52822199368226952107186219)
  ·
    refine ⟨79233299052340428160779329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52822199368226952107186219 79233299052340428160779329)
    ·
      refine ⟨59424974289255321120584497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79233299052340428160779329 59424974289255321120584497)
      ·
        refine ⟨44568730716941490840438373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59424974289255321120584497 44568730716941490840438373)
        ·
          refine ⟨8356637009426529532582195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44568730716941490840438373 8356637009426529532582195)
          ·
            refine ⟨12534955514139794298873293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8356637009426529532582195 12534955514139794298873293)
            ·
              refine ⟨4700608317802422862077485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12534955514139794298873293 4700608317802422862077485)
              ·
                refine ⟨1762728119175908573279057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4700608317802422862077485 1762728119175908573279057)
                ·
                  refine ⟨1322046089381931429959293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1762728119175908573279057 1322046089381931429959293)
                  ·
                    refine ⟨495767283518224286234735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1322046089381931429959293 495767283518224286234735)
                    ·
                      rfl

theorem cell22_1448255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2, 3].length) (baseStart_1448255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448255 prefixEnd_1448255 := by exact prefixLift 1448255
  have htrace : WordTrace (prefixWord ++ tailWord_1448255) baseStart_1448255 baseEnd_1448255 := by
    simpa [prefixWord, tailWord_1448255, baseEnd_1448255] using wordTrace_append hprefix tailTrace_1448255
  have hstable : (prefixWord ++ tailWord_1448255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448255).length < 2 ^ (prefixWord ++ tailWord_1448255).sum := by decide
  have hdescent : baseEnd_1448255 < baseStart_1448255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448328 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 1, 7]
def baseStart_1448328 : Nat := 118140960795 + 1448328 * 2 ^ 59
def prefixEnd_1448328 : Nat := 4983230072969 + 3 ^ 40 * 1448328 * 2
def baseEnd_1448328 : Nat := 495792272910076429159511

theorem tailTrace_1448328 : CollatzResearch.WordTrace tailWord_1448328 prefixEnd_1448328 495792272910076429159511 := by
  unfold tailWord_1448328
  simp only [CollatzResearch.WordTrace]
  refine ⟨26412430948481242787296819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35216574597974990383062425 26412430948481242787296819)
  ·
    refine ⟨39618646422721864180945229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26412430948481242787296819 39618646422721864180945229)
    ·
      refine ⟨14856992408520699067854461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39618646422721864180945229 14856992408520699067854461)
      ·
        refine ⟨5571372153195262150445423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14856992408520699067854461 5571372153195262150445423)
        ·
          refine ⟨8357058229792893225668135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5571372153195262150445423 8357058229792893225668135)
          ·
            refine ⟨12535587344689339838502203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8357058229792893225668135 12535587344689339838502203)
            ·
              refine ⟨18803381017034009757753305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12535587344689339838502203 18803381017034009757753305)
              ·
                refine ⟨14102535762775507318314979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18803381017034009757753305 14102535762775507318314979)
                ·
                  refine ⟨21153803644163260977472469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14102535762775507318314979 21153803644163260977472469)
                  ·
                    refine ⟨495792272910076429159511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21153803644163260977472469 495792272910076429159511)
                    ·
                      rfl

theorem cell22_1448328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_1448328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448328 prefixEnd_1448328 := by exact prefixLift 1448328
  have htrace : WordTrace (prefixWord ++ tailWord_1448328) baseStart_1448328 baseEnd_1448328 := by
    simpa [prefixWord, tailWord_1448328, baseEnd_1448328] using wordTrace_append hprefix tailTrace_1448328
  have hstable : (prefixWord ++ tailWord_1448328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448328).length < 2 ^ (prefixWord ++ tailWord_1448328).sum := by decide
  have hdescent : baseEnd_1448328 < baseStart_1448328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448334 : List Nat := [4, 1, 1, 4, 1, 1, 1, 5, 1, 3]
def baseStart_1448334 : Nat := 118140960795 + 1448334 * 2 ^ 59
def prefixEnd_1448334 : Nat := 4983230072969 + 3 ^ 40 * 1448334 * 2
def baseEnd_1448334 : Nat := 495794326832694413509493

theorem tailTrace_1448334 : CollatzResearch.WordTrace tailWord_1448334 prefixEnd_1448334 495794326832694413509493 := by
  unfold tailWord_1448334
  simp only [CollatzResearch.WordTrace]
  refine ⟨6603135091867593574914007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35216720489960499066208037 6603135091867593574914007)
  ·
    refine ⟨9904702637801390362371011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6603135091867593574914007 9904702637801390362371011)
    ·
      refine ⟨14857053956702085543556517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9904702637801390362371011 14857053956702085543556517)
      ·
        refine ⟨2785697616881641039416847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14857053956702085543556517 2785697616881641039416847)
        ·
          refine ⟨4178546425322461559125271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2785697616881641039416847 4178546425322461559125271)
          ·
            refine ⟨6267819637983692338687907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4178546425322461559125271 6267819637983692338687907)
            ·
              refine ⟨9401729456975538508031861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6267819637983692338687907 9401729456975538508031861)
              ·
                refine ⟨881412136591456735127987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9401729456975538508031861 881412136591456735127987)
                ·
                  refine ⟨1322118204887185102691981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 881412136591456735127987 1322118204887185102691981)
                  ·
                    refine ⟨495794326832694413509493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1322118204887185102691981 495794326832694413509493)
                    ·
                      rfl

theorem cell22_1448334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_1448334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448334 prefixEnd_1448334 := by exact prefixLift 1448334
  have htrace : WordTrace (prefixWord ++ tailWord_1448334) baseStart_1448334 baseEnd_1448334 := by
    simpa [prefixWord, tailWord_1448334, baseEnd_1448334] using wordTrace_append hprefix tailTrace_1448334
  have hstable : (prefixWord ++ tailWord_1448334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448334).length < 2 ^ (prefixWord ++ tailWord_1448334).sum := by decide
  have hdescent : baseEnd_1448334 < baseStart_1448334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448377 : List Nat := [1, 2, 1, 4, 3, 2, 2, 2, 1, 4]
def baseStart_1448377 : Nat := 118140960795 + 1448377 * 2 ^ 59
def prefixEnd_1448377 : Nat := 4983230072969 + 3 ^ 40 * 1448377 * 2
def baseEnd_1448377 : Nat := 495809046611456634684361

theorem tailTrace_1448377 : CollatzResearch.WordTrace tailWord_1448377 prefixEnd_1448377 495809046611456634684361 := by
  unfold tailWord_1448377
  simp only [CollatzResearch.WordTrace]
  refine ⟨52826649073784966943127385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35217766049189977962084923 52826649073784966943127385)
  ·
    refine ⟨39619986805338725207345539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52826649073784966943127385 39619986805338725207345539)
    ·
      refine ⟨59429980208008087811018309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39619986805338725207345539 59429980208008087811018309)
      ·
        refine ⟨11143121289001516464565933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59429980208008087811018309 11143121289001516464565933)
        ·
          refine ⟨4178670483375568674212225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11143121289001516464565933 4178670483375568674212225)
          ·
            refine ⟨3134002862531676505659169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4178670483375568674212225 3134002862531676505659169)
            ·
              refine ⟨2350502146898757379244377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3134002862531676505659169 2350502146898757379244377)
              ·
                refine ⟨1762876610174068034433283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2350502146898757379244377 1762876610174068034433283)
                ·
                  refine ⟨2644314915261102051649925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1762876610174068034433283 2644314915261102051649925)
                  ·
                    refine ⟨495809046611456634684361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2644314915261102051649925 495809046611456634684361)
                    ·
                      rfl

theorem cell22_1448377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 4].length) (baseStart_1448377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448377 prefixEnd_1448377 := by exact prefixLift 1448377
  have htrace : WordTrace (prefixWord ++ tailWord_1448377) baseStart_1448377 baseEnd_1448377 := by
    simpa [prefixWord, tailWord_1448377, baseEnd_1448377] using wordTrace_append hprefix tailTrace_1448377
  have hstable : (prefixWord ++ tailWord_1448377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448377).length < 2 ^ (prefixWord ++ tailWord_1448377).sum := by decide
  have hdescent : baseEnd_1448377 < baseStart_1448377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448385 : List Nat := [1, 2, 7, 1, 1, 2, 1, 3, 1, 3]
def baseStart_1448385 : Nat := 118140960795 + 1448385 * 2 ^ 59
def prefixEnd_1448385 : Nat := 4983230072969 + 3 ^ 40 * 1448385 * 2
def baseEnd_1448385 : Nat := 495811785174947280484337

theorem tailTrace_1448385 : CollatzResearch.WordTrace tailWord_1448385 prefixEnd_1448385 495811785174947280484337 := by
  unfold tailWord_1448385
  simp only [CollatzResearch.WordTrace]
  refine ⟨52826940857755984309418609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35217960571837322872945739 52826940857755984309418609)
  ·
    refine ⟨39620205643316988232063957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52826940857755984309418609 39620205643316988232063957)
    ·
      refine ⟨928598569765241911688999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 39620205643316988232063957 928598569765241911688999)
      ·
        refine ⟨1392897854647862867533499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 928598569765241911688999 1392897854647862867533499)
        ·
          refine ⟨2089346781971794301300249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1392897854647862867533499 2089346781971794301300249)
          ·
            refine ⟨1567010086478845725975187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2089346781971794301300249 1567010086478845725975187)
            ·
              refine ⟨2350515129718268588962781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1567010086478845725975187 2350515129718268588962781)
              ·
                refine ⟨881443173644350720861043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2350515129718268588962781 881443173644350720861043)
                ·
                  refine ⟨1322164760466526081291565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 881443173644350720861043 1322164760466526081291565)
                  ·
                    refine ⟨495811785174947280484337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1322164760466526081291565 495811785174947280484337)
                    ·
                      rfl

theorem cell22_1448385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_1448385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448385 prefixEnd_1448385 := by exact prefixLift 1448385
  have htrace : WordTrace (prefixWord ++ tailWord_1448385) baseStart_1448385 baseEnd_1448385 := by
    simpa [prefixWord, tailWord_1448385, baseEnd_1448385] using wordTrace_append hprefix tailTrace_1448385
  have hstable : (prefixWord ++ tailWord_1448385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448385).length < 2 ^ (prefixWord ++ tailWord_1448385).sum := by decide
  have hdescent : baseEnd_1448385 < baseStart_1448385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448392 : List Nat := [2, 1, 3, 1, 3, 2, 3, 3, 4]
def baseStart_1448392 : Nat := 118140960795 + 1448392 * 2 ^ 59
def prefixEnd_1448392 : Nat := 4983230072969 + 3 ^ 40 * 1448392 * 2
def baseEnd_1448392 : Nat := 165271393806000531853105

theorem tailTrace_1448392 : CollatzResearch.WordTrace tailWord_1448392 prefixEnd_1448392 165271393806000531853105 := by
  unfold tailWord_1448392
  simp only [CollatzResearch.WordTrace]
  refine ⟨26413598084365312252461715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35218130779153749669948953 26413598084365312252461715)
  ·
    refine ⟨39620397126547968378692573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26413598084365312252461715 39620397126547968378692573)
    ·
      refine ⟨14857648922455488142009715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39620397126547968378692573 14857648922455488142009715)
      ·
        refine ⟨22286473383683232213014573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14857648922455488142009715 22286473383683232213014573)
        ·
          refine ⟨8357427518881212079880465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22286473383683232213014573 8357427518881212079880465)
          ·
            refine ⟨6268070639160909059910349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8357427518881212079880465 6268070639160909059910349)
            ·
              refine ⟨2350526489685340897466381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6268070639160909059910349 2350526489685340897466381)
              ·
                refine ⟨881447433632002836549893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2350526489685340897466381 881447433632002836549893)
                ·
                  refine ⟨165271393806000531853105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 881447433632002836549893 165271393806000531853105)
                  ·
                    rfl

theorem cell22_1448392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3, 4].length) (baseStart_1448392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448392 prefixEnd_1448392 := by exact prefixLift 1448392
  have htrace : WordTrace (prefixWord ++ tailWord_1448392) baseStart_1448392 baseEnd_1448392 := by
    simpa [prefixWord, tailWord_1448392, baseEnd_1448392] using wordTrace_append hprefix tailTrace_1448392
  have hstable : (prefixWord ++ tailWord_1448392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448392).length < 2 ^ (prefixWord ++ tailWord_1448392).sum := by decide
  have hdescent : baseEnd_1448392 < baseStart_1448392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448405 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 4, 4]
def baseStart_1448405 : Nat := 118140960795 + 1448405 * 2 ^ 59
def prefixEnd_1448405 : Nat := 4983230072969 + 3 ^ 40 * 1448405 * 2
def baseEnd_1448405 : Nat := 495818631583673894984275

theorem tailTrace_1448405 : CollatzResearch.WordTrace tailWord_1448405 prefixEnd_1448405 495818631583673894984275 := by
  unfold tailWord_1448405
  simp only [CollatzResearch.WordTrace]
  refine ⟨52827670317683527725146669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35218446878455685150097779 52827670317683527725146669)
  ·
    refine ⟨19810376369131322896930001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52827670317683527725146669 19810376369131322896930001)
    ·
      refine ⟨14857782276848492172697501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19810376369131322896930001 14857782276848492172697501)
      ·
        refine ⟨5571668353818184564761563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14857782276848492172697501 5571668353818184564761563)
        ·
          refine ⟨8357502530727276847142345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5571668353818184564761563 8357502530727276847142345)
          ·
            refine ⟨6268126898045457635356759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8357502530727276847142345 6268126898045457635356759)
            ·
              refine ⟨9402190347068186453035139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6268126898045457635356759 9402190347068186453035139)
              ·
                refine ⟨14103285520602279679552709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9402190347068186453035139 14103285520602279679552709)
                ·
                  refine ⟨2644366035112927439916133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14103285520602279679552709 2644366035112927439916133)
                  ·
                    refine ⟨495818631583673894984275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2644366035112927439916133 495818631583673894984275)
                    ·
                      rfl

theorem cell22_1448405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_1448405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448405 prefixEnd_1448405 := by exact prefixLift 1448405
  have htrace : WordTrace (prefixWord ++ tailWord_1448405) baseStart_1448405 baseEnd_1448405 := by
    simpa [prefixWord, tailWord_1448405, baseEnd_1448405] using wordTrace_append hprefix tailTrace_1448405
  have hstable : (prefixWord ++ tailWord_1448405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448405).length < 2 ^ (prefixWord ++ tailWord_1448405).sum := by decide
  have hdescent : baseEnd_1448405 < baseStart_1448405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448424 : List Nat := [2, 1, 4, 1, 1, 3, 4, 1, 2, 3]
def baseStart_1448424 : Nat := 118140960795 + 1448424 * 2 ^ 59
def prefixEnd_1448424 : Nat := 4983230072969 + 3 ^ 40 * 1448424 * 2
def baseEnd_1448424 : Nat := 495825135671964178759217

theorem tailTrace_1448424 : CollatzResearch.WordTrace tailWord_1448424 prefixEnd_1448424 495825135671964178759217 := by
  unfold tailWord_1448424
  simp only [CollatzResearch.WordTrace]
  refine ⟨26414181652307346985044163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35218908869743129313392217 26414181652307346985044163)
  ·
    refine ⟨39621272478461020477566245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26414181652307346985044163 39621272478461020477566245)
    ·
      refine ⟨7428988589711441339543671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39621272478461020477566245 7428988589711441339543671)
      ·
        refine ⟨11143482884567162009315507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7428988589711441339543671 11143482884567162009315507)
        ·
          refine ⟨16715224326850743013973261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11143482884567162009315507 16715224326850743013973261)
          ·
            refine ⟨6268209122569028630239973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16715224326850743013973261 6268209122569028630239973)
            ·
              refine ⟨1175289210481692868169995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6268209122569028630239973 1175289210481692868169995)
              ·
                refine ⟨1762933815722539302254993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1175289210481692868169995 1762933815722539302254993)
                ·
                  refine ⟨1322200361791904476691245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1762933815722539302254993 1322200361791904476691245)
                  ·
                    refine ⟨495825135671964178759217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1322200361791904476691245 495825135671964178759217)
                    ·
                      rfl

theorem cell22_1448424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_1448424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448424 prefixEnd_1448424 := by exact prefixLift 1448424
  have htrace : WordTrace (prefixWord ++ tailWord_1448424) baseStart_1448424 baseEnd_1448424 := by
    simpa [prefixWord, tailWord_1448424, baseEnd_1448424] using wordTrace_append hprefix tailTrace_1448424
  have hstable : (prefixWord ++ tailWord_1448424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448424).length < 2 ^ (prefixWord ++ tailWord_1448424).sum := by decide
  have hdescent : baseEnd_1448424 < baseStart_1448424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448435 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 5, 3]
def baseStart_1448435 : Nat := 118140960795 + 1448435 * 2 ^ 59
def prefixEnd_1448435 : Nat := 4983230072969 + 3 ^ 40 * 1448435 * 2
def baseEnd_1448435 : Nat := 495828901196763816734183

theorem tailTrace_1448435 : CollatzResearch.WordTrace tailWord_1448435 prefixEnd_1448435 495828901196763816734183 := by
  unfold tailWord_1448435
  simp only [CollatzResearch.WordTrace]
  refine ⟨52828764507574842848738759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35219176338383228565825839 52828764507574842848738759)
  ·
    refine ⟨79243146761362264273108139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52828764507574842848738759 79243146761362264273108139)
    ·
      refine ⟨118864720142043396409662209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79243146761362264273108139 118864720142043396409662209)
      ·
        refine ⟨89148540106532547307246657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118864720142043396409662209 89148540106532547307246657)
        ·
          refine ⟨66861405079899410480434993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89148540106532547307246657 66861405079899410480434993)
          ·
            refine ⟨50146053809924557860326245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66861405079899410480434993 50146053809924557860326245)
            ·
              refine ⟨9402385089360854598811171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50146053809924557860326245 9402385089360854598811171)
              ·
                refine ⟨14103577634041281898216757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9402385089360854598811171 14103577634041281898216757)
                ·
                  refine ⟨1322210403191370177957821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14103577634041281898216757 1322210403191370177957821)
                  ·
                    refine ⟨495828901196763816734183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1322210403191370177957821 495828901196763816734183)
                    ·
                      rfl

theorem cell22_1448435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5, 3].length) (baseStart_1448435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448435 prefixEnd_1448435 := by exact prefixLift 1448435
  have htrace : WordTrace (prefixWord ++ tailWord_1448435) baseStart_1448435 baseEnd_1448435 := by
    simpa [prefixWord, tailWord_1448435, baseEnd_1448435] using wordTrace_append hprefix tailTrace_1448435
  have hstable : (prefixWord ++ tailWord_1448435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448435).length < 2 ^ (prefixWord ++ tailWord_1448435).sum := by decide
  have hdescent : baseEnd_1448435 < baseStart_1448435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448454 : List Nat := [6, 2, 1, 1, 1, 11]
def baseStart_1448454 : Nat := 118140960795 + 1448454 * 2 ^ 59
def prefixEnd_1448454 : Nat := 4983230072969 + 3 ^ 40 * 1448454 * 2
def baseEnd_1448454 : Nat := 6121424756605606179125

theorem tailTrace_1448454 : CollatzResearch.WordTrace tailWord_1448454 prefixEnd_1448454 6121424756605606179125 := by
  unfold tailWord_1448454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1650920546703312784177513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35219638329670672729120277 1650920546703312784177513)
  ·
    refine ⟨1238190410027484588133135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1650920546703312784177513 1238190410027484588133135)
    ·
      refine ⟨1857285615041226882199703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1238190410027484588133135 1857285615041226882199703)
      ·
        refine ⟨2785928422561840323299555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1857285615041226882199703 2785928422561840323299555)
        ·
          refine ⟨4178892633842760484949333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2785928422561840323299555 4178892633842760484949333)
          ·
            refine ⟨6121424756605606179125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4178892633842760484949333 6121424756605606179125)
            ·
              rfl

theorem cell22_1448454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 11].length) (baseStart_1448454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448454 prefixEnd_1448454 := by exact prefixLift 1448454
  have htrace : WordTrace (prefixWord ++ tailWord_1448454) baseStart_1448454 baseEnd_1448454 := by
    simpa [prefixWord, tailWord_1448454, baseEnd_1448454] using wordTrace_append hprefix tailTrace_1448454
  have hstable : (prefixWord ++ tailWord_1448454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448454).length < 2 ^ (prefixWord ++ tailWord_1448454).sum := by decide
  have hdescent : baseEnd_1448454 < baseStart_1448454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448469 : List Nat := [1, 3, 2, 1, 3, 1, 3, 4, 1, 3]
def baseStart_1448469 : Nat := 118140960795 + 1448469 * 2 ^ 59
def prefixEnd_1448469 : Nat := 4983230072969 + 3 ^ 40 * 1448469 * 2
def baseEnd_1448469 : Nat := 495840540091599061384079

theorem tailTrace_1448469 : CollatzResearch.WordTrace tailWord_1448469 prefixEnd_1448469 495840540091599061384079 := by
  unfold tailWord_1448469
  simp only [CollatzResearch.WordTrace]
  refine ⟨52830004589451666655476461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35220003059634444436984307 52830004589451666655476461)
  ·
    refine ⟨19811251721044374995803673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52830004589451666655476461 19811251721044374995803673)
    ·
      refine ⟨14858438790783281246852755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19811251721044374995803673 14858438790783281246852755)
      ·
        refine ⟨22287658186174921870279133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14858438790783281246852755 22287658186174921870279133)
        ·
          refine ⟨8357871819815595701354675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22287658186174921870279133 8357871819815595701354675)
          ·
            refine ⟨12536807729723393552032013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8357871819815595701354675 12536807729723393552032013)
            ·
              refine ⟨4701302898646272582012005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12536807729723393552032013 4701302898646272582012005)
              ·
                refine ⟨881494293496176109127251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4701302898646272582012005 881494293496176109127251)
                ·
                  refine ⟨1322241440244264163690877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 881494293496176109127251 1322241440244264163690877)
                  ·
                    refine ⟨495840540091599061384079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1322241440244264163690877 495840540091599061384079)
                    ·
                      rfl

theorem cell22_1448469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_1448469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448469 prefixEnd_1448469 := by exact prefixLift 1448469
  have htrace : WordTrace (prefixWord ++ tailWord_1448469) baseStart_1448469 baseEnd_1448469 := by
    simpa [prefixWord, tailWord_1448469, baseEnd_1448469] using wordTrace_append hprefix tailTrace_1448469
  have hstable : (prefixWord ++ tailWord_1448469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448469).length < 2 ^ (prefixWord ++ tailWord_1448469).sum := by decide
  have hdescent : baseEnd_1448469 < baseStart_1448469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448516 : List Nat := [2, 3, 5, 1, 1, 1, 1, 1, 7]
def baseStart_1448516 : Nat := 118140960795 + 1448516 * 2 ^ 59
def prefixEnd_1448516 : Nat := 4983230072969 + 3 ^ 40 * 1448516 * 2
def baseEnd_1448516 : Nat := 165285543050702201819645

theorem tailTrace_1448516 : CollatzResearch.WordTrace tailWord_1448516 prefixEnd_1448516 165285543050702201819645 := by
  unfold tailWord_1448516
  simp only [CollatzResearch.WordTrace]
  refine ⟨26415859410140696841218701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35221145880187595788291601 26415859410140696841218701)
  ·
    refine ⟨9905947278802761315457013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26415859410140696841218701 9905947278802761315457013)
    ·
      refine ⟨928682557387758873324095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9905947278802761315457013 928682557387758873324095)
      ·
        refine ⟨1393023836081638309986143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 928682557387758873324095 1393023836081638309986143)
        ·
          refine ⟨2089535754122457464979215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1393023836081638309986143 2089535754122457464979215)
          ·
            refine ⟨3134303631183686197468823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2089535754122457464979215 3134303631183686197468823)
            ·
              refine ⟨4701455446775529296203235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3134303631183686197468823 4701455446775529296203235)
              ·
                refine ⟨7052183170163293944304853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4701455446775529296203235 7052183170163293944304853)
                ·
                  refine ⟨165285543050702201819645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7052183170163293944304853 165285543050702201819645)
                  ·
                    rfl

theorem cell22_1448516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_1448516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448516 prefixEnd_1448516 := by exact prefixLift 1448516
  have htrace : WordTrace (prefixWord ++ tailWord_1448516) baseStart_1448516 baseEnd_1448516 := by
    simpa [prefixWord, tailWord_1448516, baseEnd_1448516] using wordTrace_append hprefix tailTrace_1448516
  have hstable : (prefixWord ++ tailWord_1448516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448516).length < 2 ^ (prefixWord ++ tailWord_1448516).sum := by decide
  have hdescent : baseEnd_1448516 < baseStart_1448516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448527 : List Nat := [1, 1, 2, 1, 1, 2, 6, 4, 4]
def baseStart_1448527 : Nat := 118140960795 + 1448527 * 2 ^ 59
def prefixEnd_1448527 : Nat := 4983230072969 + 3 ^ 40 * 1448527 * 2
def baseEnd_1448527 : Nat := 165286798225635414477967

theorem tailTrace_1448527 : CollatzResearch.WordTrace tailWord_1448527 prefixEnd_1448527 165286798225635414477967 := by
  unfold tailWord_1448527
  simp only [CollatzResearch.WordTrace]
  refine ⟨52832120023241542561087835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35221413348827695040725223 52832120023241542561087835)
  ·
    refine ⟨79248180034862313841631753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52832120023241542561087835 79248180034862313841631753)
    ·
      refine ⟨59436135026146735381223815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79248180034862313841631753 59436135026146735381223815)
      ·
        refine ⟨89154202539220103071835723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59436135026146735381223815 89154202539220103071835723)
        ·
          refine ⟨133731303808830154607753585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89154202539220103071835723 133731303808830154607753585)
          ·
            refine ⟨100298477856622615955815189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133731303808830154607753585 100298477856622615955815189)
            ·
              refine ⟨4701491149529185122928837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 100298477856622615955815189 4701491149529185122928837)
              ·
                refine ⟨881529590536722210549157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4701491149529185122928837 881529590536722210549157)
                ·
                  refine ⟨165286798225635414477967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 881529590536722210549157 165286798225635414477967)
                  ·
                    rfl

theorem cell22_1448527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4, 4].length) (baseStart_1448527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448527 prefixEnd_1448527 := by exact prefixLift 1448527
  have htrace : WordTrace (prefixWord ++ tailWord_1448527) baseStart_1448527 baseEnd_1448527 := by
    simpa [prefixWord, tailWord_1448527, baseEnd_1448527] using wordTrace_append hprefix tailTrace_1448527
  have hstable : (prefixWord ++ tailWord_1448527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448527).length < 2 ^ (prefixWord ++ tailWord_1448527).sum := by decide
  have hdescent : baseEnd_1448527 < baseStart_1448527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448557 : List Nat := [1, 5, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_1448557 : Nat := 118140960795 + 1448557 * 2 ^ 59
def prefixEnd_1448557 : Nat := 4983230072969 + 3 ^ 40 * 1448557 * 2
def baseEnd_1448557 : Nat := 495870664289996165183809

theorem tailTrace_1448557 : CollatzResearch.WordTrace tailWord_1448557 prefixEnd_1448557 495870664289996165183809 := by
  unfold tailWord_1448557
  simp only [CollatzResearch.WordTrace]
  refine ⟨52833214213132857684679925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35222142808755238456453283 52833214213132857684679925)
  ·
    refine ⟨4953113832481205407938743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52833214213132857684679925 4953113832481205407938743)
    ·
      refine ⟨7429670748721808111908115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4953113832481205407938743 7429670748721808111908115)
      ·
        refine ⟨11144506123082712167862173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7429670748721808111908115 11144506123082712167862173)
        ·
          refine ⟨4179189796156017062948315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11144506123082712167862173 4179189796156017062948315)
          ·
            refine ⟨6268784694234025594422473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4179189796156017062948315 6268784694234025594422473)
            ·
              refine ⟨4701588520675519195816855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6268784694234025594422473 4701588520675519195816855)
              ·
                refine ⟨7052382781013278793725283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4701588520675519195816855 7052382781013278793725283)
                ·
                  refine ⟨10578574171519918190587925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7052382781013278793725283 10578574171519918190587925)
                  ·
                    refine ⟨495870664289996165183809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10578574171519918190587925 495870664289996165183809)
                    ·
                      rfl

theorem cell22_1448557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_1448557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448557 prefixEnd_1448557 := by exact prefixLift 1448557
  have htrace : WordTrace (prefixWord ++ tailWord_1448557) baseStart_1448557 baseEnd_1448557 := by
    simpa [prefixWord, tailWord_1448557, baseEnd_1448557] using wordTrace_append hprefix tailTrace_1448557
  have hstable : (prefixWord ++ tailWord_1448557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448557).length < 2 ^ (prefixWord ++ tailWord_1448557).sum := by decide
  have hdescent : baseEnd_1448557 < baseStart_1448557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448585 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 2, 6]
def baseStart_1448585 : Nat := 118140960795 + 1448585 * 2 ^ 59
def prefixEnd_1448585 : Nat := 4983230072969 + 3 ^ 40 * 1448585 * 2
def baseEnd_1448585 : Nat := 495880249262213425483723

theorem tailTrace_1448585 : CollatzResearch.WordTrace tailWord_1448585 prefixEnd_1448585 495880249262213425483723 := by
  unfold tailWord_1448585
  simp only [CollatzResearch.WordTrace]
  refine ⟨52834235457031418466699209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35222823638020945644466139 52834235457031418466699209)
  ·
    refine ⟨39625676592773563850024407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52834235457031418466699209 39625676592773563850024407)
    ·
      refine ⟨59438514889160345775036611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39625676592773563850024407 59438514889160345775036611)
      ·
        refine ⟨89157772333740518662554917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59438514889160345775036611 89157772333740518662554917)
        ·
          refine ⟨16717082312576347249229047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89157772333740518662554917 16717082312576347249229047)
          ·
            refine ⟨25075623468864520873843571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16717082312576347249229047 25075623468864520873843571)
            ·
              refine ⟨37613435203296781310765357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25075623468864520873843571 37613435203296781310765357)
              ·
                refine ⟨14105038201236292991537009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37613435203296781310765357 14105038201236292991537009)
                ·
                  refine ⟨10578778650927219743652757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14105038201236292991537009 10578778650927219743652757)
                  ·
                    refine ⟨495880249262213425483723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10578778650927219743652757 495880249262213425483723)
                    ·
                      rfl

theorem cell22_1448585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 6].length) (baseStart_1448585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448585 prefixEnd_1448585 := by exact prefixLift 1448585
  have htrace : WordTrace (prefixWord ++ tailWord_1448585) baseStart_1448585 baseEnd_1448585 := by
    simpa [prefixWord, tailWord_1448585, baseEnd_1448585] using wordTrace_append hprefix tailTrace_1448585
  have hstable : (prefixWord ++ tailWord_1448585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448585).length < 2 ^ (prefixWord ++ tailWord_1448585).sum := by decide
  have hdescent : baseEnd_1448585 < baseStart_1448585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448587 : List Nat := [1, 1, 1, 1, 4, 1, 2, 5, 3, 3]
def baseStart_1448587 : Nat := 118140960795 + 1448587 * 2 ^ 59
def prefixEnd_1448587 : Nat := 4983230072969 + 3 ^ 40 * 1448587 * 2
def baseEnd_1448587 : Nat := 495880933903086086933717

theorem tailTrace_1448587 : CollatzResearch.WordTrace tailWord_1448587 prefixEnd_1448587 495880933903086086933717 := by
  unfold tailWord_1448587
  simp only [CollatzResearch.WordTrace]
  refine ⟨52834308403024172808272015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35222872268682781872181343 52834308403024172808272015)
  ·
    refine ⟨79251462604536259212408023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52834308403024172808272015 79251462604536259212408023)
    ·
      refine ⟨118877193906804388818612035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79251462604536259212408023 118877193906804388818612035)
      ·
        refine ⟨178315790860206583227918053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118877193906804388818612035 178315790860206583227918053)
        ·
          refine ⟨33434210786288734355234635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178315790860206583227918053 33434210786288734355234635)
          ·
            refine ⟨50151316179433101532851953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33434210786288734355234635 50151316179433101532851953)
            ·
              refine ⟨37613487134574826149638965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50151316179433101532851953 37613487134574826149638965)
              ·
                refine ⟨3526264418866389951528653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37613487134574826149638965 3526264418866389951528653)
                ·
                  refine ⟨1322349157074896231823245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3526264418866389951528653 1322349157074896231823245)
                  ·
                    refine ⟨495880933903086086933717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1322349157074896231823245 495880933903086086933717)
                    ·
                      rfl

theorem cell22_1448587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3, 3].length) (baseStart_1448587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448587 prefixEnd_1448587 := by exact prefixLift 1448587
  have htrace : WordTrace (prefixWord ++ tailWord_1448587) baseStart_1448587 baseEnd_1448587 := by
    simpa [prefixWord, tailWord_1448587, baseEnd_1448587] using wordTrace_append hprefix tailTrace_1448587
  have hstable : (prefixWord ++ tailWord_1448587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448587).length < 2 ^ (prefixWord ++ tailWord_1448587).sum := by decide
  have hdescent : baseEnd_1448587 < baseStart_1448587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448711 : List Nat := [1, 1, 4, 4, 1, 3, 1, 1, 1, 5]
def baseStart_1448711 : Nat := 118140960795 + 1448711 * 2 ^ 59
def prefixEnd_1448711 : Nat := 4983230072969 + 3 ^ 40 * 1448711 * 2
def baseEnd_1448711 : Nat := 495923381637191096833337

theorem tailTrace_1448711 : CollatzResearch.WordTrace tailWord_1448711 prefixEnd_1448711 495923381637191096833337 := by
  unfold tailWord_1448711
  simp only [CollatzResearch.WordTrace]
  refine ⟨52838831054574941985785987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35225887369716627990523991 52838831054574941985785987)
  ·
    refine ⟨79258246581862412978678981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52838831054574941985785987 79258246581862412978678981)
    ·
      refine ⟨14860921234099202433502309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79258246581862412978678981 14860921234099202433502309)
      ·
        refine ⟨2786422731393600456281683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14860921234099202433502309 2786422731393600456281683)
        ·
          refine ⟨4179634097090400684422525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2786422731393600456281683 4179634097090400684422525)
          ·
            refine ⟨1567362786408900256658447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4179634097090400684422525 1567362786408900256658447)
            ·
              refine ⟨2351044179613350384987671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1567362786408900256658447 2351044179613350384987671)
              ·
                refine ⟨3526566269420025577481507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2351044179613350384987671 3526566269420025577481507)
                ·
                  refine ⟨5289849404130038366222261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3526566269420025577481507 5289849404130038366222261)
                  ·
                    refine ⟨495923381637191096833337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5289849404130038366222261 495923381637191096833337)
                    ·
                      rfl

theorem cell22_1448711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_1448711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448711 prefixEnd_1448711 := by exact prefixLift 1448711
  have htrace : WordTrace (prefixWord ++ tailWord_1448711) baseStart_1448711 baseEnd_1448711 := by
    simpa [prefixWord, tailWord_1448711, baseEnd_1448711] using wordTrace_append hprefix tailTrace_1448711
  have hstable : (prefixWord ++ tailWord_1448711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448711).length < 2 ^ (prefixWord ++ tailWord_1448711).sum := by decide
  have hdescent : baseEnd_1448711 < baseStart_1448711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448829 : List Nat := [1, 4, 1, 1, 2, 1, 3, 3, 1, 5]
def baseStart_1448829 : Nat := 118140960795 + 1448829 * 2 ^ 59
def prefixEnd_1448829 : Nat := 4983230072969 + 3 ^ 40 * 1448829 * 2
def baseEnd_1448829 : Nat := 495963775448678122382975

theorem tailTrace_1448829 : CollatzResearch.WordTrace tailWord_1448829 prefixEnd_1448829 495963775448678122382975 := by
  unfold tailWord_1448829
  simp only [CollatzResearch.WordTrace]
  refine ⟨52843134868147448138581541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35228756578764965425721027 52843134868147448138581541)
  ·
    refine ⟨9908087787777646525984039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52843134868147448138581541 9908087787777646525984039)
    ·
      refine ⟨14862131681666469788976059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9908087787777646525984039 14862131681666469788976059)
      ·
        refine ⟨22293197522499704683464089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14862131681666469788976059 22293197522499704683464089)
        ·
          refine ⟨16719898141874778512598067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22293197522499704683464089 16719898141874778512598067)
          ·
            refine ⟨25079847212812167768897101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16719898141874778512598067 25079847212812167768897101)
            ·
              refine ⟨9404942704804562913336413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25079847212812167768897101 9404942704804562913336413)
              ·
                refine ⟨3526853514301711092501155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9404942704804562913336413 3526853514301711092501155)
                ·
                  refine ⟨5290280271452566638751733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3526853514301711092501155 5290280271452566638751733)
                  ·
                    refine ⟨495963775448678122382975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5290280271452566638751733 495963775448678122382975)
                    ·
                      rfl

theorem cell22_1448829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_1448829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448829 prefixEnd_1448829 := by exact prefixLift 1448829
  have htrace : WordTrace (prefixWord ++ tailWord_1448829) baseStart_1448829 baseEnd_1448829 := by
    simpa [prefixWord, tailWord_1448829, baseEnd_1448829] using wordTrace_append hprefix tailTrace_1448829
  have hstable : (prefixWord ++ tailWord_1448829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448829).length < 2 ^ (prefixWord ++ tailWord_1448829).sum := by decide
  have hdescent : baseEnd_1448829 < baseStart_1448829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448863 : List Nat := [1, 1, 2, 5, 2, 1, 3, 2, 2, 3]
def baseStart_1448863 : Nat := 118140960795 + 1448863 * 2 ^ 59
def prefixEnd_1448863 : Nat := 4983230072969 + 3 ^ 40 * 1448863 * 2
def baseEnd_1448863 : Nat := 495975414343513367032871

theorem tailTrace_1448863 : CollatzResearch.WordTrace tailWord_1448863 prefixEnd_1448863 495975414343513367032871 := by
  unfold tailWord_1448863
  simp only [CollatzResearch.WordTrace]
  refine ⟨52844374950024271945319243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35229583300016181296879495 52844374950024271945319243)
  ·
    refine ⟨79266562425036407917978865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52844374950024271945319243 79266562425036407917978865)
    ·
      refine ⟨59449921818777305938484149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79266562425036407917978865 59449921818777305938484149)
      ·
        refine ⟨5573430170510372431732889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59449921818777305938484149 5573430170510372431732889)
        ·
          refine ⟨4180072627882779323799667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5573430170510372431732889 4180072627882779323799667)
          ·
            refine ⟨6270108941824168985699501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4180072627882779323799667 6270108941824168985699501)
            ·
              refine ⟨2351290853184063369637313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6270108941824168985699501 2351290853184063369637313)
              ·
                refine ⟨1763468139888047527227985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2351290853184063369637313 1763468139888047527227985)
                ·
                  refine ⟨1322601104916035645420989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1763468139888047527227985 1322601104916035645420989)
                  ·
                    refine ⟨495975414343513367032871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1322601104916035645420989 495975414343513367032871)
                    ·
                      rfl

theorem cell22_1448863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2, 3].length) (baseStart_1448863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448863 prefixEnd_1448863 := by exact prefixLift 1448863
  have htrace : WordTrace (prefixWord ++ tailWord_1448863) baseStart_1448863 baseEnd_1448863 := by
    simpa [prefixWord, tailWord_1448863, baseEnd_1448863] using wordTrace_append hprefix tailTrace_1448863
  have hstable : (prefixWord ++ tailWord_1448863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448863).length < 2 ^ (prefixWord ++ tailWord_1448863).sum := by decide
  have hdescent : baseEnd_1448863 < baseStart_1448863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448893 : List Nat := [1, 4, 1, 2, 4, 2, 2, 6]
def baseStart_1448893 : Nat := 118140960795 + 1448893 * 2 ^ 59
def prefixEnd_1448893 : Nat := 4983230072969 + 3 ^ 40 * 1448893 * 2
def baseEnd_1448893 : Nat := 55109520439622587642531

theorem tailTrace_1448893 : CollatzResearch.WordTrace tailWord_1448893 prefixEnd_1448893 55109520439622587642531 := by
  unfold tailWord_1448893
  simp only [CollatzResearch.WordTrace]
  refine ⟨52845469139915587068911333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35230312759943724712607555 52845469139915587068911333)
  ·
    refine ⟨9908525463734172575420875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52845469139915587068911333 9908525463734172575420875)
    ·
      refine ⟨14862788195601258863131313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9908525463734172575420875 14862788195601258863131313)
      ·
        refine ⟨11147091146700944147348485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14862788195601258863131313 11147091146700944147348485)
        ·
          refine ⟨2090079590006427027627841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11147091146700944147348485 2090079590006427027627841)
          ·
            refine ⟨1567559692504820270720881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2090079590006427027627841 1567559692504820270720881)
            ·
              refine ⟨1175669769378615203040661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1567559692504820270720881 1175669769378615203040661)
              ·
                refine ⟨55109520439622587642531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1175669769378615203040661 55109520439622587642531)
                ·
                  rfl

theorem cell22_1448893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 6].length) (baseStart_1448893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448893 prefixEnd_1448893 := by exact prefixLift 1448893
  have htrace : WordTrace (prefixWord ++ tailWord_1448893) baseStart_1448893 baseEnd_1448893 := by
    simpa [prefixWord, tailWord_1448893, baseEnd_1448893] using wordTrace_append hprefix tailTrace_1448893
  have hstable : (prefixWord ++ tailWord_1448893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448893).length < 2 ^ (prefixWord ++ tailWord_1448893).sum := by decide
  have hdescent : baseEnd_1448893 < baseStart_1448893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448919 : List Nat := [1, 1, 3, 2, 1, 1, 2, 4, 2, 5]
def baseStart_1448919 : Nat := 118140960795 + 1448919 * 2 ^ 59
def prefixEnd_1448919 : Nat := 4983230072969 + 3 ^ 40 * 1448919 * 2
def baseEnd_1448919 : Nat := 495994584287947887632699

theorem tailTrace_1448919 : CollatzResearch.WordTrace tailWord_1448919 prefixEnd_1448919 495994584287947887632699 := by
  unfold tailWord_1448919
  simp only [CollatzResearch.WordTrace]
  refine ⟨52846417437821393509357811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35230944958547595672905207 52846417437821393509357811)
  ·
    refine ⟨79269626156732090264036717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52846417437821393509357811 79269626156732090264036717)
    ·
      refine ⟨29726109808774533849013769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79269626156732090264036717 29726109808774533849013769)
      ·
        refine ⟨22294582356580900386760327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29726109808774533849013769 22294582356580900386760327)
        ·
          refine ⟨33441873534871350580140491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22294582356580900386760327 33441873534871350580140491)
          ·
            refine ⟨50162810302307025870210737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33441873534871350580140491 50162810302307025870210737)
            ·
              refine ⟨37622107726730269402658053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50162810302307025870210737 37622107726730269402658053)
              ·
                refine ⟨7054145198761925512998385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37622107726730269402658053 7054145198761925512998385)
                ·
                  refine ⟨5290608899071444134748789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7054145198761925512998385 5290608899071444134748789)
                  ·
                    refine ⟨495994584287947887632699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5290608899071444134748789 495994584287947887632699)
                    ·
                      rfl

theorem cell22_1448919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_1448919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448919 prefixEnd_1448919 := by exact prefixLift 1448919
  have htrace : WordTrace (prefixWord ++ tailWord_1448919) baseStart_1448919 baseEnd_1448919 := by
    simpa [prefixWord, tailWord_1448919, baseEnd_1448919] using wordTrace_append hprefix tailTrace_1448919
  have hstable : (prefixWord ++ tailWord_1448919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448919).length < 2 ^ (prefixWord ++ tailWord_1448919).sum := by decide
  have hdescent : baseEnd_1448919 < baseStart_1448919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448925 : List Nat := [1, 4, 3, 1, 2, 3, 1, 1, 3, 3]
def baseStart_1448925 : Nat := 118140960795 + 1448925 * 2 ^ 59
def prefixEnd_1448925 : Nat := 4983230072969 + 3 ^ 40 * 1448925 * 2
def baseEnd_1448925 : Nat := 495996638210565871982681

theorem tailTrace_1448925 : CollatzResearch.WordTrace tailWord_1448925 prefixEnd_1448925 495996638210565871982681 := by
  unfold tailWord_1448925
  simp only [CollatzResearch.WordTrace]
  refine ⟨52846636275799656534076229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35231090850533104356050819 52846636275799656534076229)
  ·
    refine ⟨9908744301712435600139293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52846636275799656534076229 9908744301712435600139293)
    ·
      refine ⟨3715779113142163350052235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9908744301712435600139293 3715779113142163350052235)
      ·
        refine ⟨5573668669713245025078353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3715779113142163350052235 5573668669713245025078353)
        ·
          refine ⟨4180251502284933768808765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5573668669713245025078353 4180251502284933768808765)
          ·
            refine ⟨1567594313356850163303287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4180251502284933768808765 1567594313356850163303287)
            ·
              refine ⟨2351391470035275244954931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1567594313356850163303287 2351391470035275244954931)
              ·
                refine ⟨3527087205052912867432397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2351391470035275244954931 3527087205052912867432397)
                ·
                  refine ⟨1322657701894842325287149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3527087205052912867432397 1322657701894842325287149)
                  ·
                    refine ⟨495996638210565871982681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1322657701894842325287149 495996638210565871982681)
                    ·
                      rfl

theorem cell22_1448925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_1448925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448925 prefixEnd_1448925 := by exact prefixLift 1448925
  have htrace : WordTrace (prefixWord ++ tailWord_1448925) baseStart_1448925 baseEnd_1448925 := by
    simpa [prefixWord, tailWord_1448925, baseEnd_1448925] using wordTrace_append hprefix tailTrace_1448925
  have hstable : (prefixWord ++ tailWord_1448925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448925).length < 2 ^ (prefixWord ++ tailWord_1448925).sum := by decide
  have hdescent : baseEnd_1448925 < baseStart_1448925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448938 : List Nat := [3, 1, 3, 1, 2, 2, 4, 1, 5]
def baseStart_1448938 : Nat := 118140960795 + 1448938 * 2 ^ 59
def prefixEnd_1448938 : Nat := 4983230072969 + 3 ^ 40 * 1448938 * 2
def baseEnd_1448938 : Nat := 165333696125412723802547

theorem tailTrace_1448938 : CollatzResearch.WordTrace tailWord_1448938 prefixEnd_1448938 165333696125412723802547 := by
  unfold tailWord_1448938
  simp only [CollatzResearch.WordTrace]
  refine ⟨13211777606188139938574867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35231406949835039836199645 13211777606188139938574867)
  ·
    refine ⟨19817666409282209907862301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13211777606188139938574867 19817666409282209907862301)
    ·
      refine ⟨7431624903480828715448363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19817666409282209907862301 7431624903480828715448363)
      ·
        refine ⟨11147437355221243073172545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7431624903480828715448363 11147437355221243073172545)
        ·
          refine ⟨8360578016415932304879409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11147437355221243073172545 8360578016415932304879409)
          ·
            refine ⟨6270433512311949228659557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8360578016415932304879409 6270433512311949228659557)
            ·
              refine ⟨1175706283558490480373667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6270433512311949228659557 1175706283558490480373667)
              ·
                refine ⟨1763559425337735720560501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1175706283558490480373667 1763559425337735720560501)
                ·
                  refine ⟨165333696125412723802547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1763559425337735720560501 165333696125412723802547)
                  ·
                    rfl

theorem cell22_1448938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 5].length) (baseStart_1448938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448938 prefixEnd_1448938 := by exact prefixLift 1448938
  have htrace : WordTrace (prefixWord ++ tailWord_1448938) baseStart_1448938 baseEnd_1448938 := by
    simpa [prefixWord, tailWord_1448938, baseEnd_1448938] using wordTrace_append hprefix tailTrace_1448938
  have hstable : (prefixWord ++ tailWord_1448938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448938).length < 2 ^ (prefixWord ++ tailWord_1448938).sum := by decide
  have hdescent : baseEnd_1448938 < baseStart_1448938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448979 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 3, 6]
def baseStart_1448979 : Nat := 118140960795 + 1448979 * 2 ^ 59
def prefixEnd_1448979 : Nat := 4983230072969 + 3 ^ 40 * 1448979 * 2
def baseEnd_1448979 : Nat := 496015123514127731132515

theorem tailTrace_1448979 : CollatzResearch.WordTrace tailWord_1448979 prefixEnd_1448979 496015123514127731132515 := by
  unfold tailWord_1448979
  simp only [CollatzResearch.WordTrace]
  refine ⟨52848605817604023756541991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35232403878402682504361327 52848605817604023756541991)
  ·
    refine ⟨79272908726406035634812987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52848605817604023756541991 79272908726406035634812987)
    ·
      refine ⟨118909363089609053452219481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79272908726406035634812987 118909363089609053452219481)
      ·
        refine ⟨89182022317206790089164611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118909363089609053452219481 89182022317206790089164611)
        ·
          refine ⟨133773033475810185133746917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89182022317206790089164611 133773033475810185133746917)
          ·
            refine ⟨25082443776714409712577547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133773033475810185133746917 25082443776714409712577547)
            ·
              refine ⟨37623665665071614568866321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25082443776714409712577547 37623665665071614568866321)
              ·
                refine ⟨28217749248803710926649741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37623665665071614568866321 28217749248803710926649741)
                ·
                  refine ⟨10581655968301391597493653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28217749248803710926649741 10581655968301391597493653)
                  ·
                    refine ⟨496015123514127731132515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10581655968301391597493653 496015123514127731132515)
                    ·
                      rfl

theorem cell22_1448979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 6].length) (baseStart_1448979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1448979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1448979 prefixEnd_1448979 := by exact prefixLift 1448979
  have htrace : WordTrace (prefixWord ++ tailWord_1448979) baseStart_1448979 baseEnd_1448979 := by
    simpa [prefixWord, tailWord_1448979, baseEnd_1448979] using wordTrace_append hprefix tailTrace_1448979
  have hstable : (prefixWord ++ tailWord_1448979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448979).length < 2 ^ (prefixWord ++ tailWord_1448979).sum := by decide
  have hdescent : baseEnd_1448979 < baseStart_1448979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449137 : List Nat := [1, 2, 2, 5, 1, 2, 3, 1, 1, 4]
def baseStart_1449137 : Nat := 118140960795 + 1449137 * 2 ^ 59
def prefixEnd_1449137 : Nat := 4983230072969 + 3 ^ 40 * 1449137 * 2
def baseEnd_1449137 : Nat := 496069210143067985682031

theorem tailTrace_1449137 : CollatzResearch.WordTrace tailWord_1449137 prefixEnd_1449137 496069210143067985682031 := by
  unfold tailWord_1449137
  simp only [CollatzResearch.WordTrace]
  refine ⟨52854368551031616740793665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35236245700687744493862443 52854368551031616740793665)
  ·
    refine ⟨39640776413273712555595249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52854368551031616740793665 39640776413273712555595249)
    ·
      refine ⟨29730582309955284416696437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39640776413273712555595249 29730582309955284416696437)
      ·
        refine ⟨2787242091558307914065291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29730582309955284416696437 2787242091558307914065291)
        ·
          refine ⟨4180863137337461871097937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2787242091558307914065291 4180863137337461871097937)
          ·
            refine ⟨3135647353003096403323453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4180863137337461871097937 3135647353003096403323453)
            ·
              refine ⟨1175867757376161151246295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3135647353003096403323453 1175867757376161151246295)
              ·
                refine ⟨1763801636064241726869443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1175867757376161151246295 1763801636064241726869443)
                ·
                  refine ⟨2645702454096362590304165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1763801636064241726869443 2645702454096362590304165)
                  ·
                    refine ⟨496069210143067985682031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2645702454096362590304165 496069210143067985682031)
                    ·
                      rfl

theorem cell22_1449137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 1, 4].length) (baseStart_1449137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1449137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1449137 prefixEnd_1449137 := by exact prefixLift 1449137
  have htrace : WordTrace (prefixWord ++ tailWord_1449137) baseStart_1449137 baseEnd_1449137 := by
    simpa [prefixWord, tailWord_1449137, baseEnd_1449137] using wordTrace_append hprefix tailTrace_1449137
  have hstable : (prefixWord ++ tailWord_1449137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449137).length < 2 ^ (prefixWord ++ tailWord_1449137).sum := by decide
  have hdescent : baseEnd_1449137 < baseStart_1449137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449212 : List Nat := [2, 2, 2, 1, 5, 1, 2, 1, 3, 3]
def baseStart_1449212 : Nat := 118140960795 + 1449212 * 2 ^ 59
def prefixEnd_1449212 : Nat := 4983230072969 + 3 ^ 40 * 1449212 * 2
def baseEnd_1449212 : Nat := 496094884175792790056801

theorem tailTrace_1449212 : CollatzResearch.WordTrace tailWord_1449212 prefixEnd_1449212 496094884175792790056801 := by
  unfold tailWord_1449212
  simp only [CollatzResearch.WordTrace]
  refine ⟨26428552012879952274886945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35238069350506603033182593 26428552012879952274886945)
  ·
    refine ⟨19821414009659964206165209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26428552012879952274886945 19821414009659964206165209)
    ·
      refine ⟨14866060507244973154623907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19821414009659964206165209 14866060507244973154623907)
      ·
        refine ⟨22299090760867459731935861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14866060507244973154623907 22299090760867459731935861)
        ·
          refine ⟨2090539758831324349868987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22299090760867459731935861 2090539758831324349868987)
          ·
            refine ⟨3135809638246986524803481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2090539758831324349868987 3135809638246986524803481)
            ·
              refine ⟨2351857228685239893602611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3135809638246986524803481 2351857228685239893602611)
              ·
                refine ⟨3527785843027859840403917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2351857228685239893602611 3527785843027859840403917)
                ·
                  refine ⟨1322919691135447440151469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3527785843027859840403917 1322919691135447440151469)
                  ·
                    refine ⟨496094884175792790056801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1322919691135447440151469 496094884175792790056801)
                    ·
                      rfl

theorem cell22_1449212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_1449212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1449212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1449212 prefixEnd_1449212 := by exact prefixLift 1449212
  have htrace : WordTrace (prefixWord ++ tailWord_1449212) baseStart_1449212 baseEnd_1449212 := by
    simpa [prefixWord, tailWord_1449212, baseEnd_1449212] using wordTrace_append hprefix tailTrace_1449212
  have hstable : (prefixWord ++ tailWord_1449212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449212).length < 2 ^ (prefixWord ++ tailWord_1449212).sum := by decide
  have hdescent : baseEnd_1449212 < baseStart_1449212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449225 : List Nat := [1, 2, 1, 1, 3, 3, 5, 1, 5]
def baseStart_1449225 : Nat := 118140960795 + 1449225 * 2 ^ 59
def prefixEnd_1449225 : Nat := 4983230072969 + 3 ^ 40 * 1449225 * 2
def baseEnd_1449225 : Nat := 165366444780488363160587

theorem tailTrace_1449225 : CollatzResearch.WordTrace tailWord_1449225 prefixEnd_1449225 165366444780488363160587 := by
  unfold tailWord_1449225
  simp only [CollatzResearch.WordTrace]
  refine ⟨52857578174712807769997129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35238385449808538513331419 52857578174712807769997129)
  ·
    refine ⟨39643183631034605827497847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52857578174712807769997129 39643183631034605827497847)
    ·
      refine ⟨59464775446551908741246771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39643183631034605827497847 59464775446551908741246771)
      ·
        refine ⟨89197163169827863111870157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59464775446551908741246771 89197163169827863111870157)
        ·
          refine ⟨33448936188685448666951309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89197163169827863111870157 33448936188685448666951309)
          ·
            refine ⟨12543351070757043250106741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33448936188685448666951309 12543351070757043250106741)
            ·
              refine ⟨1175939162883472804697507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12543351070757043250106741 1175939162883472804697507)
              ·
                refine ⟨1763908744325209207046261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1175939162883472804697507 1763908744325209207046261)
                ·
                  refine ⟨165366444780488363160587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1763908744325209207046261 165366444780488363160587)
                  ·
                    rfl

theorem cell22_1449225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 5].length) (baseStart_1449225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1449225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1449225 prefixEnd_1449225 := by exact prefixLift 1449225
  have htrace : WordTrace (prefixWord ++ tailWord_1449225) baseStart_1449225 baseEnd_1449225 := by
    simpa [prefixWord, tailWord_1449225, baseEnd_1449225] using wordTrace_append hprefix tailTrace_1449225
  have hstable : (prefixWord ++ tailWord_1449225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449225).length < 2 ^ (prefixWord ++ tailWord_1449225).sum := by decide
  have hdescent : baseEnd_1449225 < baseStart_1449225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449283 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 6, 4]
def baseStart_1449283 : Nat := 118140960795 + 1449283 * 2 ^ 59
def prefixEnd_1449283 : Nat := 4983230072969 + 3 ^ 40 * 1449283 * 2
def baseEnd_1449283 : Nat := 496119188926772271531583

theorem tailTrace_1449283 : CollatzResearch.WordTrace tailWord_1449283 prefixEnd_1449283 496119188926772271531583 := by
  unfold tailWord_1449283
  simp only [CollatzResearch.WordTrace]
  refine ⟨52859693608502683675608503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35239795739001789117072335 52859693608502683675608503)
  ·
    refine ⟨79289540412754025513412755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52859693608502683675608503 79289540412754025513412755)
    ·
      refine ⟨118934310619131038270119133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79289540412754025513412755 118934310619131038270119133)
      ·
        refine ⟨44600366482174139351294675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118934310619131038270119133 44600366482174139351294675)
        ·
          refine ⟨66900549723261209026942013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44600366482174139351294675 66900549723261209026942013)
          ·
            refine ⟨25087706146222953385103255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66900549723261209026942013 25087706146222953385103255)
            ·
              refine ⟨37631559219334430077654883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25087706146222953385103255 37631559219334430077654883)
              ·
                refine ⟨56447338829001645116482325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37631559219334430077654883 56447338829001645116482325)
                ·
                  refine ⟨2645969007609452114835109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56447338829001645116482325 2645969007609452114835109)
                  ·
                    refine ⟨496119188926772271531583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2645969007609452114835109 496119188926772271531583)
                    ·
                      rfl

theorem cell22_1449283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 4].length) (baseStart_1449283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1449283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1449283 prefixEnd_1449283 := by exact prefixLift 1449283
  have htrace : WordTrace (prefixWord ++ tailWord_1449283) baseStart_1449283 baseEnd_1449283 := by
    simpa [prefixWord, tailWord_1449283, baseEnd_1449283] using wordTrace_append hprefix tailTrace_1449283
  have hstable : (prefixWord ++ tailWord_1449283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449283).length < 2 ^ (prefixWord ++ tailWord_1449283).sum := by decide
  have hdescent : baseEnd_1449283 < baseStart_1449283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449319 : List Nat := [1, 1, 5, 1, 4, 1, 2, 2, 2, 3]
def baseStart_1449319 : Nat := 118140960795 + 1449319 * 2 ^ 59
def prefixEnd_1449319 : Nat := 4983230072969 + 3 ^ 40 * 1449319 * 2
def baseEnd_1449319 : Nat := 496131512462480177631473

theorem tailTrace_1449319 : CollatzResearch.WordTrace tailWord_1449319 prefixEnd_1449319 496131512462480177631473 := by
  unfold tailWord_1449319
  simp only [CollatzResearch.WordTrace]
  refine ⟨52861006636372261823919011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35240671090914841215946007 52861006636372261823919011)
  ·
    refine ⟨79291509954558392735878517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52861006636372261823919011 79291509954558392735878517)
    ·
      refine ⟨7433579058239849318988611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79291509954558392735878517 7433579058239849318988611)
      ·
        refine ⟨11150368587359773978482917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7433579058239849318988611 11150368587359773978482917)
        ·
          refine ⟨2090694110129957620965547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11150368587359773978482917 2090694110129957620965547)
          ·
            refine ⟨3136041165194936431448321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2090694110129957620965547 3136041165194936431448321)
            ·
              refine ⟨2352030873896202323586241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3136041165194936431448321 2352030873896202323586241)
              ·
                refine ⟨1764023155422151742689681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2352030873896202323586241 1764023155422151742689681)
                ·
                  refine ⟨1323017366566613807017261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1764023155422151742689681 1323017366566613807017261)
                  ·
                    refine ⟨496131512462480177631473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1323017366566613807017261 496131512462480177631473)
                    ·
                      rfl

theorem cell22_1449319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_1449319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1449319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1449319 prefixEnd_1449319 := by exact prefixLift 1449319
  have htrace : WordTrace (prefixWord ++ tailWord_1449319) baseStart_1449319 baseEnd_1449319 := by
    simpa [prefixWord, tailWord_1449319, baseEnd_1449319] using wordTrace_append hprefix tailTrace_1449319
  have hstable : (prefixWord ++ tailWord_1449319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449319).length < 2 ^ (prefixWord ++ tailWord_1449319).sum := by decide
  have hdescent : baseEnd_1449319 < baseStart_1449319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449328 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 1, 8]
def baseStart_1449328 : Nat := 118140960795 + 1449328 * 2 ^ 59
def prefixEnd_1449328 : Nat := 4983230072969 + 3 ^ 40 * 1449328 * 2
def baseEnd_1449328 : Nat := 496134593346407154156445

theorem tailTrace_1449328 : CollatzResearch.WordTrace tailWord_1449328 prefixEnd_1449328 496134593346407154156445 := by
  unfold tailWord_1449328
  simp only [CollatzResearch.WordTrace]
  refine ⟨26430667446669828180498319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35240889928893104240664425 26430667446669828180498319)
  ·
    refine ⟨39646001170004742270747479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26430667446669828180498319 39646001170004742270747479)
    ·
      refine ⟨59469001755007113406121219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39646001170004742270747479 59469001755007113406121219)
      ·
        refine ⟨89203502632510670109181829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59469001755007113406121219 89203502632510670109181829)
        ·
          refine ⟨16725656743595750645471593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89203502632510670109181829 16725656743595750645471593)
          ·
            refine ⟨12544242557696812984103695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16725656743595750645471593 12544242557696812984103695)
            ·
              refine ⟨18816363836545219476155543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12544242557696812984103695 18816363836545219476155543)
              ·
                refine ⟨28224545754817829214233315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18816363836545219476155543 28224545754817829214233315)
                ·
                  refine ⟨42336818632226743821349973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28224545754817829214233315 42336818632226743821349973)
                  ·
                    refine ⟨496134593346407154156445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42336818632226743821349973 496134593346407154156445)
                    ·
                      rfl

theorem cell22_1449328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 8].length) (baseStart_1449328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1449328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1449328 prefixEnd_1449328 := by exact prefixLift 1449328
  have htrace : WordTrace (prefixWord ++ tailWord_1449328) baseStart_1449328 baseEnd_1449328 := by
    simpa [prefixWord, tailWord_1449328, baseEnd_1449328] using wordTrace_append hprefix tailTrace_1449328
  have hstable : (prefixWord ++ tailWord_1449328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449328).length < 2 ^ (prefixWord ++ tailWord_1449328).sum := by decide
  have hdescent : baseEnd_1449328 < baseStart_1449328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449347 : List Nat := [1, 1, 1, 3, 5, 2, 1, 2, 3, 3]
def baseStart_1449347 : Nat := 118140960795 + 1449347 * 2 ^ 59
def prefixEnd_1449347 : Nat := 4983230072969 + 3 ^ 40 * 1449347 * 2
def baseEnd_1449347 : Nat := 496141097434697437931387

theorem tailTrace_1449347 : CollatzResearch.WordTrace tailWord_1449347 prefixEnd_1449347 496141097434697437931387 := by
  unfold tailWord_1449347
  simp only [CollatzResearch.WordTrace]
  refine ⟨52862027880270822605938295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35241351920180548403958863 52862027880270822605938295)
  ·
    refine ⟨79293041820406233908907443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52862027880270822605938295 79293041820406233908907443)
    ·
      refine ⟨118939562730609350863361165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79293041820406233908907443 118939562730609350863361165)
      ·
        refine ⟨44602336023978506573760437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118939562730609350863361165 44602336023978506573760437)
        ·
          refine ⟨4181469002247984991290041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44602336023978506573760437 4181469002247984991290041)
          ·
            refine ⟨3136101751685988743467531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4181469002247984991290041 3136101751685988743467531)
            ·
              refine ⟨4704152627528983115201297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3136101751685988743467531 4704152627528983115201297)
              ·
                refine ⟨3528114470646737336400973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4704152627528983115201297 3528114470646737336400973)
                ·
                  refine ⟨1323042926492526501150365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3528114470646737336400973 1323042926492526501150365)
                  ·
                    refine ⟨496141097434697437931387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1323042926492526501150365 496141097434697437931387)
                    ·
                      rfl

theorem cell22_1449347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3, 3].length) (baseStart_1449347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1449347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1449347 prefixEnd_1449347 := by exact prefixLift 1449347
  have htrace : WordTrace (prefixWord ++ tailWord_1449347) baseStart_1449347 baseEnd_1449347 := by
    simpa [prefixWord, tailWord_1449347, baseEnd_1449347] using wordTrace_append hprefix tailTrace_1449347
  have hstable : (prefixWord ++ tailWord_1449347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449347).length < 2 ^ (prefixWord ++ tailWord_1449347).sum := by decide
  have hdescent : baseEnd_1449347 < baseStart_1449347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449375 : List Nat := [1, 1, 2, 5, 1, 2, 1, 2, 2, 5]
def baseStart_1449375 : Nat := 118140960795 + 1449375 * 2 ^ 59
def prefixEnd_1449375 : Nat := 4983230072969 + 3 ^ 40 * 1449375 * 2
def baseEnd_1449375 : Nat := 496150682406914698231301

theorem tailTrace_1449375 : CollatzResearch.WordTrace tailWord_1449375 prefixEnd_1449375 496150682406914698231301 := by
  unfold tailWord_1449375
  simp only [CollatzResearch.WordTrace]
  refine ⟨52863049124169383387957579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35242032749446255591971719 52863049124169383387957579)
  ·
    refine ⟨79294573686254075081936369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52863049124169383387957579 79294573686254075081936369)
    ·
      refine ⟨59470930264690556311452277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79294573686254075081936369 59470930264690556311452277)
      ·
        refine ⟨5575399712314739654198651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59470930264690556311452277 5575399712314739654198651)
        ·
          refine ⟨8363099568472109481297977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5575399712314739654198651 8363099568472109481297977)
          ·
            refine ⟨6272324676354082110973483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8363099568472109481297977 6272324676354082110973483)
            ·
              refine ⟨9408487014531123166460225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6272324676354082110973483 9408487014531123166460225)
              ·
                refine ⟨7056365260898342374845169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9408487014531123166460225 7056365260898342374845169)
                ·
                  refine ⟨5292273945673756781133877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7056365260898342374845169 5292273945673756781133877)
                  ·
                    refine ⟨496150682406914698231301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5292273945673756781133877 496150682406914698231301)
                    ·
                      rfl

theorem cell22_1449375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 5].length) (baseStart_1449375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1449375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1449375 prefixEnd_1449375 := by exact prefixLift 1449375
  have htrace : WordTrace (prefixWord ++ tailWord_1449375) baseStart_1449375 baseEnd_1449375 := by
    simpa [prefixWord, tailWord_1449375, baseEnd_1449375] using wordTrace_append hprefix tailTrace_1449375
  have hstable : (prefixWord ++ tailWord_1449375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449375).length < 2 ^ (prefixWord ++ tailWord_1449375).sum := by decide
  have hdescent : baseEnd_1449375 < baseStart_1449375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449405 : List Nat := [1, 4, 1, 2, 2, 1, 1, 4, 6]
def baseStart_1449405 : Nat := 118140960795 + 1449405 * 2 ^ 59
def prefixEnd_1449405 : Nat := 4983230072969 + 3 ^ 40 * 1449405 * 2
def baseEnd_1449405 : Nat := 165386984006668206660403

theorem tailTrace_1449405 : CollatzResearch.WordTrace tailWord_1449405 prefixEnd_1449405 165386984006668206660403 := by
  unfold tailWord_1449405
  simp only [CollatzResearch.WordTrace]
  refine ⟨52864143314060698511549669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35242762209373799007699779 52864143314060698511549669)
  ·
    refine ⟨9912026871386380970915563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52864143314060698511549669 9912026871386380970915563)
    ·
      refine ⟨14868040307079571456373345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9912026871386380970915563 14868040307079571456373345)
      ·
        refine ⟨11151030230309678592280009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14868040307079571456373345 11151030230309678592280009)
        ·
          refine ⟨8363272672732258944210007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11151030230309678592280009 8363272672732258944210007)
          ·
            refine ⟨12544909009098388416315011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8363272672732258944210007 12544909009098388416315011)
            ·
              refine ⟨18817363513647582624472517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12544909009098388416315011 18817363513647582624472517)
              ·
                refine ⟨3528255658808921742088597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18817363513647582624472517 3528255658808921742088597)
                ·
                  refine ⟨165386984006668206660403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3528255658808921742088597 165386984006668206660403)
                  ·
                    rfl

theorem cell22_1449405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_1449405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1449405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1449405 prefixEnd_1449405 := by exact prefixLift 1449405
  have htrace : WordTrace (prefixWord ++ tailWord_1449405) baseStart_1449405 baseEnd_1449405 := by
    simpa [prefixWord, tailWord_1449405, baseEnd_1449405] using wordTrace_append hprefix tailTrace_1449405
  have hstable : (prefixWord ++ tailWord_1449405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449405).length < 2 ^ (prefixWord ++ tailWord_1449405).sum := by decide
  have hdescent : baseEnd_1449405 < baseStart_1449405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449439 : List Nat := [1, 1, 2, 3, 3, 1, 5, 2, 4]
def baseStart_1449439 : Nat := 118140960795 + 1449439 * 2 ^ 59
def prefixEnd_1449439 : Nat := 4983230072969 + 3 ^ 40 * 1449439 * 2
def baseEnd_1449439 : Nat := 165390863638279954877035

theorem tailTrace_1449439 : CollatzResearch.WordTrace tailWord_1449439 prefixEnd_1449439 165390863638279954877035 := by
  unfold tailWord_1449439
  simp only [CollatzResearch.WordTrace]
  refine ⟨52865383395937522318287371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35243588930625014878858247 52865383395937522318287371)
  ·
    refine ⟨79298075093906283477431057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52865383395937522318287371 79298075093906283477431057)
    ·
      refine ⟨59473556320429712608073293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79298075093906283477431057 59473556320429712608073293)
      ·
        refine ⟨22302583620161142228027485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59473556320429712608073293 22302583620161142228027485)
        ·
          refine ⟨8363468857560428335510307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22302583620161142228027485 8363468857560428335510307)
          ·
            refine ⟨12545203286340642503265461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8363468857560428335510307 12545203286340642503265461)
            ·
              refine ⟨1176112808094435234681137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12545203286340642503265461 1176112808094435234681137)
              ·
                refine ⟨882084606070826426010853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1176112808094435234681137 882084606070826426010853)
                ·
                  refine ⟨165390863638279954877035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 882084606070826426010853 165390863638279954877035)
                  ·
                    rfl

theorem cell22_1449439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2, 4].length) (baseStart_1449439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1449439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1449439 prefixEnd_1449439 := by exact prefixLift 1449439
  have htrace : WordTrace (prefixWord ++ tailWord_1449439) baseStart_1449439 baseEnd_1449439 := by
    simpa [prefixWord, tailWord_1449439, baseEnd_1449439] using wordTrace_append hprefix tailTrace_1449439
  have hstable : (prefixWord ++ tailWord_1449439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449439).length < 2 ^ (prefixWord ++ tailWord_1449439).sum := by decide
  have hdescent : baseEnd_1449439 < baseStart_1449439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449454 : List Nat := [4, 1, 2, 1, 2, 1, 3, 3, 2, 3]
def baseStart_1449454 : Nat := 118140960795 + 1449454 * 2 ^ 59
def prefixEnd_1449454 : Nat := 4983230072969 + 3 ^ 40 * 1449454 * 2
def baseEnd_1449454 : Nat := 496177725721384825506059

theorem tailTrace_1449454 : CollatzResearch.WordTrace tailWord_1449454 prefixEnd_1449454 496177725721384825506059 := by
  unfold tailWord_1449454
  simp only [CollatzResearch.WordTrace]
  refine ⟨6608241311360397485010427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35243953660588786586722277 6608241311360397485010427)
  ·
    refine ⟨9912361967040596227515641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6608241311360397485010427 9912361967040596227515641)
    ·
      refine ⟨7434271475280447170636731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9912361967040596227515641 7434271475280447170636731)
      ·
        refine ⟨11151407212920670755955097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7434271475280447170636731 11151407212920670755955097)
        ·
          refine ⟨8363555409690503066966323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11151407212920670755955097 8363555409690503066966323)
          ·
            refine ⟨12545333114535754600449485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8363555409690503066966323 12545333114535754600449485)
            ·
              refine ⟨4704499917950907975168557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12545333114535754600449485 4704499917950907975168557)
              ·
                refine ⟨1764187469231590490688209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4704499917950907975168557 1764187469231590490688209)
                ·
                  refine ⟨1323140601923692868016157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1764187469231590490688209 1323140601923692868016157)
                  ·
                    refine ⟨496177725721384825506059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1323140601923692868016157 496177725721384825506059)
                    ·
                      rfl

theorem cell22_1449454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_1449454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1449454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1449454 prefixEnd_1449454 := by exact prefixLift 1449454
  have htrace : WordTrace (prefixWord ++ tailWord_1449454) baseStart_1449454 baseEnd_1449454 := by
    simpa [prefixWord, tailWord_1449454, baseEnd_1449454] using wordTrace_append hprefix tailTrace_1449454
  have hstable : (prefixWord ++ tailWord_1449454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449454).length < 2 ^ (prefixWord ++ tailWord_1449454).sum := by decide
  have hdescent : baseEnd_1449454 < baseStart_1449454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449533 : List Nat := [1, 4, 1, 3, 3, 1, 2, 3, 1, 3]
def baseStart_1449533 : Nat := 118140960795 + 1449533 * 2 ^ 59
def prefixEnd_1449533 : Nat := 4983230072969 + 3 ^ 40 * 1449533 * 2
def baseEnd_1449533 : Nat := 496204769035854952780817

theorem tailTrace_1449533 : CollatzResearch.WordTrace tailWord_1449533 prefixEnd_1449533 496204769035854952780817 := by
  unfold tailWord_1449533
  simp only [CollatzResearch.WordTrace]
  refine ⟨52868811857596976372209253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35245874571731317581472835 52868811857596976372209253)
  ·
    refine ⟨9912902223299433069789235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52868811857596976372209253 9912902223299433069789235)
    ·
      refine ⟨14869353334949149604683853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9912902223299433069789235 14869353334949149604683853)
      ·
        refine ⟨5576007500605931101756445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14869353334949149604683853 5576007500605931101756445)
        ·
          refine ⟨2091002812727224163158667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5576007500605931101756445 2091002812727224163158667)
          ·
            refine ⟨3136504219090836244738001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2091002812727224163158667 3136504219090836244738001)
            ·
              refine ⟨2352378164318127183553501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3136504219090836244738001 2352378164318127183553501)
              ·
                refine ⟨882141811619297693832563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2352378164318127183553501 882141811619297693832563)
                ·
                  refine ⟨1323212717428946540748845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 882141811619297693832563 1323212717428946540748845)
                  ·
                    refine ⟨496204769035854952780817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1323212717428946540748845 496204769035854952780817)
                    ·
                      rfl

theorem cell22_1449533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_1449533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1449533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1449533 prefixEnd_1449533 := by exact prefixLift 1449533
  have htrace : WordTrace (prefixWord ++ tailWord_1449533) baseStart_1449533 baseEnd_1449533 := by
    simpa [prefixWord, tailWord_1449533, baseEnd_1449533] using wordTrace_append hprefix tailTrace_1449533
  have hstable : (prefixWord ++ tailWord_1449533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449533).length < 2 ^ (prefixWord ++ tailWord_1449533).sum := by decide
  have hdescent : baseEnd_1449533 < baseStart_1449533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449576 : List Nat := [2, 1, 4, 3, 1, 2, 2, 2, 1, 4]
def baseStart_1449576 : Nat := 118140960795 + 1449576 * 2 ^ 59
def prefixEnd_1449576 : Nat := 4983230072969 + 3 ^ 40 * 1449576 * 2
def baseEnd_1449576 : Nat := 496219488814617173955685

theorem tailTrace_1449576 : CollatzResearch.WordTrace tailWord_1449576 prefixEnd_1449576 496219488814617173955685 := by
  unfold tailWord_1449576
  simp only [CollatzResearch.WordTrace]
  refine ⟨26435190098220597358012291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35246920130960796477349721 26435190098220597358012291)
  ·
    refine ⟨39652785147330896037018437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26435190098220597358012291 39652785147330896037018437)
    ·
      refine ⟨7434897215124543006940957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39652785147330896037018437 7434897215124543006940957)
      ·
        refine ⟨2788086455671703627602859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7434897215124543006940957 2788086455671703627602859)
        ·
          refine ⟨4182129683507555441404289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2788086455671703627602859 4182129683507555441404289)
          ·
            refine ⟨3136597262630666581053217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4182129683507555441404289 3136597262630666581053217)
            ·
              refine ⟨2352447946972999935789913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3136597262630666581053217 2352447946972999935789913)
              ·
                refine ⟨1764335960229749951842435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2352447946972999935789913 1764335960229749951842435)
                ·
                  refine ⟨2646503940344624927763653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1764335960229749951842435 2646503940344624927763653)
                  ·
                    refine ⟨496219488814617173955685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2646503940344624927763653 496219488814617173955685)
                    ·
                      rfl

theorem cell22_1449576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_1449576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1449576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1449576 prefixEnd_1449576 := by exact prefixLift 1449576
  have htrace : WordTrace (prefixWord ++ tailWord_1449576) baseStart_1449576 baseEnd_1449576 := by
    simpa [prefixWord, tailWord_1449576, baseEnd_1449576] using wordTrace_append hprefix tailTrace_1449576
  have hstable : (prefixWord ++ tailWord_1449576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449576).length < 2 ^ (prefixWord ++ tailWord_1449576).sum := by decide
  have hdescent : baseEnd_1449576 < baseStart_1449576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449608 : List Nat := [2, 1, 3, 5, 2, 1, 1, 1, 6]
def baseStart_1449608 : Nat := 118140960795 + 1449608 * 2 ^ 59
def prefixEnd_1449608 : Nat := 4983230072969 + 3 ^ 40 * 1449608 * 2
def baseEnd_1449608 : Nat := 165410147689526585718529

theorem tailTrace_1449608 : CollatzResearch.WordTrace tailWord_1449608 prefixEnd_1449608 165410147689526585718529 := by
  unfold tailWord_1449608
  simp only [CollatzResearch.WordTrace]
  refine ⟨26435773666162632090594739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35247698221550176120792985 26435773666162632090594739)
  ·
    refine ⟨39653660499243948135892109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26435773666162632090594739 39653660499243948135892109)
    ·
      refine ⟨14870122687216480550959541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39653660499243948135892109 14870122687216480550959541)
      ·
        refine ⟨1394074001926545051652457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14870122687216480550959541 1394074001926545051652457)
        ·
          refine ⟨1045555501444908788739343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1394074001926545051652457 1045555501444908788739343)
          ·
            refine ⟨1568333252167363183109015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045555501444908788739343 1568333252167363183109015)
            ·
              refine ⟨2352499878251044774663523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1568333252167363183109015 2352499878251044774663523)
              ·
                refine ⟨3528749817376567161995285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2352499878251044774663523 3528749817376567161995285)
                ·
                  refine ⟨165410147689526585718529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3528749817376567161995285 165410147689526585718529)
                  ·
                    rfl

theorem cell22_1449608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 6].length) (baseStart_1449608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1449608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1449608 prefixEnd_1449608 := by exact prefixLift 1449608
  have htrace : WordTrace (prefixWord ++ tailWord_1449608) baseStart_1449608 baseEnd_1449608 := by
    simpa [prefixWord, tailWord_1449608, baseEnd_1449608] using wordTrace_append hprefix tailTrace_1449608
  have hstable : (prefixWord ++ tailWord_1449608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449608).length < 2 ^ (prefixWord ++ tailWord_1449608).sum := by decide
  have hdescent : baseEnd_1449608 < baseStart_1449608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449623 : List Nat := [1, 1, 3, 3, 2, 4, 2, 1, 2, 3]
def baseStart_1449623 : Nat := 118140960795 + 1449623 * 2 ^ 59
def prefixEnd_1449623 : Nat := 4983230072969 + 3 ^ 40 * 1449623 * 2
def baseEnd_1449623 : Nat := 496235577875124718030541

theorem tailTrace_1449623 : CollatzResearch.WordTrace tailWord_1449623 prefixEnd_1449623 496235577875124718030541 := by
  unfold tailWord_1449623
  simp only [CollatzResearch.WordTrace]
  refine ⟨52872094427270921742985523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35248062951513947828657015 52872094427270921742985523)
  ·
    refine ⟨79308141640906382614478285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52872094427270921742985523 79308141640906382614478285)
    ·
      refine ⟨29740553115339893480429357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79308141640906382614478285 29740553115339893480429357)
      ·
        refine ⟨11152707418252460055161009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29740553115339893480429357 11152707418252460055161009)
        ·
          refine ⟨8364530563689345041370757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11152707418252460055161009 8364530563689345041370757)
          ·
            refine ⟨1568349480691752195257017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8364530563689345041370757 1568349480691752195257017)
            ·
              refine ⟨1176262110518814146442763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1568349480691752195257017 1176262110518814146442763)
              ·
                refine ⟨1764393165778221219664145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1176262110518814146442763 1764393165778221219664145)
                ·
                  refine ⟨1323294874333665914748109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1764393165778221219664145 1323294874333665914748109)
                  ·
                    refine ⟨496235577875124718030541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1323294874333665914748109 496235577875124718030541)
                    ·
                      rfl

theorem cell22_1449623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 2, 3].length) (baseStart_1449623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1449623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1449623 prefixEnd_1449623 := by exact prefixLift 1449623
  have htrace : WordTrace (prefixWord ++ tailWord_1449623) baseStart_1449623 baseEnd_1449623 := by
    simpa [prefixWord, tailWord_1449623, baseEnd_1449623] using wordTrace_append hprefix tailTrace_1449623
  have hstable : (prefixWord ++ tailWord_1449623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449623).length < 2 ^ (prefixWord ++ tailWord_1449623).sum := by decide
  have hdescent : baseEnd_1449623 < baseStart_1449623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449651 : List Nat := [1, 1, 1, 2, 3, 3, 2, 5, 1, 3]
def baseStart_1449651 : Nat := 118140960795 + 1449651 * 2 ^ 59
def prefixEnd_1449651 : Nat := 4983230072969 + 3 ^ 40 * 1449651 * 2
def baseEnd_1449651 : Nat := 496245162847341978330455

theorem tailTrace_1449651 : CollatzResearch.WordTrace tailWord_1449651 prefixEnd_1449651 496245162847341978330455 := by
  unfold tailWord_1449651
  simp only [CollatzResearch.WordTrace]
  refine ⟨52873115671169482525004807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35248743780779655016669871 52873115671169482525004807)
  ·
    refine ⟨79309673506754223787507211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52873115671169482525004807 79309673506754223787507211)
    ·
      refine ⟨118964510260131335681260817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79309673506754223787507211 118964510260131335681260817)
      ·
        refine ⟨89223382695098501760945613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118964510260131335681260817 89223382695098501760945613)
        ·
          refine ⟨33458768510661938160354605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89223382695098501760945613 33458768510661938160354605)
          ·
            refine ⟨12547038191498226810132977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33458768510661938160354605 12547038191498226810132977)
            ·
              refine ⟨9410278643623670107599733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12547038191498226810132977 9410278643623670107599733)
              ·
                refine ⟨882213622839719072587475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9410278643623670107599733 882213622839719072587475)
                ·
                  refine ⟨1323320434259578608881213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 882213622839719072587475 1323320434259578608881213)
                  ·
                    refine ⟨496245162847341978330455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1323320434259578608881213 496245162847341978330455)
                    ·
                      rfl

theorem cell22_1449651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5, 1, 3].length) (baseStart_1449651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1449651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1449651 prefixEnd_1449651 := by exact prefixLift 1449651
  have htrace : WordTrace (prefixWord ++ tailWord_1449651) baseStart_1449651 baseEnd_1449651 := by
    simpa [prefixWord, tailWord_1449651, baseEnd_1449651] using wordTrace_append hprefix tailTrace_1449651
  have hstable : (prefixWord ++ tailWord_1449651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449651).length < 2 ^ (prefixWord ++ tailWord_1449651).sum := by decide
  have hdescent : baseEnd_1449651 < baseStart_1449651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449664 : List Nat := [2, 1, 1, 2, 4, 1, 4, 2, 5]
def baseStart_1449664 : Nat := 118140960795 + 1449664 * 2 ^ 59
def prefixEnd_1449664 : Nat := 4983230072969 + 3 ^ 40 * 1449664 * 2
def baseEnd_1449664 : Nat := 165416537671004759251805

theorem tailTrace_1449664 : CollatzResearch.WordTrace tailWord_1449664 prefixEnd_1449664 165416537671004759251805 := by
  unfold tailWord_1449664
  simp only [CollatzResearch.WordTrace]
  refine ⟨26436794910061192872614023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35249059880081590496818697 26436794910061192872614023)
  ·
    refine ⟨39655192365091789308921035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26436794910061192872614023 39655192365091789308921035)
    ·
      refine ⟨59482788547637683963381553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39655192365091789308921035 59482788547637683963381553)
      ·
        refine ⟨44612091410728262972536165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59482788547637683963381553 44612091410728262972536165)
        ·
          refine ⟨8364767139511549307350531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44612091410728262972536165 8364767139511549307350531)
          ·
            refine ⟨12547150709267323961025797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8364767139511549307350531 12547150709267323961025797)
            ·
              refine ⟨2352590757987623242692337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12547150709267323961025797 2352590757987623242692337)
              ·
                refine ⟨1764443068490717432019253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2352590757987623242692337 1764443068490717432019253)
                ·
                  refine ⟨165416537671004759251805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1764443068490717432019253 165416537671004759251805)
                  ·
                    rfl

theorem cell22_1449664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 5].length) (baseStart_1449664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1449664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1449664 prefixEnd_1449664 := by exact prefixLift 1449664
  have htrace : WordTrace (prefixWord ++ tailWord_1449664) baseStart_1449664 baseEnd_1449664 := by
    simpa [prefixWord, tailWord_1449664, baseEnd_1449664] using wordTrace_append hprefix tailTrace_1449664
  have hstable : (prefixWord ++ tailWord_1449664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449664).length < 2 ^ (prefixWord ++ tailWord_1449664).sum := by decide
  have hdescent : baseEnd_1449664 < baseStart_1449664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449668 : List Nat := [2, 3, 3, 1, 1, 1, 3, 4, 1, 3]
def baseStart_1449668 : Nat := 118140960795 + 1449668 * 2 ^ 59
def prefixEnd_1449668 : Nat := 4983230072969 + 3 ^ 40 * 1449668 * 2
def baseEnd_1449668 : Nat := 496250982294759600655403

theorem tailTrace_1449668 : CollatzResearch.WordTrace tailWord_1449668 prefixEnd_1449668 496250982294759600655403 := by
  unfold tailWord_1449668
  simp only [CollatzResearch.WordTrace]
  refine ⟨26436867856053947214186829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35249157141405262952249105 26436867856053947214186829)
  ·
    refine ⟨9913825446020230205320061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26436867856053947214186829 9913825446020230205320061)
    ·
      refine ⟨3717684542257586326995023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9913825446020230205320061 3717684542257586326995023)
      ·
        refine ⟨5576526813386379490492535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3717684542257586326995023 5576526813386379490492535)
        ·
          refine ⟨8364790220079569235738803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5576526813386379490492535 8364790220079569235738803)
          ·
            refine ⟨12547185330119353853608205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8364790220079569235738803 12547185330119353853608205)
            ·
              refine ⟨4705194498794757695103077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12547185330119353853608205 4705194498794757695103077)
              ·
                refine ⟨882223968524017067831827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4705194498794757695103077 882223968524017067831827)
                ·
                  refine ⟨1323335952786025601747741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 882223968524017067831827 1323335952786025601747741)
                  ·
                    refine ⟨496250982294759600655403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1323335952786025601747741 496250982294759600655403)
                    ·
                      rfl

theorem cell22_1449668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_1449668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1449668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1449668 prefixEnd_1449668 := by exact prefixLift 1449668
  have htrace : WordTrace (prefixWord ++ tailWord_1449668) baseStart_1449668 baseEnd_1449668 := by
    simpa [prefixWord, tailWord_1449668, baseEnd_1449668] using wordTrace_append hprefix tailTrace_1449668
  have hstable : (prefixWord ++ tailWord_1449668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449668).length < 2 ^ (prefixWord ++ tailWord_1449668).sum := by decide
  have hdescent : baseEnd_1449668 < baseStart_1449668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449737 : List Nat := [1, 2, 1, 1, 3, 2, 1, 11]
def baseStart_1449737 : Nat := 118140960795 + 1449737 * 2 ^ 59
def prefixEnd_1449737 : Nat := 4983230072969 + 3 ^ 40 * 1449737 * 2
def baseEnd_1449737 : Nat := 55141622489429602297799

theorem tailTrace_1449737 : CollatzResearch.WordTrace tailWord_1449737 prefixEnd_1449737 55141622489429602297799 := by
  unfold tailWord_1449737
  simp only [CollatzResearch.WordTrace]
  refine ⟨52876252348857919212635465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35250834899238612808423643 52876252348857919212635465)
  ·
    refine ⟨39657189261643439409476599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52876252348857919212635465 39657189261643439409476599)
    ·
      refine ⟨59485783892465159114214899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39657189261643439409476599 59485783892465159114214899)
      ·
        refine ⟨89228675838697738671322349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59485783892465159114214899 89228675838697738671322349)
        ·
          refine ⟨33460753439511652001745881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89228675838697738671322349 33460753439511652001745881)
          ·
            refine ⟨25095565079633739001309411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33460753439511652001745881 25095565079633739001309411)
            ·
              refine ⟨37643347619450608501964117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25095565079633739001309411 37643347619450608501964117)
              ·
                refine ⟨55141622489429602297799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 37643347619450608501964117 55141622489429602297799)
                ·
                  rfl

theorem cell22_1449737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 11].length) (baseStart_1449737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1449737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1449737 prefixEnd_1449737 := by exact prefixLift 1449737
  have htrace : WordTrace (prefixWord ++ tailWord_1449737) baseStart_1449737 baseEnd_1449737 := by
    simpa [prefixWord, tailWord_1449737, baseEnd_1449737] using wordTrace_append hprefix tailTrace_1449737
  have hstable : (prefixWord ++ tailWord_1449737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449737).length < 2 ^ (prefixWord ++ tailWord_1449737).sum := by decide
  have hdescent : baseEnd_1449737 < baseStart_1449737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449754 : List Nat := [3, 1, 1, 3, 2, 3, 1, 8]
def baseStart_1449754 : Nat := 118140960795 + 1449754 * 2 ^ 59
def prefixEnd_1449754 : Nat := 4983230072969 + 3 ^ 40 * 1449754 * 2
def baseEnd_1449754 : Nat := 55142269094698227000571

theorem tailTrace_1449754 : CollatzResearch.WordTrace tailWord_1449754 prefixEnd_1449754 55142269094698227000571 := by
  unfold tailWord_1449754
  simp only [CollatzResearch.WordTrace]
  refine ⟨13219218097449082779001079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35251248259864220744002877 13219218097449082779001079)
  ·
    refine ⟨19828827146173624168501619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13219218097449082779001079 19828827146173624168501619)
    ·
      refine ⟨29743240719260436252752429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19828827146173624168501619 29743240719260436252752429)
      ·
        refine ⟨11153715269722663594782161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29743240719260436252752429 11153715269722663594782161)
        ·
          refine ⟨8365286452291997696086621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11153715269722663594782161 8365286452291997696086621)
          ·
            refine ⟨3136982419609499136032483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8365286452291997696086621 3136982419609499136032483)
            ·
              refine ⟨4705473629414248704048725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3136982419609499136032483 4705473629414248704048725)
              ·
                refine ⟨55142269094698227000571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4705473629414248704048725 55142269094698227000571)
                ·
                  rfl

theorem cell22_1449754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 8].length) (baseStart_1449754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1449754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1449754 prefixEnd_1449754 := by exact prefixLift 1449754
  have htrace : WordTrace (prefixWord ++ tailWord_1449754) baseStart_1449754 baseEnd_1449754 := by
    simpa [prefixWord, tailWord_1449754, baseEnd_1449754] using wordTrace_append hprefix tailTrace_1449754
  have hstable : (prefixWord ++ tailWord_1449754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449754).length < 2 ^ (prefixWord ++ tailWord_1449754).sum := by decide
  have hdescent : baseEnd_1449754 < baseStart_1449754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449880 : List Nat := [2, 1, 2, 6, 1, 1, 1, 3, 1, 4]
def baseStart_1449880 : Nat := 118140960795 + 1449880 * 2 ^ 59
def prefixEnd_1449880 : Nat := 4983230072969 + 3 ^ 40 * 1449880 * 2
def baseEnd_1449880 : Nat := 496323554227261714354753

theorem tailTrace_1449880 : CollatzResearch.WordTrace tailWord_1449880 prefixEnd_1449880 496323554227261714354753 := by
  unfold tailWord_1449880
  simp only [CollatzResearch.WordTrace]
  refine ⟨26440733993669927317545547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35254311991559903090060729 26440733993669927317545547)
  ·
    refine ⟨39661100990504890976318321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26440733993669927317545547 39661100990504890976318321)
    ·
      refine ⟨29745825742878668232238741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39661100990504890976318321 29745825742878668232238741)
      ·
        refine ⟨1394335581697437573386191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29745825742878668232238741 1394335581697437573386191)
        ·
          refine ⟨2091503372546156360079287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1394335581697437573386191 2091503372546156360079287)
          ·
            refine ⟨3137255058819234540118931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2091503372546156360079287 3137255058819234540118931)
            ·
              refine ⟨4705882588228851810178397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3137255058819234540118931 4705882588228851810178397)
              ·
                refine ⟨1764705970585819428816899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4705882588228851810178397 1764705970585819428816899)
                ·
                  refine ⟨2647058955878729143225349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1764705970585819428816899 2647058955878729143225349)
                  ·
                    refine ⟨496323554227261714354753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2647058955878729143225349 496323554227261714354753)
                    ·
                      rfl

theorem cell22_1449880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 1, 4].length) (baseStart_1449880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1449880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1449880 prefixEnd_1449880 := by exact prefixLift 1449880
  have htrace : WordTrace (prefixWord ++ tailWord_1449880) baseStart_1449880 baseEnd_1449880 := by
    simpa [prefixWord, tailWord_1449880, baseEnd_1449880] using wordTrace_append hprefix tailTrace_1449880
  have hstable : (prefixWord ++ tailWord_1449880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449880).length < 2 ^ (prefixWord ++ tailWord_1449880).sum := by decide
  have hdescent : baseEnd_1449880 < baseStart_1449880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449951 : List Nat := [1, 1, 2, 3, 4, 1, 2, 1, 7]
def baseStart_1449951 : Nat := 118140960795 + 1449951 * 2 ^ 59
def prefixEnd_1449951 : Nat := 4983230072969 + 3 ^ 40 * 1449951 * 2
def baseEnd_1449951 : Nat := 165449286326080398609845

theorem tailTrace_1449951 : CollatzResearch.WordTrace tailWord_1449951 prefixEnd_1449951 165449286326080398609845 := by
  unfold tailWord_1449951
  simp only [CollatzResearch.WordTrace]
  refine ⟨52884057570082633760925707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35256038380055089173950471 52884057570082633760925707)
  ·
    refine ⟨79326086355123950641388561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52884057570082633760925707 79326086355123950641388561)
    ·
      refine ⟨59494564766342962981041421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79326086355123950641388561 59494564766342962981041421)
      ·
        refine ⟨22310461787378611117890533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59494564766342962981041421 22310461787378611117890533)
        ·
          refine ⟨4183211585133489584604475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22310461787378611117890533 4183211585133489584604475)
          ·
            refine ⟨6274817377700234376906713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4183211585133489584604475 6274817377700234376906713)
            ·
              refine ⟨4706113033275175782680035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6274817377700234376906713 4706113033275175782680035)
              ·
                refine ⟨7059169549912763674020053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4706113033275175782680035 7059169549912763674020053)
                ·
                  refine ⟨165449286326080398609845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7059169549912763674020053 165449286326080398609845)
                  ·
                    rfl

theorem cell22_1449951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 7].length) (baseStart_1449951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1449951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1449951 prefixEnd_1449951 := by exact prefixLift 1449951
  have htrace : WordTrace (prefixWord ++ tailWord_1449951) baseStart_1449951 baseEnd_1449951 := by
    simpa [prefixWord, tailWord_1449951, baseEnd_1449951] using wordTrace_append hprefix tailTrace_1449951
  have hstable : (prefixWord ++ tailWord_1449951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449951).length < 2 ^ (prefixWord ++ tailWord_1449951).sum := by decide
  have hdescent : baseEnd_1449951 < baseStart_1449951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449955 : List Nat := [1, 1, 1, 6, 1, 4, 1, 1, 3, 3]
def baseStart_1449955 : Nat := 118140960795 + 1449955 * 2 ^ 59
def prefixEnd_1449955 : Nat := 4983230072969 + 3 ^ 40 * 1449955 * 2
def baseEnd_1449955 : Nat := 496349228259986518729523

theorem tailTrace_1449955 : CollatzResearch.WordTrace tailWord_1449955 prefixEnd_1449955 496349228259986518729523 := by
  unfold tailWord_1449955
  simp only [CollatzResearch.WordTrace]
  refine ⟨52884203462068142444071319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35256135641378761629380879 52884203462068142444071319)
  ·
    refine ⟨79326305193102213666106979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52884203462068142444071319 79326305193102213666106979)
    ·
      refine ⟨118989457789653320499160469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79326305193102213666106979 118989457789653320499160469)
      ·
        refine ⟨5577630833889999398398147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 118989457789653320499160469 5577630833889999398398147)
        ·
          refine ⟨8366446250834999097597221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5577630833889999398398147 8366446250834999097597221)
          ·
            refine ⟨1568708672031562330799479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8366446250834999097597221 1568708672031562330799479)
            ·
              refine ⟨2353063008047343496199219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1568708672031562330799479 2353063008047343496199219)
              ·
                refine ⟨3529594512071015244298829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2353063008047343496199219 3529594512071015244298829)
                ·
                  refine ⟨1323597942026630716612061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3529594512071015244298829 1323597942026630716612061)
                  ·
                    refine ⟨496349228259986518729523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1323597942026630716612061 496349228259986518729523)
                    ·
                      rfl

theorem cell22_1449955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3, 3].length) (baseStart_1449955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1449955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1449955 prefixEnd_1449955 := by exact prefixLift 1449955
  have htrace : WordTrace (prefixWord ++ tailWord_1449955) baseStart_1449955 baseEnd_1449955 := by
    simpa [prefixWord, tailWord_1449955, baseEnd_1449955] using wordTrace_append hprefix tailTrace_1449955
  have hstable : (prefixWord ++ tailWord_1449955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449955).length < 2 ^ (prefixWord ++ tailWord_1449955).sum := by decide
  have hdescent : baseEnd_1449955 < baseStart_1449955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449968 : List Nat := [2, 1, 1, 1, 3, 2, 6, 1, 5]
def baseStart_1449968 : Nat := 118140960795 + 1449968 * 2 ^ 59
def prefixEnd_1449968 : Nat := 4983230072969 + 3 ^ 40 * 1449968 * 2
def baseEnd_1449968 : Nat := 165451226141886272718161

theorem tailTrace_1449968 : CollatzResearch.WordTrace tailWord_1449968 prefixEnd_1449968 165451226141886272718161 := by
  unfold tailWord_1449968
  simp only [CollatzResearch.WordTrace]
  refine ⟨26442338805510522832147279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35256451740680697109529705 26442338805510522832147279)
  ·
    refine ⟨39663508208265784248220919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26442338805510522832147279 39663508208265784248220919)
    ·
      refine ⟨59495262312398676372331379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39663508208265784248220919 59495262312398676372331379)
      ·
        refine ⟨89242893468598014558497069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59495262312398676372331379 89242893468598014558497069)
        ·
          refine ⟨33466085050724255459436401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89242893468598014558497069 33466085050724255459436401)
          ·
            refine ⟨25099563788043191594577301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33466085050724255459436401 25099563788043191594577301)
            ·
              refine ⟨1176542052564524605995811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25099563788043191594577301 1176542052564524605995811)
              ·
                refine ⟨1764813078846786908993717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1176542052564524605995811 1764813078846786908993717)
                ·
                  refine ⟨165451226141886272718161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1764813078846786908993717 165451226141886272718161)
                  ·
                    rfl

theorem cell22_1449968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 5].length) (baseStart_1449968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1449968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1449968 prefixEnd_1449968 := by exact prefixLift 1449968
  have htrace : WordTrace (prefixWord ++ tailWord_1449968) baseStart_1449968 baseEnd_1449968 := by
    simpa [prefixWord, tailWord_1449968, baseEnd_1449968] using wordTrace_append hprefix tailTrace_1449968
  have hstable : (prefixWord ++ tailWord_1449968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449968).length < 2 ^ (prefixWord ++ tailWord_1449968).sum := by decide
  have hdescent : baseEnd_1449968 < baseStart_1449968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450062 : List Nat := [4, 1, 1, 1, 1, 6, 1, 2, 2, 3]
def baseStart_1450062 : Nat := 118140960795 + 1450062 * 2 ^ 59
def prefixEnd_1450062 : Nat := 4983230072969 + 3 ^ 40 * 1450062 * 2
def baseEnd_1450062 : Nat := 496385856546673906304195

theorem tailTrace_1450062 : CollatzResearch.WordTrace tailWord_1450062 prefixEnd_1450062 496385856546673906304195 := by
  unfold tailWord_1450062
  simp only [CollatzResearch.WordTrace]
  refine ⟨6611013259085062464777055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35258737381786999812144293 6611013259085062464777055)
  ·
    refine ⟨9916519888627593697165583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6611013259085062464777055 9916519888627593697165583)
    ·
      refine ⟨14874779832941390545748375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9916519888627593697165583 14874779832941390545748375)
      ·
        refine ⟨22312169749412085818622563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14874779832941390545748375 22312169749412085818622563)
        ·
          refine ⟨33468254624118128727933845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22312169749412085818622563 33468254624118128727933845)
          ·
            refine ⟨1568824435505537284121899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33468254624118128727933845 1568824435505537284121899)
            ·
              refine ⟨2353236653258305926182849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1568824435505537284121899 2353236653258305926182849)
              ·
                refine ⟨1764927489943729444637137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2353236653258305926182849 1764927489943729444637137)
                ·
                  refine ⟨1323695617457797083477853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1764927489943729444637137 1323695617457797083477853)
                  ·
                    refine ⟨496385856546673906304195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1323695617457797083477853 496385856546673906304195)
                    ·
                      rfl

theorem cell22_1450062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_1450062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1450062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1450062 prefixEnd_1450062 := by exact prefixLift 1450062
  have htrace : WordTrace (prefixWord ++ tailWord_1450062) baseStart_1450062 baseEnd_1450062 := by
    simpa [prefixWord, tailWord_1450062, baseEnd_1450062] using wordTrace_append hprefix tailTrace_1450062
  have hstable : (prefixWord ++ tailWord_1450062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450062).length < 2 ^ (prefixWord ++ tailWord_1450062).sum := by decide
  have hdescent : baseEnd_1450062 < baseStart_1450062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450071 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 1, 8]
def baseStart_1450071 : Nat := 118140960795 + 1450071 * 2 ^ 59
def prefixEnd_1450071 : Nat := 4983230072969 + 3 ^ 40 * 1450071 * 2
def baseEnd_1450071 : Nat := 496388937430600882829167

theorem tailTrace_1450071 : CollatzResearch.WordTrace tailWord_1450071 prefixEnd_1450071 496388937430600882829167 := by
  unfold tailWord_1450071
  simp only [CollatzResearch.WordTrace]
  refine ⟨52888434329647894255294067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35258956219765262836862711 52888434329647894255294067)
  ·
    refine ⟨79332651494471841382941101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52888434329647894255294067 79332651494471841382941101)
    ·
      refine ⟨29749744310426940518602913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79332651494471841382941101 29749744310426940518602913)
      ·
        refine ⟨22312308232820205388952185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29749744310426940518602913 22312308232820205388952185)
        ·
          refine ⟨16734231174615154041714139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22312308232820205388952185 16734231174615154041714139)
          ·
            refine ⟨25101346761922731062571209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16734231174615154041714139 25101346761922731062571209)
            ·
              refine ⟨18826010071442048296928407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25101346761922731062571209 18826010071442048296928407)
              ·
                refine ⟨28239015107163072445392611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18826010071442048296928407 28239015107163072445392611)
                ·
                  refine ⟨42358522660744608668088917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28239015107163072445392611 42358522660744608668088917)
                  ·
                    refine ⟨496388937430600882829167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42358522660744608668088917 496388937430600882829167)
                    ·
                      rfl

theorem cell22_1450071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_1450071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1450071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1450071 prefixEnd_1450071 := by exact prefixLift 1450071
  have htrace : WordTrace (prefixWord ++ tailWord_1450071) baseStart_1450071 baseEnd_1450071 := by
    simpa [prefixWord, tailWord_1450071, baseEnd_1450071] using wordTrace_append hprefix tailTrace_1450071
  have hstable : (prefixWord ++ tailWord_1450071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450071).length < 2 ^ (prefixWord ++ tailWord_1450071).sum := by decide
  have hdescent : baseEnd_1450071 < baseStart_1450071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450133 : List Nat := [1, 3, 2, 1, 1, 1, 4, 2, 3, 4]
def baseStart_1450133 : Nat := 118140960795 + 1450133 * 2 ^ 59
def prefixEnd_1450133 : Nat := 4983230072969 + 3 ^ 40 * 1450133 * 2
def baseEnd_1450133 : Nat := 496410161297653387778977

theorem tailTrace_1450133 : CollatzResearch.WordTrace tailWord_1450133 prefixEnd_1450133 496410161297653387778977 := by
  unfold tailWord_1450133
  simp only [CollatzResearch.WordTrace]
  refine ⟨52890695655423278844051053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35260463770282185896034035 52890695655423278844051053)
  ·
    refine ⟨19834010870783729566519145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52890695655423278844051053 19834010870783729566519145)
    ·
      refine ⟨14875508153087797174889359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19834010870783729566519145 14875508153087797174889359)
      ·
        refine ⟨22313262229631695762334039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14875508153087797174889359 22313262229631695762334039)
        ·
          refine ⟨33469893344447543643501059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22313262229631695762334039 33469893344447543643501059)
          ·
            refine ⟨50204840016671315465251589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33469893344447543643501059 50204840016671315465251589)
            ·
              refine ⟨9413407503125871649734673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50204840016671315465251589 9413407503125871649734673)
              ·
                refine ⟨7060055627344403737301005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9413407503125871649734673 7060055627344403737301005)
                ·
                  refine ⟨2647520860254151401487877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7060055627344403737301005 2647520860254151401487877)
                  ·
                    refine ⟨496410161297653387778977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2647520860254151401487877 496410161297653387778977)
                    ·
                      rfl

theorem cell22_1450133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_1450133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1450133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1450133 prefixEnd_1450133 := by exact prefixLift 1450133
  have htrace : WordTrace (prefixWord ++ tailWord_1450133) baseStart_1450133 baseEnd_1450133 := by
    simpa [prefixWord, tailWord_1450133, baseEnd_1450133] using wordTrace_append hprefix tailTrace_1450133
  have hstable : (prefixWord ++ tailWord_1450133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450133).length < 2 ^ (prefixWord ++ tailWord_1450133).sum := by decide
  have hdescent : baseEnd_1450133 < baseStart_1450133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450167 : List Nat := [1, 1, 3, 1, 4, 3, 3, 1, 1, 4]
def baseStart_1450167 : Nat := 118140960795 + 1450167 * 2 ^ 59
def prefixEnd_1450167 : Nat := 4983230072969 + 3 ^ 40 * 1450167 * 2
def baseEnd_1450167 : Nat := 496421800192488632428873

theorem tailTrace_1450167 : CollatzResearch.WordTrace tailWord_1450167 prefixEnd_1450167 496421800192488632428873 := by
  unfold tailWord_1450167
  simp only [CollatzResearch.WordTrace]
  refine ⟨52891935737300102650788755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35261290491533401767192503 52891935737300102650788755)
  ·
    refine ⟨79337903605950153976183133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52891935737300102650788755 79337903605950153976183133)
    ·
      refine ⟨29751713852231307741068675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79337903605950153976183133 29751713852231307741068675)
      ·
        refine ⟨44627570778346961611603013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29751713852231307741068675 44627570778346961611603013)
        ·
          refine ⟨8367669520940055302175565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44627570778346961611603013 8367669520940055302175565)
          ·
            refine ⟨3137876070352520738315837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8367669520940055302175565 3137876070352520738315837)
            ·
              refine ⟨1176703526382195276868439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3137876070352520738315837 1176703526382195276868439)
              ·
                refine ⟨1765055289573292915302659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1176703526382195276868439 1765055289573292915302659)
                ·
                  refine ⟨2647582934359939372953989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1765055289573292915302659 2647582934359939372953989)
                  ·
                    refine ⟨496421800192488632428873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2647582934359939372953989 496421800192488632428873)
                    ·
                      rfl

theorem cell22_1450167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 1, 4].length) (baseStart_1450167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1450167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1450167 prefixEnd_1450167 := by exact prefixLift 1450167
  have htrace : WordTrace (prefixWord ++ tailWord_1450167) baseStart_1450167 baseEnd_1450167 := by
    simpa [prefixWord, tailWord_1450167, baseEnd_1450167] using wordTrace_append hprefix tailTrace_1450167
  have hstable : (prefixWord ++ tailWord_1450167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450167).length < 2 ^ (prefixWord ++ tailWord_1450167).sum := by decide
  have hdescent : baseEnd_1450167 < baseStart_1450167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450193 : List Nat := [1, 2, 2, 1, 2, 2, 5, 7]
def baseStart_1450193 : Nat := 118140960795 + 1450193 * 2 ^ 59
def prefixEnd_1450193 : Nat := 4983230072969 + 3 ^ 40 * 1450193 * 2
def baseEnd_1450193 : Nat := 55158966724870359030977

theorem tailTrace_1450193 : CollatzResearch.WordTrace tailWord_1450193 prefixEnd_1450193 55158966724870359030977 := by
  unfold tailWord_1450193
  simp only [CollatzResearch.WordTrace]
  refine ⟨52892884035205909091235233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35261922690137272727490155 52892884035205909091235233)
  ·
    refine ⟨39669663026404431818426425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52892884035205909091235233 39669663026404431818426425)
    ·
      refine ⟨29752247269803323863819819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39669663026404431818426425 29752247269803323863819819)
      ·
        refine ⟨44628370904704985795729729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29752247269803323863819819 44628370904704985795729729)
        ·
          refine ⟨33471278178528739346797297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44628370904704985795729729 33471278178528739346797297)
          ·
            refine ⟨25103458633896554510097973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33471278178528739346797297 25103458633896554510097973)
            ·
              refine ⟨2353449246927801985321685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25103458633896554510097973 2353449246927801985321685)
              ·
                refine ⟨55158966724870359030977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2353449246927801985321685 55158966724870359030977)
                ·
                  rfl

theorem cell22_1450193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 7].length) (baseStart_1450193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1450193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1450193 prefixEnd_1450193 := by exact prefixLift 1450193
  have htrace : WordTrace (prefixWord ++ tailWord_1450193) baseStart_1450193 baseEnd_1450193 := by
    simpa [prefixWord, tailWord_1450193, baseEnd_1450193] using wordTrace_append hprefix tailTrace_1450193
  have hstable : (prefixWord ++ tailWord_1450193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450193).length < 2 ^ (prefixWord ++ tailWord_1450193).sum := by decide
  have hdescent : baseEnd_1450193 < baseStart_1450193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450197 : List Nat := [1, 3, 2, 4, 2, 1, 2, 1, 1, 5]
def baseStart_1450197 : Nat := 118140960795 + 1450197 * 2 ^ 59
def prefixEnd_1450197 : Nat := 4983230072969 + 3 ^ 40 * 1450197 * 2
def baseEnd_1450197 : Nat := 496432069805578554178781

theorem tailTrace_1450197 : CollatzResearch.WordTrace tailWord_1450197 prefixEnd_1450197 496432069805578554178781 := by
  unfold tailWord_1450197
  simp only [CollatzResearch.WordTrace]
  refine ⟨52893029927191417774380845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35262019951460945182920563 52893029927191417774380845)
  ·
    refine ⟨19834886222696781665392817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52893029927191417774380845 19834886222696781665392817)
    ·
      refine ⟨14876164667022586249044613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19834886222696781665392817 14876164667022586249044613)
      ·
        refine ⟨2789280875066734921695865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14876164667022586249044613 2789280875066734921695865)
        ·
          refine ⟨2091960656300051191271899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2789280875066734921695865 2091960656300051191271899)
          ·
            refine ⟨3137940984450076786907849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2091960656300051191271899 3137940984450076786907849)
            ·
              refine ⟨2353455738337557590180887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3137940984450076786907849 2353455738337557590180887)
              ·
                refine ⟨3530183607506336385271331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2353455738337557590180887 3530183607506336385271331)
                ·
                  refine ⟨5295275411259504577906997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3530183607506336385271331 5295275411259504577906997)
                  ·
                    refine ⟨496432069805578554178781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5295275411259504577906997 496432069805578554178781)
                    ·
                      rfl

theorem cell22_1450197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_1450197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1450197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1450197 prefixEnd_1450197 := by exact prefixLift 1450197
  have htrace : WordTrace (prefixWord ++ tailWord_1450197) baseStart_1450197 baseEnd_1450197 := by
    simpa [prefixWord, tailWord_1450197, baseEnd_1450197] using wordTrace_append hprefix tailTrace_1450197
  have hstable : (prefixWord ++ tailWord_1450197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450197).length < 2 ^ (prefixWord ++ tailWord_1450197).sum := by decide
  have hdescent : baseEnd_1450197 < baseStart_1450197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450276 : List Nat := [2, 3, 1, 3, 1, 4, 1, 3, 1, 3]
def baseStart_1450276 : Nat := 118140960795 + 1450276 * 2 ^ 59
def prefixEnd_1450276 : Nat := 4983230072969 + 3 ^ 40 * 1450276 * 2
def baseEnd_1450276 : Nat := 496459113120048681453539

theorem tailTrace_1450276 : CollatzResearch.WordTrace tailWord_1450276 prefixEnd_1450276 496459113120048681453539 := by
  unfold tailWord_1450276
  simp only [CollatzResearch.WordTrace]
  refine ⟨26447955646952607133253341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35263940862603476177671121 26447955646952607133253341)
  ·
    refine ⟨9917983367607227674970003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26447955646952607133253341 9917983367607227674970003)
    ·
      refine ⟨14876975051410841512455005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9917983367607227674970003 14876975051410841512455005)
      ·
        refine ⟨5578865644279065567170627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14876975051410841512455005 5578865644279065567170627)
        ·
          refine ⟨8368298466418598350755941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5578865644279065567170627 8368298466418598350755941)
          ·
            refine ⟨1569055962453487190766739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8368298466418598350755941 1569055962453487190766739)
            ·
              refine ⟨2353583943680230786150109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1569055962453487190766739 2353583943680230786150109)
              ·
                refine ⟨882593978880086544806291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2353583943680230786150109 882593978880086544806291)
                ·
                  refine ⟨1323890968320129817209437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 882593978880086544806291 1323890968320129817209437)
                  ·
                    refine ⟨496459113120048681453539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1323890968320129817209437 496459113120048681453539)
                    ·
                      rfl

theorem cell22_1450276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_1450276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1450276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1450276 prefixEnd_1450276 := by exact prefixLift 1450276
  have htrace : WordTrace (prefixWord ++ tailWord_1450276) baseStart_1450276 baseEnd_1450276 := by
    simpa [prefixWord, tailWord_1450276, baseEnd_1450276] using wordTrace_append hprefix tailTrace_1450276
  have hstable : (prefixWord ++ tailWord_1450276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450276).length < 2 ^ (prefixWord ++ tailWord_1450276).sum := by decide
  have hdescent : baseEnd_1450276 < baseStart_1450276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450315 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 6, 3]
def baseStart_1450315 : Nat := 118140960795 + 1450315 * 2 ^ 59
def prefixEnd_1450315 : Nat := 4983230072969 + 3 ^ 40 * 1450315 * 2
def baseEnd_1450315 : Nat := 496472463617065579728419

theorem tailTrace_1450315 : CollatzResearch.WordTrace tailWord_1450315 prefixEnd_1450315 496472463617065579728419 := by
  unfold tailWord_1450315
  simp only [CollatzResearch.WordTrace]
  refine ⟨52897333740763923927176399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35264889160509282618117599 52897333740763923927176399)
  ·
    refine ⟨79346000611145885890764599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52897333740763923927176399 79346000611145885890764599)
    ·
      refine ⟨119019000916718828836146899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79346000611145885890764599 119019000916718828836146899)
      ·
        refine ⟨178528501375078243254220349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119019000916718828836146899 178528501375078243254220349)
        ·
          refine ⟨66948188015654341220332631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178528501375078243254220349 66948188015654341220332631)
          ·
            refine ⟨100422282023481511830498947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66948188015654341220332631 100422282023481511830498947)
            ·
              refine ⟨150633423035222267745748421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100422282023481511830498947 150633423035222267745748421)
              ·
                refine ⟨28243766819104175202327829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150633423035222267745748421 28243766819104175202327829)
                ·
                  refine ⟨1323926569645508212609117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28243766819104175202327829 1323926569645508212609117)
                  ·
                    refine ⟨496472463617065579728419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1323926569645508212609117 496472463617065579728419)
                    ·
                      rfl

theorem cell22_1450315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6, 3].length) (baseStart_1450315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1450315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1450315 prefixEnd_1450315 := by exact prefixLift 1450315
  have htrace : WordTrace (prefixWord ++ tailWord_1450315) baseStart_1450315 baseEnd_1450315 := by
    simpa [prefixWord, tailWord_1450315, baseEnd_1450315] using wordTrace_append hprefix tailTrace_1450315
  have hstable : (prefixWord ++ tailWord_1450315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450315).length < 2 ^ (prefixWord ++ tailWord_1450315).sum := by decide
  have hdescent : baseEnd_1450315 < baseStart_1450315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450349 : List Nat := [1, 5, 1, 1, 1, 2, 4, 2, 2, 3]
def baseStart_1450349 : Nat := 118140960795 + 1450349 * 2 ^ 59
def prefixEnd_1450349 : Nat := 4983230072969 + 3 ^ 40 * 1450349 * 2
def baseEnd_1450349 : Nat := 496484102511900824378315

theorem tailTrace_1450349 : CollatzResearch.WordTrace tailWord_1450349 prefixEnd_1450349 496484102511900824378315 := by
  unfold tailWord_1450349
  simp only [CollatzResearch.WordTrace]
  refine ⟨52898573822640747733914101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35265715881760498489276067 52898573822640747733914101)
  ·
    refine ⟨4959241295872570100054447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52898573822640747733914101 4959241295872570100054447)
    ·
      refine ⟨7438861943808855150081671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4959241295872570100054447 7438861943808855150081671)
      ·
        refine ⟨11158292915713282725122507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7438861943808855150081671 11158292915713282725122507)
        ·
          refine ⟨16737439373569924087683761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11158292915713282725122507 16737439373569924087683761)
          ·
            refine ⟨12553079530177443065762821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16737439373569924087683761 12553079530177443065762821)
            ·
              refine ⟨2353702411908270574830529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12553079530177443065762821 2353702411908270574830529)
              ·
                refine ⟨1765276808931202931122897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2353702411908270574830529 1765276808931202931122897)
                ·
                  refine ⟨1323957606698402198342173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1765276808931202931122897 1323957606698402198342173)
                  ·
                    refine ⟨496484102511900824378315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1323957606698402198342173 496484102511900824378315)
                    ·
                      rfl

theorem cell22_1450349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_1450349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1450349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1450349 prefixEnd_1450349 := by exact prefixLift 1450349
  have htrace : WordTrace (prefixWord ++ tailWord_1450349) baseStart_1450349 baseEnd_1450349 := by
    simpa [prefixWord, tailWord_1450349, baseEnd_1450349] using wordTrace_append hprefix tailTrace_1450349
  have hstable : (prefixWord ++ tailWord_1450349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450349).length < 2 ^ (prefixWord ++ tailWord_1450349).sum := by decide
  have hdescent : baseEnd_1450349 < baseStart_1450349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450375 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 2, 6]
def baseStart_1450375 : Nat := 118140960795 + 1450375 * 2 ^ 59
def prefixEnd_1450375 : Nat := 4983230072969 + 3 ^ 40 * 1450375 * 2
def baseEnd_1450375 : Nat := 496493002843245423228235

theorem tailTrace_1450375 : CollatzResearch.WordTrace tailWord_1450375 prefixEnd_1450375 496493002843245423228235 := by
  unfold tailWord_1450375
  simp only [CollatzResearch.WordTrace]
  refine ⟨52899522120546554174360579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35266348080364369449573719 52899522120546554174360579)
  ·
    refine ⟨79349283180819831261540869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52899522120546554174360579 79349283180819831261540869)
    ·
      refine ⟨14877990596403718361538913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79349283180819831261540869 14877990596403718361538913)
      ·
        refine ⟨11158492947302788771154185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14877990596403718361538913 11158492947302788771154185)
        ·
          refine ⟨8368869710477091578365639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11158492947302788771154185 8368869710477091578365639)
          ·
            refine ⟨12553304565715637367548459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8368869710477091578365639 12553304565715637367548459)
            ·
              refine ⟨18829956848573456051322689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12553304565715637367548459 18829956848573456051322689)
              ·
                refine ⟨14122467636430092038492017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18829956848573456051322689 14122467636430092038492017)
                ·
                  refine ⟨10591850727322569028869013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14122467636430092038492017 10591850727322569028869013)
                  ·
                    refine ⟨496493002843245423228235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10591850727322569028869013 496493002843245423228235)
                    ·
                      rfl

theorem cell22_1450375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_1450375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1450375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1450375 prefixEnd_1450375 := by exact prefixLift 1450375
  have htrace : WordTrace (prefixWord ++ tailWord_1450375) baseStart_1450375 baseEnd_1450375 := by
    simpa [prefixWord, tailWord_1450375, baseEnd_1450375] using wordTrace_append hprefix tailTrace_1450375
  have hstable : (prefixWord ++ tailWord_1450375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450375).length < 2 ^ (prefixWord ++ tailWord_1450375).sum := by decide
  have hdescent : baseEnd_1450375 < baseStart_1450375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450377 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 5, 3]
def baseStart_1450377 : Nat := 118140960795 + 1450377 * 2 ^ 59
def prefixEnd_1450377 : Nat := 4983230072969 + 3 ^ 40 * 1450377 * 2
def baseEnd_1450377 : Nat := 496493687484118084678229

theorem tailTrace_1450377 : CollatzResearch.WordTrace tailWord_1450377 prefixEnd_1450377 496493687484118084678229 := by
  unfold tailWord_1450377
  simp only [CollatzResearch.WordTrace]
  refine ⟨52899595066539308515933385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35266396711026205677288923 52899595066539308515933385)
  ·
    refine ⟨39674696299904481386950039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52899595066539308515933385 39674696299904481386950039)
    ·
      refine ⟨59512044449856722080425059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39674696299904481386950039 59512044449856722080425059)
      ·
        refine ⟨89268066674785083120637589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59512044449856722080425059 89268066674785083120637589)
        ·
          refine ⟨4184440625380550771279887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 89268066674785083120637589 4184440625380550771279887)
          ·
            refine ⟨6276660938070826156919831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4184440625380550771279887 6276660938070826156919831)
            ·
              refine ⟨9414991407106239235379747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6276660938070826156919831 9414991407106239235379747)
              ·
                refine ⟨14122487110659358853069621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9414991407106239235379747 14122487110659358853069621)
                ·
                  refine ⟨1323983166624314892475277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14122487110659358853069621 1323983166624314892475277)
                  ·
                    refine ⟨496493687484118084678229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1323983166624314892475277 496493687484118084678229)
                    ·
                      rfl

theorem cell22_1450377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5, 3].length) (baseStart_1450377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1450377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1450377 prefixEnd_1450377 := by exact prefixLift 1450377
  have htrace : WordTrace (prefixWord ++ tailWord_1450377) baseStart_1450377 baseEnd_1450377 := by
    simpa [prefixWord, tailWord_1450377, baseEnd_1450377] using wordTrace_append hprefix tailTrace_1450377
  have hstable : (prefixWord ++ tailWord_1450377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450377).length < 2 ^ (prefixWord ++ tailWord_1450377).sum := by decide
  have hdescent : baseEnd_1450377 < baseStart_1450377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450405 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 4, 5]
def baseStart_1450405 : Nat := 118140960795 + 1450405 * 2 ^ 59
def prefixEnd_1450405 : Nat := 4983230072969 + 3 ^ 40 * 1450405 * 2
def baseEnd_1450405 : Nat := 496503272456335344978143

theorem tailTrace_1450405 : CollatzResearch.WordTrace tailWord_1450405 prefixEnd_1450405 496503272456335344978143 := by
  unfold tailWord_1450405
  simp only [CollatzResearch.WordTrace]
  refine ⟨52900616310437869297952669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35267077540291912865301779 52900616310437869297952669)
  ·
    refine ⟨19837731116414200986732251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52900616310437869297952669 19837731116414200986732251)
    ·
      refine ⟨29756596674621301480098377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19837731116414200986732251 29756596674621301480098377)
      ·
        refine ⟨22317447505965976110073783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29756596674621301480098377 22317447505965976110073783)
        ·
          refine ⟨33476171258948964165110675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22317447505965976110073783 33476171258948964165110675)
          ·
            refine ⟨50214256888423446247666013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33476171258948964165110675 50214256888423446247666013)
            ·
              refine ⟨18830346333158792342874755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50214256888423446247666013 18830346333158792342874755)
              ·
                refine ⟨28245519499738188514312133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18830346333158792342874755 28245519499738188514312133)
                ·
                  refine ⟨5296034906200910346433525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28245519499738188514312133 5296034906200910346433525)
                  ·
                    refine ⟨496503272456335344978143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5296034906200910346433525 496503272456335344978143)
                    ·
                      rfl

theorem cell22_1450405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_1450405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1450405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1450405 prefixEnd_1450405 := by exact prefixLift 1450405
  have htrace : WordTrace (prefixWord ++ tailWord_1450405) baseStart_1450405 baseEnd_1450405 := by
    simpa [prefixWord, tailWord_1450405, baseEnd_1450405] using wordTrace_append hprefix tailTrace_1450405
  have hstable : (prefixWord ++ tailWord_1450405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450405).length < 2 ^ (prefixWord ++ tailWord_1450405).sum := by decide
  have hdescent : baseEnd_1450405 < baseStart_1450405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450407 : List Nat := [1, 1, 6, 1, 1, 3, 1, 1, 7]
def baseStart_1450407 : Nat := 118140960795 + 1450407 * 2 ^ 59
def prefixEnd_1450407 : Nat := 4983230072969 + 3 ^ 40 * 1450407 * 2
def baseEnd_1450407 : Nat := 165501319032402668809379

theorem tailTrace_1450407 : CollatzResearch.WordTrace tailWord_1450407 prefixEnd_1450407 165501319032402668809379 := by
  unfold tailWord_1450407
  simp only [CollatzResearch.WordTrace]
  refine ⟨52900689256430623639525475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35267126170953749093016983 52900689256430623639525475)
  ·
    refine ⟨79351033884645935459288213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52900689256430623639525475 79351033884645935459288213)
    ·
      refine ⟨3719579713342778224654135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 79351033884645935459288213 3719579713342778224654135)
      ·
        refine ⟨5579369570014167336981203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3719579713342778224654135 5579369570014167336981203)
        ·
          refine ⟨8369054355021251005471805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5579369570014167336981203 8369054355021251005471805)
          ·
            refine ⟨3138395383132969127051927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8369054355021251005471805 3138395383132969127051927)
            ·
              refine ⟨4707593074699453690577891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3138395383132969127051927 4707593074699453690577891)
              ·
                refine ⟨7061389612049180535866837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4707593074699453690577891 7061389612049180535866837)
                ·
                  refine ⟨165501319032402668809379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7061389612049180535866837 165501319032402668809379)
                  ·
                    rfl

theorem cell22_1450407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 7].length) (baseStart_1450407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1450407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1450407 prefixEnd_1450407 := by exact prefixLift 1450407
  have htrace : WordTrace (prefixWord ++ tailWord_1450407) baseStart_1450407 baseEnd_1450407 := by
    simpa [prefixWord, tailWord_1450407, baseEnd_1450407] using wordTrace_append hprefix tailTrace_1450407
  have hstable : (prefixWord ++ tailWord_1450407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450407).length < 2 ^ (prefixWord ++ tailWord_1450407).sum := by decide
  have hdescent : baseEnd_1450407 < baseStart_1450407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450497 : List Nat := [1, 2, 4, 1, 3, 1, 2, 8]
def baseStart_1450497 : Nat := 118140960795 + 1450497 * 2 ^ 59
def prefixEnd_1450497 : Nat := 4983230072969 + 3 ^ 40 * 1450497 * 2
def baseEnd_1450497 : Nat := 55170529548497530186429

theorem tailTrace_1450497 : CollatzResearch.WordTrace tailWord_1450497 prefixEnd_1450497 55170529548497530186429 := by
  unfold tailWord_1450497
  simp only [CollatzResearch.WordTrace]
  refine ⟨52903971826104569010301745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35269314550736379340201163 52903971826104569010301745)
  ·
    refine ⟨39677978869578426757726309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52903971826104569010301745 39677978869578426757726309)
    ·
      refine ⟨7439621038045955017073683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39677978869578426757726309 7439621038045955017073683)
      ·
        refine ⟨11159431557068932525610525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7439621038045955017073683 11159431557068932525610525)
        ·
          refine ⟨4184786833900849697103947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11159431557068932525610525 4184786833900849697103947)
          ·
            refine ⟨6277180250851274545655921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4184786833900849697103947 6277180250851274545655921)
            ·
              refine ⟨4707885188138455909241941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6277180250851274545655921 4707885188138455909241941)
              ·
                refine ⟨55170529548497530186429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4707885188138455909241941 55170529548497530186429)
                ·
                  rfl

theorem cell22_1450497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 8].length) (baseStart_1450497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1450497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1450497 prefixEnd_1450497 := by exact prefixLift 1450497
  have htrace : WordTrace (prefixWord ++ tailWord_1450497) baseStart_1450497 baseEnd_1450497 := by
    simpa [prefixWord, tailWord_1450497, baseEnd_1450497] using wordTrace_append hprefix tailTrace_1450497
  have hstable : (prefixWord ++ tailWord_1450497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450497).length < 2 ^ (prefixWord ++ tailWord_1450497).sum := by decide
  have hdescent : baseEnd_1450497 < baseStart_1450497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450516 : List Nat := [2, 4, 3, 1, 1, 1, 2, 2, 2, 4]
def baseStart_1450516 : Nat := 118140960795 + 1450516 * 2 ^ 59
def prefixEnd_1450516 : Nat := 4983230072969 + 3 ^ 40 * 1450516 * 2
def baseEnd_1450516 : Nat := 496541270024768055452803

theorem tailTrace_1450516 : CollatzResearch.WordTrace tailWord_1450516 prefixEnd_1450516 496541270024768055452803 := by
  unfold tailWord_1450516
  simp only [CollatzResearch.WordTrace]
  refine ⟨26452332406517867627621701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35269776542023823503495601 26452332406517867627621701)
  ·
    refine ⟨4959812326222100180179069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26452332406517867627621701 4959812326222100180179069)
    ·
      refine ⟨1859929622333287567567151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4959812326222100180179069 1859929622333287567567151)
      ·
        refine ⟨2789894433499931351350727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1859929622333287567567151 2789894433499931351350727)
        ·
          refine ⟨4184841650249897027026091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2789894433499931351350727 4184841650249897027026091)
          ·
            refine ⟨6277262475374845540539137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4184841650249897027026091 6277262475374845540539137)
            ·
              refine ⟨4707946856531134155404353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6277262475374845540539137 4707946856531134155404353)
              ·
                refine ⟨3530960142398350616553265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4707946856531134155404353 3530960142398350616553265)
                ·
                  refine ⟨2648220106798762962414949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3530960142398350616553265 2648220106798762962414949)
                  ·
                    refine ⟨496541270024768055452803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2648220106798762962414949 496541270024768055452803)
                    ·
                      rfl

theorem cell22_1450516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_1450516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1450516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1450516 prefixEnd_1450516 := by exact prefixLift 1450516
  have htrace : WordTrace (prefixWord ++ tailWord_1450516) baseStart_1450516 baseEnd_1450516 := by
    simpa [prefixWord, tailWord_1450516, baseEnd_1450516] using wordTrace_append hprefix tailTrace_1450516
  have hstable : (prefixWord ++ tailWord_1450516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450516).length < 2 ^ (prefixWord ++ tailWord_1450516).sum := by decide
  have hdescent : baseEnd_1450516 < baseStart_1450516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450529 : List Nat := [1, 2, 3, 2, 2, 1, 2, 3, 3, 3]
def baseStart_1450529 : Nat := 118140960795 + 1450529 * 2 ^ 59
def prefixEnd_1450529 : Nat := 4983230072969 + 3 ^ 40 * 1450529 * 2
def baseEnd_1450529 : Nat := 496545720190440354877763

theorem tailTrace_1450529 : CollatzResearch.WordTrace tailWord_1450529 prefixEnd_1450529 496545720190440354877763 := by
  unfold tailWord_1450529
  simp only [CollatzResearch.WordTrace]
  refine ⟨52905138961988638475466641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35270092641325758983644427 52905138961988638475466641)
  ·
    refine ⟨39678854221491478856599981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52905138961988638475466641 39678854221491478856599981)
    ·
      refine ⟨14879570333059304571224993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39678854221491478856599981 14879570333059304571224993)
      ·
        refine ⟨11159677749794478428418745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14879570333059304571224993 11159677749794478428418745)
        ·
          refine ⟨8369758312345858821314059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11159677749794478428418745 8369758312345858821314059)
          ·
            refine ⟨12554637468518788231971089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8369758312345858821314059 12554637468518788231971089)
            ·
              refine ⟨9415978101389091173978317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12554637468518788231971089 9415978101389091173978317)
              ·
                refine ⟨3530991788020909190241869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9415978101389091173978317 3530991788020909190241869)
                ·
                  refine ⟨1324121920507840946340701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3530991788020909190241869 1324121920507840946340701)
                  ·
                    refine ⟨496545720190440354877763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1324121920507840946340701 496545720190440354877763)
                    ·
                      rfl

theorem cell22_1450529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_1450529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1450529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1450529 prefixEnd_1450529 := by exact prefixLift 1450529
  have htrace : WordTrace (prefixWord ++ tailWord_1450529) baseStart_1450529 baseEnd_1450529 := by
    simpa [prefixWord, tailWord_1450529, baseEnd_1450529] using wordTrace_append hprefix tailTrace_1450529
  have hstable : (prefixWord ++ tailWord_1450529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450529).length < 2 ^ (prefixWord ++ tailWord_1450529).sum := by decide
  have hdescent : baseEnd_1450529 < baseStart_1450529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450548 : List Nat := [2, 5, 1, 3, 1, 1, 3, 6]
def baseStart_1450548 : Nat := 118140960795 + 1450548 * 2 ^ 59
def prefixEnd_1450548 : Nat := 4983230072969 + 3 ^ 40 * 1450548 * 2
def baseEnd_1450548 : Nat := 55172469364303404294745

theorem tailTrace_1450548 : CollatzResearch.WordTrace tailWord_1450548 prefixEnd_1450548 55172469364303404294745 := by
  unfold tailWord_1450548
  simp only [CollatzResearch.WordTrace]
  refine ⟨26452915974459902360204149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35270554632613203146938865 26452915974459902360204149)
  ·
    refine ⟨2479960872605615846269139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26452915974459902360204149 2479960872605615846269139)
    ·
      refine ⟨3719941308908423769403709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2479960872605615846269139 3719941308908423769403709)
      ·
        refine ⟨1394977990840658913526391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3719941308908423769403709 1394977990840658913526391)
        ·
          refine ⟨2092466986260988370289587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1394977990840658913526391 2092466986260988370289587)
          ·
            refine ⟨3138700479391482555434381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2092466986260988370289587 3138700479391482555434381)
            ·
              refine ⟨1177012679771805958287893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3138700479391482555434381 1177012679771805958287893)
              ·
                refine ⟨55172469364303404294745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1177012679771805958287893 55172469364303404294745)
                ·
                  rfl

theorem cell22_1450548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 6].length) (baseStart_1450548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1450548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1450548 prefixEnd_1450548 := by exact prefixLift 1450548
  have htrace : WordTrace (prefixWord ++ tailWord_1450548) baseStart_1450548 baseEnd_1450548 := by
    simpa [prefixWord, tailWord_1450548, baseEnd_1450548] using wordTrace_append hprefix tailTrace_1450548
  have hstable : (prefixWord ++ tailWord_1450548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450548).length < 2 ^ (prefixWord ++ tailWord_1450548).sum := by decide
  have hdescent : baseEnd_1450548 < baseStart_1450548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450606 : List Nat := [4, 1, 2, 2, 2, 1, 1, 4, 1, 4]
def baseStart_1450606 : Nat := 118140960795 + 1450606 * 2 ^ 59
def prefixEnd_1450606 : Nat := 4983230072969 + 3 ^ 40 * 1450606 * 2
def baseEnd_1450606 : Nat := 496572078864037820702527

theorem tailTrace_1450606 : CollatzResearch.WordTrace tailWord_1450606 prefixEnd_1450606 496572078864037820702527 := by
  unfold tailWord_1450606
  simp only [CollatzResearch.WordTrace]
  refine ⟨6613493422838710078252459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35271964921806453750679781 6613493422838710078252459)
  ·
    refine ⟨9920240134258065117378689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6613493422838710078252459 9920240134258065117378689)
    ·
      refine ⟨7440180100693548838034017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9920240134258065117378689 7440180100693548838034017)
      ·
        refine ⟨5580135075520161628525513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7440180100693548838034017 5580135075520161628525513)
        ·
          refine ⟨4185101306640121221394135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5580135075520161628525513 4185101306640121221394135)
          ·
            refine ⟨6277651959960181832091203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4185101306640121221394135 6277651959960181832091203)
            ·
              refine ⟨9416477939940272748136805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6277651959960181832091203 9416477939940272748136805)
              ·
                refine ⟨1765589613738801140275651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9416477939940272748136805 1765589613738801140275651)
                ·
                  refine ⟨2648384420608201710413477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1765589613738801140275651 2648384420608201710413477)
                  ·
                    refine ⟨496572078864037820702527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2648384420608201710413477 496572078864037820702527)
                    ·
                      rfl

theorem cell22_1450606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_1450606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1450606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1450606 prefixEnd_1450606 := by exact prefixLift 1450606
  have htrace : WordTrace (prefixWord ++ tailWord_1450606) baseStart_1450606 baseEnd_1450606 := by
    simpa [prefixWord, tailWord_1450606, baseEnd_1450606] using wordTrace_append hprefix tailTrace_1450606
  have hstable : (prefixWord ++ tailWord_1450606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450606).length < 2 ^ (prefixWord ++ tailWord_1450606).sum := by decide
  have hdescent : baseEnd_1450606 < baseStart_1450606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450638 : List Nat := [4, 1, 1, 3, 1, 1, 5, 2, 4]
def baseStart_1450638 : Nat := 118140960795 + 1450638 * 2 ^ 59
def prefixEnd_1450638 : Nat := 4983230072969 + 3 ^ 40 * 1450638 * 2
def baseEnd_1450638 : Nat := 165527677706000134634143

theorem tailTrace_1450638 : CollatzResearch.WordTrace tailWord_1450638 prefixEnd_1450638 165527677706000134634143 := by
  unfold tailWord_1450638
  simp only [CollatzResearch.WordTrace]
  refine ⟨6613639314824218761398071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35272743012395833394123045 6613639314824218761398071)
  ·
    refine ⟨9920458972236328142097107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6613639314824218761398071 9920458972236328142097107)
    ·
      refine ⟨14880688458354492213145661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9920458972236328142097107 14880688458354492213145661)
      ·
        refine ⟨5580258171882934579929623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14880688458354492213145661 5580258171882934579929623)
        ·
          refine ⟨8370387257824401869894435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5580258171882934579929623 8370387257824401869894435)
          ·
            refine ⟨12555580886736602804841653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8370387257824401869894435 12555580886736602804841653)
            ·
              refine ⟨1177085708131556512953905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12555580886736602804841653 1177085708131556512953905)
              ·
                refine ⟨882814281098667384715429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1177085708131556512953905 882814281098667384715429)
                ·
                  refine ⟨165527677706000134634143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 882814281098667384715429 165527677706000134634143)
                  ·
                    rfl

theorem cell22_1450638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_1450638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1450638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1450638 prefixEnd_1450638 := by exact prefixLift 1450638
  have htrace : WordTrace (prefixWord ++ tailWord_1450638) baseStart_1450638 baseEnd_1450638 := by
    simpa [prefixWord, tailWord_1450638, baseEnd_1450638] using wordTrace_append hprefix tailTrace_1450638
  have hstable : (prefixWord ++ tailWord_1450638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450638).length < 2 ^ (prefixWord ++ tailWord_1450638).sum := by decide
  have hdescent : baseEnd_1450638 < baseStart_1450638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450653 : List Nat := [1, 4, 2, 1, 1, 1, 6, 1, 2, 3]
def baseStart_1450653 : Nat := 118140960795 + 1450653 * 2 ^ 59
def prefixEnd_1450653 : Nat := 4983230072969 + 3 ^ 40 * 1450653 * 2
def baseEnd_1450653 : Nat := 496588167924545364777383

theorem tailTrace_1450653 : CollatzResearch.WordTrace tailWord_1450653 prefixEnd_1450653 496588167924545364777383 := by
  unfold tailWord_1450653
  simp only [CollatzResearch.WordTrace]
  refine ⟨52909661613539407652980613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35273107742359605101987075 52909661613539407652980613)
  ·
    refine ⟨9920561552538638934933865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52909661613539407652980613 9920561552538638934933865)
    ·
      refine ⟨7440421164403979201200399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9920561552538638934933865 7440421164403979201200399)
      ·
        refine ⟨11160631746605968801800599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7440421164403979201200399 11160631746605968801800599)
        ·
          refine ⟨16740947619908953202700899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11160631746605968801800599 16740947619908953202700899)
          ·
            refine ⟨25111421429863429804051349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16740947619908953202700899 25111421429863429804051349)
            ·
              refine ⟨1177097879524848272064907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25111421429863429804051349 1177097879524848272064907)
              ·
                refine ⟨1765646819287272408097361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1177097879524848272064907 1765646819287272408097361)
                ·
                  refine ⟨1324235114465454306073021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1765646819287272408097361 1324235114465454306073021)
                  ·
                    refine ⟨496588167924545364777383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1324235114465454306073021 496588167924545364777383)
                    ·
                      rfl

theorem cell22_1450653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_1450653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1450653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1450653 prefixEnd_1450653 := by exact prefixLift 1450653
  have htrace : WordTrace (prefixWord ++ tailWord_1450653) baseStart_1450653 baseEnd_1450653 := by
    simpa [prefixWord, tailWord_1450653, baseEnd_1450653] using wordTrace_append hprefix tailTrace_1450653
  have hstable : (prefixWord ++ tailWord_1450653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450653).length < 2 ^ (prefixWord ++ tailWord_1450653).sum := by decide
  have hdescent : baseEnd_1450653 < baseStart_1450653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450689 : List Nat := [1, 2, 6, 2, 2, 1, 2, 2, 4]
def baseStart_1450689 : Nat := 118140960795 + 1450689 * 2 ^ 59
def prefixEnd_1450689 : Nat := 4983230072969 + 3 ^ 40 * 1450689 * 2
def baseEnd_1450689 : Nat := 165533497153417756959091

theorem tailTrace_1450689 : CollatzResearch.WordTrace tailWord_1450689 prefixEnd_1450689 165533497153417756959091 := by
  unfold tailWord_1450689
  simp only [CollatzResearch.WordTrace]
  refine ⟨52910974641408985801291121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35273983094272657200860747 52910974641408985801291121)
  ·
    refine ⟨39683230981056739350968341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52910974641408985801291121 39683230981056739350968341)
    ·
      refine ⟨1860151452237034657076641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39683230981056739350968341 1860151452237034657076641)
      ·
        refine ⟨1395113589177775992807481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1860151452237034657076641 1395113589177775992807481)
        ·
          refine ⟨1046335191883331994605611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1395113589177775992807481 1046335191883331994605611)
          ·
            refine ⟨1569502787824997991908417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1046335191883331994605611 1569502787824997991908417)
            ·
              refine ⟨1177127090868748493931313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1569502787824997991908417 1177127090868748493931313)
              ·
                refine ⟨882845318151561370448485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1177127090868748493931313 882845318151561370448485)
                ·
                  refine ⟨165533497153417756959091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 882845318151561370448485 165533497153417756959091)
                  ·
                    rfl

theorem cell22_1450689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2, 4].length) (baseStart_1450689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1450689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1450689 prefixEnd_1450689 := by exact prefixLift 1450689
  have htrace : WordTrace (prefixWord ++ tailWord_1450689) baseStart_1450689 baseEnd_1450689 := by
    simpa [prefixWord, tailWord_1450689, baseEnd_1450689] using wordTrace_append hprefix tailTrace_1450689
  have hstable : (prefixWord ++ tailWord_1450689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450689).length < 2 ^ (prefixWord ++ tailWord_1450689).sum := by decide
  have hdescent : baseEnd_1450689 < baseStart_1450689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450756 : List Nat := [2, 3, 2, 2, 1, 1, 4, 1, 6]
def baseStart_1450756 : Nat := 118140960795 + 1450756 * 2 ^ 59
def prefixEnd_1450756 : Nat := 4983230072969 + 3 ^ 40 * 1450756 * 2
def baseEnd_1450756 : Nat := 165541142309829143150689

theorem tailTrace_1450756 : CollatzResearch.WordTrace tailWord_1450756 prefixEnd_1450756 165541142309829143150689 := by
  unfold tailWord_1450756
  simp only [CollatzResearch.WordTrace]
  refine ⟨26456709166083128121990061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35275612221444170829320081 26456709166083128121990061)
  ·
    refine ⟨9921265937281173045746273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26456709166083128121990061 9921265937281173045746273)
    ·
      refine ⟨7440949452960879784309705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9921265937281173045746273 7440949452960879784309705)
      ·
        refine ⟨5580712089720659838232279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7440949452960879784309705 5580712089720659838232279)
        ·
          refine ⟨8371068134580989757348419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5580712089720659838232279 8371068134580989757348419)
          ·
            refine ⟨12556602201871484636022629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8371068134580989757348419 12556602201871484636022629)
            ·
              refine ⟨2354362912850903369254243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12556602201871484636022629 2354362912850903369254243)
              ·
                refine ⟨3531544369276355053881365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2354362912850903369254243 3531544369276355053881365)
                ·
                  refine ⟨165541142309829143150689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3531544369276355053881365 165541142309829143150689)
                  ·
                    rfl

theorem cell22_1450756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_1450756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1450756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1450756 prefixEnd_1450756 := by exact prefixLift 1450756
  have htrace : WordTrace (prefixWord ++ tailWord_1450756) baseStart_1450756 baseEnd_1450756 := by
    simpa [prefixWord, tailWord_1450756, baseEnd_1450756] using wordTrace_append hprefix tailTrace_1450756
  have hstable : (prefixWord ++ tailWord_1450756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450756).length < 2 ^ (prefixWord ++ tailWord_1450756).sum := by decide
  have hdescent : baseEnd_1450756 < baseStart_1450756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450769 : List Nat := [1, 2, 2, 1, 1, 3, 3, 2, 1, 6]
def baseStart_1450769 : Nat := 118140960795 + 1450769 * 2 ^ 59
def prefixEnd_1450769 : Nat := 4983230072969 + 3 ^ 40 * 1450769 * 2
def baseEnd_1450769 : Nat := 496627877095159728877027

theorem tailTrace_1450769 : CollatzResearch.WordTrace tailWord_1450769 prefixEnd_1450769 496627877095159728877027 := by
  unfold tailWord_1450769
  simp only [CollatzResearch.WordTrace]
  refine ⟨52913892481119159464203361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35275928320746106309468907 52913892481119159464203361)
  ·
    refine ⟨39685419360839369598152521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52913892481119159464203361 39685419360839369598152521)
    ·
      refine ⟨29764064520629527198614391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39685419360839369598152521 29764064520629527198614391)
      ·
        refine ⟨44646096780944290797921587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29764064520629527198614391 44646096780944290797921587)
        ·
          refine ⟨66969145171416436196882381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44646096780944290797921587 66969145171416436196882381)
          ·
            refine ⟨25113429439281163573830893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66969145171416436196882381 25113429439281163573830893)
            ·
              refine ⟨9417536039730436340186585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25113429439281163573830893 9417536039730436340186585)
              ·
                refine ⟨7063152029797827255139939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9417536039730436340186585 7063152029797827255139939)
                ·
                  refine ⟨10594728044696740882709909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7063152029797827255139939 10594728044696740882709909)
                  ·
                    refine ⟨496627877095159728877027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10594728044696740882709909 496627877095159728877027)
                    ·
                      rfl

theorem cell22_1450769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_1450769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1450769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1450769 prefixEnd_1450769 := by exact prefixLift 1450769
  have htrace : WordTrace (prefixWord ++ tailWord_1450769) baseStart_1450769 baseEnd_1450769 := by
    simpa [prefixWord, tailWord_1450769, baseEnd_1450769] using wordTrace_append hprefix tailTrace_1450769
  have hstable : (prefixWord ++ tailWord_1450769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450769).length < 2 ^ (prefixWord ++ tailWord_1450769).sum := by decide
  have hdescent : baseEnd_1450769 < baseStart_1450769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450786 : List Nat := [3, 3, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_1450786 : Nat := 118140960795 + 1450786 * 2 ^ 59
def prefixEnd_1450786 : Nat := 4983230072969 + 3 ^ 40 * 1450786 * 2
def baseEnd_1450786 : Nat := 496633696542577351201975

theorem tailTrace_1450786 : CollatzResearch.WordTrace tailWord_1450786 prefixEnd_1450786 496633696542577351201975 := by
  unfold tailWord_1450786
  simp only [CollatzResearch.WordTrace]
  refine ⟨13228628130514392841893053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35276341681371714245048141 13228628130514392841893053)
  ·
    refine ⟨4960735548942897315709895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13228628130514392841893053 4960735548942897315709895)
    ·
      refine ⟨7441103323414345973564843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4960735548942897315709895 7441103323414345973564843)
      ·
        refine ⟨11161654985121518960347265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7441103323414345973564843 11161654985121518960347265)
        ·
          refine ⟨8371241238841139220260449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11161654985121518960347265 8371241238841139220260449)
          ·
            refine ⟨6278430929130854415195337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8371241238841139220260449 6278430929130854415195337)
            ·
              refine ⟨4708823196848140811396503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6278430929130854415195337 4708823196848140811396503)
              ·
                refine ⟨7063234795272211217094755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4708823196848140811396503 7063234795272211217094755)
                ·
                  refine ⟨10594852192908316825642133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7063234795272211217094755 10594852192908316825642133)
                  ·
                    refine ⟨496633696542577351201975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10594852192908316825642133 496633696542577351201975)
                    ·
                      rfl

theorem cell22_1450786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_1450786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1450786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1450786 prefixEnd_1450786 := by exact prefixLift 1450786
  have htrace : WordTrace (prefixWord ++ tailWord_1450786) baseStart_1450786 baseEnd_1450786 := by
    simpa [prefixWord, tailWord_1450786, baseEnd_1450786] using wordTrace_append hprefix tailTrace_1450786
  have hstable : (prefixWord ++ tailWord_1450786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450786).length < 2 ^ (prefixWord ++ tailWord_1450786).sum := by decide
  have hdescent : baseEnd_1450786 < baseStart_1450786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450861 : List Nat := [1, 5, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_1450861 : Nat := 118140960795 + 1450861 * 2 ^ 59
def prefixEnd_1450861 : Nat := 4983230072969 + 3 ^ 40 * 1450861 * 2
def baseEnd_1450861 : Nat := 496659370575302155576745

theorem tailTrace_1450861 : CollatzResearch.WordTrace tailWord_1450861 prefixEnd_1450861 496659370575302155576745 := by
  unfold tailWord_1450861
  simp only [CollatzResearch.WordTrace]
  refine ⟨52917247996785859176552437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35278165331190572784368291 52917247996785859176552437)
  ·
    refine ⟨4960991999698674297801791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52917247996785859176552437 4960991999698674297801791)
    ·
      refine ⟨7441487999548011446702687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4960991999698674297801791 7441487999548011446702687)
      ·
        refine ⟨11162231999322017170054031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7441487999548011446702687 11162231999322017170054031)
        ·
          refine ⟨16743347998983025755081047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11162231999322017170054031 16743347998983025755081047)
          ·
            refine ⟨25115021998474538632621571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16743347998983025755081047 25115021998474538632621571)
            ·
              refine ⟨37672532997711807948932357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25115021998474538632621571 37672532997711807948932357)
              ·
                refine ⟨7063599937070963990424817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37672532997711807948932357 7063599937070963990424817)
                ·
                  refine ⟨5297699952803222992818613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7063599937070963990424817 5297699952803222992818613)
                  ·
                    refine ⟨496659370575302155576745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5297699952803222992818613 496659370575302155576745)
                    ·
                      rfl

theorem cell22_1450861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_1450861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1450861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1450861 prefixEnd_1450861 := by exact prefixLift 1450861
  have htrace : WordTrace (prefixWord ++ tailWord_1450861) baseStart_1450861 baseEnd_1450861 := by
    simpa [prefixWord, tailWord_1450861, baseEnd_1450861] using wordTrace_append hprefix tailTrace_1450861
  have hstable : (prefixWord ++ tailWord_1450861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450861).length < 2 ^ (prefixWord ++ tailWord_1450861).sum := by decide
  have hdescent : baseEnd_1450861 < baseStart_1450861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450921 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 4, 4]
def baseStart_1450921 : Nat := 118140960795 + 1450921 * 2 ^ 59
def prefixEnd_1450921 : Nat := 4983230072969 + 3 ^ 40 * 1450921 * 2
def baseEnd_1450921 : Nat := 496679909801481999076561

theorem tailTrace_1450921 : CollatzResearch.WordTrace tailWord_1450921 prefixEnd_1450921 496679909801481999076561 := by
  unfold tailWord_1450921
  simp only [CollatzResearch.WordTrace]
  refine ⟨52919436376568489423736617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35279624251045659615824411 52919436376568489423736617)
  ·
    refine ⟨39689577282426367067802463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52919436376568489423736617 39689577282426367067802463)
    ·
      refine ⟨59534365923639550601703695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39689577282426367067802463 59534365923639550601703695)
      ·
        refine ⟨89301548885459325902555543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59534365923639550601703695 89301548885459325902555543)
        ·
          refine ⟨133952323328188988853833315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89301548885459325902555543 133952323328188988853833315)
          ·
            refine ⟨200928484992283483280749973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133952323328188988853833315 200928484992283483280749973)
            ·
              refine ⟨9418522734013288278785155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 200928484992283483280749973 9418522734013288278785155)
              ·
                refine ⟨14127784101019932418177733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9418522734013288278785155 14127784101019932418177733)
                ·
                  refine ⟨2648959518941237328408325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14127784101019932418177733 2648959518941237328408325)
                  ·
                    refine ⟨496679909801481999076561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2648959518941237328408325 496679909801481999076561)
                    ·
                      rfl

theorem cell22_1450921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 4].length) (baseStart_1450921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1450921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1450921 prefixEnd_1450921 := by exact prefixLift 1450921
  have htrace : WordTrace (prefixWord ++ tailWord_1450921) baseStart_1450921 baseEnd_1450921 := by
    simpa [prefixWord, tailWord_1450921, baseEnd_1450921] using wordTrace_append hprefix tailTrace_1450921
  have hstable : (prefixWord ++ tailWord_1450921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450921).length < 2 ^ (prefixWord ++ tailWord_1450921).sum := by decide
  have hdescent : baseEnd_1450921 < baseStart_1450921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451036 : List Nat := [2, 2, 3, 1, 4, 2, 2, 2, 1, 3]
def baseStart_1451036 : Nat := 118140960795 + 1451036 * 2 ^ 59
def prefixEnd_1451036 : Nat := 4983230072969 + 3 ^ 40 * 1451036 * 2
def baseEnd_1451036 : Nat := 496719276651660032451209

theorem tailTrace_1451036 : CollatzResearch.WordTrace tailWord_1451036 prefixEnd_1451036 496719276651660032451209 := by
  unfold tailWord_1451036
  simp only [CollatzResearch.WordTrace]
  refine ⟨26461815385575932032086481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35282420514101242709448641 26461815385575932032086481)
  ·
    refine ⟨19846361539181949024064861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26461815385575932032086481 19846361539181949024064861)
    ·
      refine ⟨7442385577193230884024323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19846361539181949024064861 7442385577193230884024323)
      ·
        refine ⟨11163578365789846326036485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7442385577193230884024323 11163578365789846326036485)
        ·
          refine ⟨2093170943585596186131841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11163578365789846326036485 2093170943585596186131841)
          ·
            refine ⟨1569878207689197139598881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2093170943585596186131841 1569878207689197139598881)
            ·
              refine ⟨1177408655766897854699161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1569878207689197139598881 1177408655766897854699161)
              ·
                refine ⟨883056491825173391024371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1177408655766897854699161 883056491825173391024371)
                ·
                  refine ⟨1324584737737760086536557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 883056491825173391024371 1324584737737760086536557)
                  ·
                    refine ⟨496719276651660032451209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1324584737737760086536557 496719276651660032451209)
                    ·
                      rfl

theorem cell22_1451036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_1451036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451036 prefixEnd_1451036 := by exact prefixLift 1451036
  have htrace : WordTrace (prefixWord ++ tailWord_1451036) baseStart_1451036 baseEnd_1451036 := by
    simpa [prefixWord, tailWord_1451036, baseEnd_1451036] using wordTrace_append hprefix tailTrace_1451036
  have hstable : (prefixWord ++ tailWord_1451036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451036).length < 2 ^ (prefixWord ++ tailWord_1451036).sum := by decide
  have hdescent : baseEnd_1451036 < baseStart_1451036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451060 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 8]
def baseStart_1451060 : Nat := 118140960795 + 1451060 * 2 ^ 59
def prefixEnd_1451060 : Nat := 4983230072969 + 3 ^ 40 * 1451060 * 2
def baseEnd_1451060 : Nat := 165575830780710656617045

theorem tailTrace_1451060 : CollatzResearch.WordTrace tailWord_1451060 prefixEnd_1451060 165575830780710656617045 := by
  unfold tailWord_1451060
  simp only [CollatzResearch.WordTrace]
  refine ⟨26462253061532458081523317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35283004082043277442031089 26462253061532458081523317)
  ·
    refine ⟨2480836224518667945142811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26462253061532458081523317 2480836224518667945142811)
    ·
      refine ⟨3721254336778001917714217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2480836224518667945142811 3721254336778001917714217)
      ·
        refine ⟨2790940752583501438285663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3721254336778001917714217 2790940752583501438285663)
        ·
          refine ⟨4186411128875252157428495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2790940752583501438285663 4186411128875252157428495)
          ·
            refine ⟨6279616693312878236142743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4186411128875252157428495 6279616693312878236142743)
            ·
              refine ⟨9419425039969317354214115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6279616693312878236142743 9419425039969317354214115)
              ·
                refine ⟨14129137559953976031321173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9419425039969317354214115 14129137559953976031321173)
                ·
                  refine ⟨165575830780710656617045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14129137559953976031321173 165575830780710656617045)
                  ·
                    rfl

theorem cell22_1451060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_1451060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451060 prefixEnd_1451060 := by exact prefixLift 1451060
  have htrace : WordTrace (prefixWord ++ tailWord_1451060) baseStart_1451060 baseEnd_1451060 := by
    simpa [prefixWord, tailWord_1451060, baseEnd_1451060] using wordTrace_append hprefix tailTrace_1451060
  have hstable : (prefixWord ++ tailWord_1451060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451060).length < 2 ^ (prefixWord ++ tailWord_1451060).sum := by decide
  have hdescent : baseEnd_1451060 < baseStart_1451060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451092 : List Nat := [2, 4, 1, 1, 1, 1, 5, 2, 2, 3]
def baseStart_1451092 : Nat := 118140960795 + 1451092 * 2 ^ 59
def prefixEnd_1451092 : Nat := 4983230072969 + 3 ^ 40 * 1451092 * 2
def baseEnd_1451092 : Nat := 496738446596094553051037

theorem tailTrace_1451092 : CollatzResearch.WordTrace tailWord_1451092 prefixEnd_1451092 496738446596094553051037 := by
  unfold tailWord_1451092
  simp only [CollatzResearch.WordTrace]
  refine ⟨26462836629474492814105765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35283782172632657085474353 26462836629474492814105765)
  ·
    refine ⟨4961781868026467402644831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26462836629474492814105765 4961781868026467402644831)
    ·
      refine ⟨7442672802039701103967247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4961781868026467402644831 7442672802039701103967247)
      ·
        refine ⟨11164009203059551655950871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7442672802039701103967247 11164009203059551655950871)
        ·
          refine ⟨16746013804589327483926307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11164009203059551655950871 16746013804589327483926307)
          ·
            refine ⟨25119020706883991225889461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16746013804589327483926307 25119020706883991225889461)
            ·
              refine ⟨2354908191270374177427137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25119020706883991225889461 2354908191270374177427137)
              ·
                refine ⟨1766181143452780633070353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2354908191270374177427137 1766181143452780633070353)
                ·
                  refine ⟨1324635857589585474802765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1766181143452780633070353 1324635857589585474802765)
                  ·
                    refine ⟨496738446596094553051037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1324635857589585474802765 496738446596094553051037)
                    ·
                      rfl

theorem cell22_1451092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_1451092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451092 prefixEnd_1451092 := by exact prefixLift 1451092
  have htrace : WordTrace (prefixWord ++ tailWord_1451092) baseStart_1451092 baseEnd_1451092 := by
    simpa [prefixWord, tailWord_1451092, baseEnd_1451092] using wordTrace_append hprefix tailTrace_1451092
  have hstable : (prefixWord ++ tailWord_1451092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451092).length < 2 ^ (prefixWord ++ tailWord_1451092).sum := by decide
  have hdescent : baseEnd_1451092 < baseStart_1451092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451094 : List Nat := [5, 2, 2, 1, 2, 1, 2, 1, 6]
def baseStart_1451094 : Nat := 118140960795 + 1451094 * 2 ^ 59
def prefixEnd_1451094 : Nat := 4983230072969 + 3 ^ 40 * 1451094 * 2
def baseEnd_1451094 : Nat := 165579710412322404833677

theorem tailTrace_1451094 : CollatzResearch.WordTrace tailWord_1451094 prefixEnd_1451094 165579710412322404833677 := by
  unfold tailWord_1451094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3307859137808858748111521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35283830803294493313189557 3307859137808858748111521)
  ·
    refine ⟨2480894353356644061083641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3307859137808858748111521 2480894353356644061083641)
    ·
      refine ⟨1860670765017483045812731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2480894353356644061083641 1860670765017483045812731)
      ·
        refine ⟨2791006147526224568719097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1860670765017483045812731 2791006147526224568719097)
        ·
          refine ⟨2093254610644668426539323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2791006147526224568719097 2093254610644668426539323)
          ·
            refine ⟨3139881915967002639808985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2093254610644668426539323 3139881915967002639808985)
            ·
              refine ⟨2354911436975251979856739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3139881915967002639808985 2354911436975251979856739)
              ·
                refine ⟨3532367155462877969785109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2354911436975251979856739 3532367155462877969785109)
                ·
                  refine ⟨165579710412322404833677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3532367155462877969785109 165579710412322404833677)
                  ·
                    rfl

theorem cell22_1451094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_1451094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451094 prefixEnd_1451094 := by exact prefixLift 1451094
  have htrace : WordTrace (prefixWord ++ tailWord_1451094) baseStart_1451094 baseEnd_1451094 := by
    simpa [prefixWord, tailWord_1451094, baseEnd_1451094] using wordTrace_append hprefix tailTrace_1451094
  have hstable : (prefixWord ++ tailWord_1451094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451094).length < 2 ^ (prefixWord ++ tailWord_1451094).sum := by decide
  have hdescent : baseEnd_1451094 < baseStart_1451094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451120 : List Nat := [2, 1, 1, 1, 5, 1, 1, 4, 3, 3]
def baseStart_1451120 : Nat := 118140960795 + 1451120 * 2 ^ 59
def prefixEnd_1451120 : Nat := 4983230072969 + 3 ^ 40 * 1451120 * 2
def baseEnd_1451120 : Nat := 496748031568311813350951

theorem tailTrace_1451120 : CollatzResearch.WordTrace tailWord_1451120 prefixEnd_1451120 496748031568311813350951 := by
  unfold tailWord_1451120
  simp only [CollatzResearch.WordTrace]
  refine ⟨26463347251423773205115407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35284463001898364273487209 26463347251423773205115407)
  ·
    refine ⟨39695020877135659807673111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26463347251423773205115407 39695020877135659807673111)
    ·
      refine ⟨59542531315703489711509667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39695020877135659807673111 59542531315703489711509667)
      ·
        refine ⟨89313796973555234567264501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59542531315703489711509667 89313796973555234567264501)
        ·
          refine ⟨8373168466270803240681047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89313796973555234567264501 8373168466270803240681047)
          ·
            refine ⟨12559752699406204861021571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8373168466270803240681047 12559752699406204861021571)
            ·
              refine ⟨18839629049109307291532357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12559752699406204861021571 18839629049109307291532357)
              ·
                refine ⟨3532430446707995117162317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18839629049109307291532357 3532430446707995117162317)
                ·
                  refine ⟨1324661417515498168935869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3532430446707995117162317 1324661417515498168935869)
                  ·
                    refine ⟨496748031568311813350951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1324661417515498168935869 496748031568311813350951)
                    ·
                      rfl

theorem cell22_1451120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 3, 3].length) (baseStart_1451120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451120 prefixEnd_1451120 := by exact prefixLift 1451120
  have htrace : WordTrace (prefixWord ++ tailWord_1451120) baseStart_1451120 baseEnd_1451120 := by
    simpa [prefixWord, tailWord_1451120, baseEnd_1451120] using wordTrace_append hprefix tailTrace_1451120
  have hstable : (prefixWord ++ tailWord_1451120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451120).length < 2 ^ (prefixWord ++ tailWord_1451120).sum := by decide
  have hdescent : baseEnd_1451120 < baseStart_1451120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451133 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 9]
def baseStart_1451133 : Nat := 118140960795 + 1451133 * 2 ^ 59
def prefixEnd_1451133 : Nat := 4983230072969 + 3 ^ 40 * 1451133 * 2
def baseEnd_1451133 : Nat := 165584160577994704258637

theorem tailTrace_1451133 : CollatzResearch.WordTrace tailWord_1451133 prefixEnd_1451133 165584160577994704258637 := by
  unfold tailWord_1451133
  simp only [CollatzResearch.WordTrace]
  refine ⟨52927168651800449630454053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35284779101200299753636035 52927168651800449630454053)
  ·
    refine ⟨9923844122212584305710135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52927168651800449630454053 9923844122212584305710135)
    ·
      refine ⟨14885766183318876458565203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9923844122212584305710135 14885766183318876458565203)
      ·
        refine ⟨22328649274978314687847805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14885766183318876458565203 22328649274978314687847805)
        ·
          refine ⟨8373243478116868007942927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22328649274978314687847805 8373243478116868007942927)
          ·
            refine ⟨12559865217175302011914391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8373243478116868007942927 12559865217175302011914391)
            ·
              refine ⟨18839797825762953017871587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12559865217175302011914391 18839797825762953017871587)
              ·
                refine ⟨28259696738644429526807381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18839797825762953017871587 28259696738644429526807381)
                ·
                  refine ⟨165584160577994704258637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28259696738644429526807381 165584160577994704258637)
                  ·
                    rfl

theorem cell22_1451133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_1451133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451133 prefixEnd_1451133 := by exact prefixLift 1451133
  have htrace : WordTrace (prefixWord ++ tailWord_1451133) baseStart_1451133 baseEnd_1451133 := by
    simpa [prefixWord, tailWord_1451133, baseEnd_1451133] using wordTrace_append hprefix tailTrace_1451133
  have hstable : (prefixWord ++ tailWord_1451133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451133).length < 2 ^ (prefixWord ++ tailWord_1451133).sum := by decide
  have hdescent : baseEnd_1451133 < baseStart_1451133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451148 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 4, 5]
def baseStart_1451148 : Nat := 118140960795 + 1451148 * 2 ^ 59
def prefixEnd_1451148 : Nat := 4983230072969 + 3 ^ 40 * 1451148 * 2
def baseEnd_1451148 : Nat := 496757616540529073650865

theorem tailTrace_1451148 : CollatzResearch.WordTrace tailWord_1451148 prefixEnd_1451148 496757616540529073650865 := by
  unfold tailWord_1451148
  simp only [CollatzResearch.WordTrace]
  refine ⟨26463857873373053596125049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35285143831164071461500065 26463857873373053596125049)
  ·
    refine ⟨19847893405029790197093787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26463857873373053596125049 19847893405029790197093787)
    ·
      refine ⟨29771840107544685295640681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19847893405029790197093787 29771840107544685295640681)
      ·
        refine ⟨22328880080658513971730511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29771840107544685295640681 22328880080658513971730511)
        ·
          refine ⟨33493320120987770957595767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22328880080658513971730511 33493320120987770957595767)
          ·
            refine ⟨50239980181481656436393651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33493320120987770957595767 50239980181481656436393651)
            ·
              refine ⟨75359970272222484654590477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50239980181481656436393651 75359970272222484654590477)
              ·
                refine ⟨28259988852083431745471429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75359970272222484654590477 28259988852083431745471429)
                ·
                  refine ⟨5298747909765643452275893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28259988852083431745471429 5298747909765643452275893)
                  ·
                    refine ⟨496757616540529073650865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5298747909765643452275893 496757616540529073650865)
                    ·
                      rfl

theorem cell22_1451148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_1451148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451148 prefixEnd_1451148 := by exact prefixLift 1451148
  have htrace : WordTrace (prefixWord ++ tailWord_1451148) baseStart_1451148 baseEnd_1451148 := by
    simpa [prefixWord, tailWord_1451148, baseEnd_1451148] using wordTrace_append hprefix tailTrace_1451148
  have hstable : (prefixWord ++ tailWord_1451148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451148).length < 2 ^ (prefixWord ++ tailWord_1451148).sum := by decide
  have hdescent : baseEnd_1451148 < baseStart_1451148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451150 : List Nat := [4, 1, 1, 3, 2, 1, 2, 1, 7]
def baseStart_1451150 : Nat := 118140960795 + 1451150 * 2 ^ 59
def prefixEnd_1451150 : Nat := 4983230072969 + 3 ^ 40 * 1451150 * 2
def baseEnd_1451150 : Nat := 165586100393800578366953

theorem tailTrace_1451150 : CollatzResearch.WordTrace tailWord_1451150 prefixEnd_1451150 165586100393800578366953 := by
  unfold tailWord_1451150
  simp only [CollatzResearch.WordTrace]
  refine ⟨6615973586592357691727863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35285192461825907689215269 6615973586592357691727863)
  ·
    refine ⟨9923960379888536537591795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6615973586592357691727863 9923960379888536537591795)
    ·
      refine ⟨14885940569832804806387693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9923960379888536537591795 14885940569832804806387693)
      ·
        refine ⟨5582227713687301802395385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14885940569832804806387693 5582227713687301802395385)
        ·
          refine ⟨4186670785265476351796539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5582227713687301802395385 4186670785265476351796539)
          ·
            refine ⟨6280006177898214527694809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4186670785265476351796539 6280006177898214527694809)
            ·
              refine ⟨4710004633423660895771107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6280006177898214527694809 4710004633423660895771107)
              ·
                refine ⟨7065006950135491343656661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4710004633423660895771107 7065006950135491343656661)
                ·
                  refine ⟨165586100393800578366953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7065006950135491343656661 165586100393800578366953)
                  ·
                    rfl

theorem cell22_1451150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_1451150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451150 prefixEnd_1451150 := by exact prefixLift 1451150
  have htrace : WordTrace (prefixWord ++ tailWord_1451150) baseStart_1451150 baseEnd_1451150 := by
    simpa [prefixWord, tailWord_1451150, baseEnd_1451150] using wordTrace_append hprefix tailTrace_1451150
  have hstable : (prefixWord ++ tailWord_1451150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451150).length < 2 ^ (prefixWord ++ tailWord_1451150).sum := by decide
  have hdescent : baseEnd_1451150 < baseStart_1451150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451154 : List Nat := [3, 2, 3, 1, 1, 4, 1, 1, 3, 3]
def baseStart_1451154 : Nat := 118140960795 + 1451154 * 2 ^ 59
def prefixEnd_1451154 : Nat := 4983230072969 + 3 ^ 40 * 1451154 * 2
def baseEnd_1451154 : Nat := 496759670463147058000847

theorem tailTrace_1451154 : CollatzResearch.WordTrace tailWord_1451154 prefixEnd_1451154 496759670463147058000847 := by
  unfold tailWord_1451154
  simp only [CollatzResearch.WordTrace]
  refine ⟨13231983646181092554242129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35285289723149580144645677 13231983646181092554242129)
  ·
    refine ⟨9923987734635819415681597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13231983646181092554242129 9923987734635819415681597)
    ·
      refine ⟨3721495400488432280880599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9923987734635819415681597 3721495400488432280880599)
      ·
        refine ⟨5582243100732648421320899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3721495400488432280880599 5582243100732648421320899)
        ·
          refine ⟨8373364651098972631981349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5582243100732648421320899 8373364651098972631981349)
          ·
            refine ⟨1570005872081057368496503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8373364651098972631981349 1570005872081057368496503)
            ·
              refine ⟨2355008808121586052744755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1570005872081057368496503 2355008808121586052744755)
              ·
                refine ⟨3532513212182379079117133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2355008808121586052744755 3532513212182379079117133)
                ·
                  refine ⟨1324692454568392154668925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3532513212182379079117133 1324692454568392154668925)
                  ·
                    refine ⟨496759670463147058000847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1324692454568392154668925 496759670463147058000847)
                    ·
                      rfl

theorem cell22_1451154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_1451154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451154 prefixEnd_1451154 := by exact prefixLift 1451154
  have htrace : WordTrace (prefixWord ++ tailWord_1451154) baseStart_1451154 baseEnd_1451154 := by
    simpa [prefixWord, tailWord_1451154, baseEnd_1451154] using wordTrace_append hprefix tailTrace_1451154
  have hstable : (prefixWord ++ tailWord_1451154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451154).length < 2 ^ (prefixWord ++ tailWord_1451154).sum := by decide
  have hdescent : baseEnd_1451154 < baseStart_1451154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451167 : List Nat := [1, 1, 2, 6, 2, 1, 1, 3, 5]
def baseStart_1451167 : Nat := 118140960795 + 1451167 * 2 ^ 59
def prefixEnd_1451167 : Nat := 4983230072969 + 3 ^ 40 * 1451167 * 2
def baseEnd_1451167 : Nat := 165588040209606452475269

theorem tailTrace_1451167 : CollatzResearch.WordTrace tailWord_1451167 prefixEnd_1451167 165588040209606452475269 := by
  unfold tailWord_1451167
  simp only [CollatzResearch.WordTrace]
  refine ⟨52928408733677273437191755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35285605822451515624794503 52928408733677273437191755)
  ·
    refine ⟨79392613100515910155787633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52928408733677273437191755 79392613100515910155787633)
    ·
      refine ⟨59544459825386932616840725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79392613100515910155787633 59544459825386932616840725)
      ·
        refine ⟨2791146554315012466414409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59544459825386932616840725 2791146554315012466414409)
        ·
          refine ⟨2093359915736259349810807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2791146554315012466414409 2093359915736259349810807)
          ·
            refine ⟨3140039873604389024716211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2093359915736259349810807 3140039873604389024716211)
            ·
              refine ⟨4710059810406583537074317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3140039873604389024716211 4710059810406583537074317)
              ·
                refine ⟨1766272428902468826402869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4710059810406583537074317 1766272428902468826402869)
                ·
                  refine ⟨165588040209606452475269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1766272428902468826402869 165588040209606452475269)
                  ·
                    rfl

theorem cell22_1451167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 5].length) (baseStart_1451167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451167 prefixEnd_1451167 := by exact prefixLift 1451167
  have htrace : WordTrace (prefixWord ++ tailWord_1451167) baseStart_1451167 baseEnd_1451167 := by
    simpa [prefixWord, tailWord_1451167, baseEnd_1451167] using wordTrace_append hprefix tailTrace_1451167
  have hstable : (prefixWord ++ tailWord_1451167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451167).length < 2 ^ (prefixWord ++ tailWord_1451167).sum := by decide
  have hdescent : baseEnd_1451167 < baseStart_1451167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451180 : List Nat := [2, 2, 1, 1, 1, 1, 1, 8, 1, 4]
def baseStart_1451180 : Nat := 118140960795 + 1451180 * 2 ^ 59
def prefixEnd_1451180 : Nat := 4983230072969 + 3 ^ 40 * 1451180 * 2
def baseEnd_1451180 : Nat := 496768570794491656850767

theorem tailTrace_1451180 : CollatzResearch.WordTrace tailWord_1451180 prefixEnd_1451180 496768570794491656850767 := by
  unfold tailWord_1451180
  simp only [CollatzResearch.WordTrace]
  refine ⟨26464441441315088328707497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35285921921753451104943329 26464441441315088328707497)
  ·
    refine ⟨19848331080986316246530623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26464441441315088328707497 19848331080986316246530623)
    ·
      refine ⟨29772496621479474369795935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19848331080986316246530623 29772496621479474369795935)
      ·
        refine ⟨44658744932219211554693903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29772496621479474369795935 44658744932219211554693903)
        ·
          refine ⟨66988117398328817332040855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44658744932219211554693903 66988117398328817332040855)
          ·
            refine ⟨100482176097493225998061283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66988117398328817332040855 100482176097493225998061283)
            ·
              refine ⟨150723264146239838997091925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100482176097493225998061283 150723264146239838997091925)
              ·
                refine ⟨1766288251713748113247171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 150723264146239838997091925 1766288251713748113247171)
                ·
                  refine ⟨2649432377570622169870757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1766288251713748113247171 2649432377570622169870757)
                  ·
                    refine ⟨496768570794491656850767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2649432377570622169870757 496768570794491656850767)
                    ·
                      rfl

theorem cell22_1451180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_1451180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451180 prefixEnd_1451180 := by exact prefixLift 1451180
  have htrace : WordTrace (prefixWord ++ tailWord_1451180) baseStart_1451180 baseEnd_1451180 := by
    simpa [prefixWord, tailWord_1451180, baseEnd_1451180] using wordTrace_append hprefix tailTrace_1451180
  have hstable : (prefixWord ++ tailWord_1451180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451180).length < 2 ^ (prefixWord ++ tailWord_1451180).sum := by decide
  have hdescent : baseEnd_1451180 < baseStart_1451180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451242 : List Nat := [3, 1, 3, 1, 1, 3, 3, 1, 2, 4]
def baseStart_1451242 : Nat := 118140960795 + 1451242 * 2 ^ 59
def prefixEnd_1451242 : Nat := 4983230072969 + 3 ^ 40 * 1451242 * 2
def baseEnd_1451242 : Nat := 496789794661544161800577

theorem tailTrace_1451242 : CollatzResearch.WordTrace tailWord_1451242 prefixEnd_1451242 496789794661544161800577 := by
  unfold tailWord_1451242
  simp only [CollatzResearch.WordTrace]
  refine ⟨13232786052101390311542995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35287429472270374164114653 13232786052101390311542995)
  ·
    refine ⟨19849179078152085467314493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13232786052101390311542995 19849179078152085467314493)
    ·
      refine ⟨7443442154307032050242935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19849179078152085467314493 7443442154307032050242935)
      ·
        refine ⟨11165163231460548075364403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7443442154307032050242935 11165163231460548075364403)
        ·
          refine ⟨16747744847190822113046605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11165163231460548075364403 16747744847190822113046605)
          ·
            refine ⟨6280404317696558292392477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16747744847190822113046605 6280404317696558292392477)
            ·
              refine ⟨2355151619136209359647179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6280404317696558292392477 2355151619136209359647179)
              ·
                refine ⟨3532727428704314039470769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2355151619136209359647179 3532727428704314039470769)
                ·
                  refine ⟨2649545571528235529603077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3532727428704314039470769 2649545571528235529603077)
                  ·
                    refine ⟨496789794661544161800577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2649545571528235529603077 496789794661544161800577)
                    ·
                      rfl

theorem cell22_1451242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_1451242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451242 prefixEnd_1451242 := by exact prefixLift 1451242
  have htrace : WordTrace (prefixWord ++ tailWord_1451242) baseStart_1451242 baseEnd_1451242 := by
    simpa [prefixWord, tailWord_1451242, baseEnd_1451242] using wordTrace_append hprefix tailTrace_1451242
  have hstable : (prefixWord ++ tailWord_1451242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451242).length < 2 ^ (prefixWord ++ tailWord_1451242).sum := by decide
  have hdescent : baseEnd_1451242 < baseStart_1451242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451349 : List Nat := [1, 3, 2, 2, 3, 1, 3, 2, 1, 4]
def baseStart_1451349 : Nat := 118140960795 + 1451349 * 2 ^ 59
def prefixEnd_1451349 : Nat := 4983230072969 + 3 ^ 40 * 1451349 * 2
def baseEnd_1451349 : Nat := 496826422948231549375249

theorem tailTrace_1451349 : CollatzResearch.WordTrace tailWord_1451349 prefixEnd_1451349 496826422948231549375249 := by
  unfold tailWord_1451349
  simp only [CollatzResearch.WordTrace]
  refine ⟨52935046819017918520317101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35290031212678612346878067 52935046819017918520317101)
  ·
    refine ⟨19850642557131719445118913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52935046819017918520317101 19850642557131719445118913)
    ·
      refine ⟨14887981917848789583839185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19850642557131719445118913 14887981917848789583839185)
      ·
        refine ⟨11165986438386592187879389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14887981917848789583839185 11165986438386592187879389)
        ·
          refine ⟨4187244914394972070454771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11165986438386592187879389 4187244914394972070454771)
          ·
            refine ⟨6280867371592458105682157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4187244914394972070454771 6280867371592458105682157)
            ·
              refine ⟨2355325264347171789630809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6280867371592458105682157 2355325264347171789630809)
              ·
                refine ⟨1766493948260378842223107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2355325264347171789630809 1766493948260378842223107)
                ·
                  refine ⟨2649740922390568263334661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1766493948260378842223107 2649740922390568263334661)
                  ·
                    refine ⟨496826422948231549375249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2649740922390568263334661 496826422948231549375249)
                    ·
                      rfl

theorem cell22_1451349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_1451349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451349 prefixEnd_1451349 := by exact prefixLift 1451349
  have htrace : WordTrace (prefixWord ++ tailWord_1451349) baseStart_1451349 baseEnd_1451349 := by
    simpa [prefixWord, tailWord_1451349, baseEnd_1451349] using wordTrace_append hprefix tailTrace_1451349
  have hstable : (prefixWord ++ tailWord_1451349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451349).length < 2 ^ (prefixWord ++ tailWord_1451349).sum := by decide
  have hdescent : baseEnd_1451349 < baseStart_1451349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451377 : List Nat := [1, 2, 2, 2, 1, 2, 4, 2, 2, 4]
def baseStart_1451377 : Nat := 118140960795 + 1451377 * 2 ^ 59
def prefixEnd_1451377 : Nat := 4983230072969 + 3 ^ 40 * 1451377 * 2
def baseEnd_1451377 : Nat := 496836007920448809675163

theorem tailTrace_1451377 : CollatzResearch.WordTrace tailWord_1451377 prefixEnd_1451377 496836007920448809675163 := by
  unfold tailWord_1451377
  simp only [CollatzResearch.WordTrace]
  refine ⟨52936068062916479302336385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35290712041944319534890923 52936068062916479302336385)
  ·
    refine ⟨39702051047187359476752289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52936068062916479302336385 39702051047187359476752289)
    ·
      refine ⟨29776538285390519607564217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39702051047187359476752289 29776538285390519607564217)
      ·
        refine ⟨22332403714042889705673163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29776538285390519607564217 22332403714042889705673163)
        ·
          refine ⟨33498605571064334558509745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22332403714042889705673163 33498605571064334558509745)
          ·
            refine ⟨25123954178298250918882309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33498605571064334558509745 25123954178298250918882309)
            ·
              refine ⟨4710741408430922047290433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25123954178298250918882309 4710741408430922047290433)
              ·
                refine ⟨3533056056323191535467825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4710741408430922047290433 3533056056323191535467825)
                ·
                  refine ⟨2649792042242393651600869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3533056056323191535467825 2649792042242393651600869)
                  ·
                    refine ⟨496836007920448809675163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2649792042242393651600869 496836007920448809675163)
                    ·
                      rfl

theorem cell22_1451377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_1451377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451377 prefixEnd_1451377 := by exact prefixLift 1451377
  have htrace : WordTrace (prefixWord ++ tailWord_1451377) baseStart_1451377 baseEnd_1451377 := by
    simpa [prefixWord, tailWord_1451377, baseEnd_1451377] using wordTrace_append hprefix tailTrace_1451377
  have hstable : (prefixWord ++ tailWord_1451377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451377).length < 2 ^ (prefixWord ++ tailWord_1451377).sum := by decide
  have hdescent : baseEnd_1451377 < baseStart_1451377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451381 : List Nat := [1, 3, 4, 1, 3, 1, 1, 4, 4]
def baseStart_1451381 : Nat := 118140960795 + 1451381 * 2 ^ 59
def prefixEnd_1451381 : Nat := 4983230072969 + 3 ^ 40 * 1451381 * 2
def baseEnd_1451381 : Nat := 165612459067398044191717

theorem tailTrace_1451381 : CollatzResearch.WordTrace tailWord_1451381 prefixEnd_1451381 165612459067398044191717 := by
  unfold tailWord_1451381
  simp only [CollatzResearch.WordTrace]
  refine ⟨52936213954901987985481997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35290809303267991990321331 52936213954901987985481997)
  ·
    refine ⟨19851080233088245494555749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52936213954901987985481997 19851080233088245494555749)
    ·
      refine ⟨3722077543704046030229203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19851080233088245494555749 3722077543704046030229203)
      ·
        refine ⟨5583116315556069045343805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3722077543704046030229203 5583116315556069045343805)
        ·
          refine ⟨2093668618333525892003927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5583116315556069045343805 2093668618333525892003927)
          ·
            refine ⟨3140502927500288838005891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2093668618333525892003927 3140502927500288838005891)
            ·
              refine ⟨4710754391250433257008837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3140502927500288838005891 4710754391250433257008837)
              ·
                refine ⟨883266448359456235689157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4710754391250433257008837 883266448359456235689157)
                ·
                  refine ⟨165612459067398044191717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 883266448359456235689157 165612459067398044191717)
                  ·
                    rfl

theorem cell22_1451381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4, 4].length) (baseStart_1451381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451381 prefixEnd_1451381 := by exact prefixLift 1451381
  have htrace : WordTrace (prefixWord ++ tailWord_1451381) baseStart_1451381 baseEnd_1451381 := by
    simpa [prefixWord, tailWord_1451381, baseEnd_1451381] using wordTrace_append hprefix tailTrace_1451381
  have hstable : (prefixWord ++ tailWord_1451381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451381).length < 2 ^ (prefixWord ++ tailWord_1451381).sum := by decide
  have hdescent : baseEnd_1451381 < baseStart_1451381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451441 : List Nat := [1, 2, 2, 4, 1, 1, 1, 6, 1, 3]
def baseStart_1451441 : Nat := 118140960795 + 1451441 * 2 ^ 59
def prefixEnd_1451441 : Nat := 4983230072969 + 3 ^ 40 * 1451441 * 2
def baseEnd_1451441 : Nat := 496857916428373976074967

theorem tailTrace_1451441 : CollatzResearch.WordTrace tailWord_1451441 prefixEnd_1451441 496857916428373976074967 := by
  unfold tailWord_1451441
  simp only [CollatzResearch.WordTrace]
  refine ⟨52938402334684618232666177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35292268223123078821777451 52938402334684618232666177)
  ·
    refine ⟨39703801751013463674499633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52938402334684618232666177 39703801751013463674499633)
    ·
      refine ⟨29777851313260097755874725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39703801751013463674499633 29777851313260097755874725)
      ·
        refine ⟨5583347121236268329226511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29777851313260097755874725 5583347121236268329226511)
        ·
          refine ⟨8375020681854402493839767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5583347121236268329226511 8375020681854402493839767)
          ·
            refine ⟨12562531022781603740759651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8375020681854402493839767 12562531022781603740759651)
            ·
              refine ⟨18843796534172405611139477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12562531022781603740759651 18843796534172405611139477)
              ·
                refine ⟨883302962539331513022163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18843796534172405611139477 883302962539331513022163)
                ·
                  refine ⟨1324954443808997269533245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 883302962539331513022163 1324954443808997269533245)
                  ·
                    refine ⟨496857916428373976074967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1324954443808997269533245 496857916428373976074967)
                    ·
                      rfl

theorem cell22_1451441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6, 1, 3].length) (baseStart_1451441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451441 prefixEnd_1451441 := by exact prefixLift 1451441
  have htrace : WordTrace (prefixWord ++ tailWord_1451441) baseStart_1451441 baseEnd_1451441 := by
    simpa [prefixWord, tailWord_1451441, baseEnd_1451441] using wordTrace_append hprefix tailTrace_1451441
  have hstable : (prefixWord ++ tailWord_1451441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451441).length < 2 ^ (prefixWord ++ tailWord_1451441).sum := by decide
  have hdescent : baseEnd_1451441 < baseStart_1451441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451467 : List Nat := [1, 1, 1, 1, 3, 3, 2, 3, 3, 4]
def baseStart_1451467 : Nat := 118140960795 + 1451467 * 2 ^ 59
def prefixEnd_1451467 : Nat := 4983230072969 + 3 ^ 40 * 1451467 * 2
def baseEnd_1451467 : Nat := 496866816759718574924887

theorem tailTrace_1451467 : CollatzResearch.WordTrace tailWord_1451467 prefixEnd_1451467 496866816759718574924887 := by
  unfold tailWord_1451467
  simp only [CollatzResearch.WordTrace]
  refine ⟨52939350632590424673112655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35292900421726949782075103 52939350632590424673112655)
  ·
    refine ⟨79409025948885637009668983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52939350632590424673112655 79409025948885637009668983)
    ·
      refine ⟨119113538923328455514503475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79409025948885637009668983 119113538923328455514503475)
      ·
        refine ⟨178670308384992683271755213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119113538923328455514503475 178670308384992683271755213)
        ·
          refine ⟨67001365644372256226908205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178670308384992683271755213 67001365644372256226908205)
          ·
            refine ⟨25125512116639596085090577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67001365644372256226908205 25125512116639596085090577)
            ·
              refine ⟨18844134087479697063817933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25125512116639596085090577 18844134087479697063817933)
              ·
                refine ⟨7066550282804886398931725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18844134087479697063817933 7066550282804886398931725)
                ·
                  refine ⟨2649956356051832399599397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7066550282804886398931725 2649956356051832399599397)
                  ·
                    refine ⟨496866816759718574924887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2649956356051832399599397 496866816759718574924887)
                    ·
                      rfl

theorem cell22_1451467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 4].length) (baseStart_1451467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451467 prefixEnd_1451467 := by exact prefixLift 1451467
  have htrace : WordTrace (prefixWord ++ tailWord_1451467) baseStart_1451467 baseEnd_1451467 := by
    simpa [prefixWord, tailWord_1451467, baseEnd_1451467] using wordTrace_append hprefix tailTrace_1451467
  have hstable : (prefixWord ++ tailWord_1451467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451467).length < 2 ^ (prefixWord ++ tailWord_1451467).sum := by decide
  have hdescent : baseEnd_1451467 < baseStart_1451467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451518 : List Nat := [4, 2, 2, 3, 1, 1, 1, 1, 3, 4]
def baseStart_1451518 : Nat := 118140960795 + 1451518 * 2 ^ 59
def prefixEnd_1451518 : Nat := 4983230072969 + 3 ^ 40 * 1451518 * 2
def baseEnd_1451518 : Nat := 496884275101971441899731

theorem tailTrace_1451518 : CollatzResearch.WordTrace tailWord_1451518 prefixEnd_1451518 496884275101971441899731 := by
  unfold tailWord_1451518
  simp only [CollatzResearch.WordTrace]
  refine ⟨6617651344425707547902401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35294140503603773588812805 6617651344425707547902401)
  ·
    refine ⟨4963238508319280660926801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6617651344425707547902401 4963238508319280660926801)
    ·
      refine ⟨3722428881239460495695101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4963238508319280660926801 3722428881239460495695101)
      ·
        refine ⟨1395910830464797685885663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3722428881239460495695101 1395910830464797685885663)
        ·
          refine ⟨2093866245697196528828495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1395910830464797685885663 2093866245697196528828495)
          ·
            refine ⟨3140799368545794793242743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2093866245697196528828495 3140799368545794793242743)
            ·
              refine ⟨4711199052818692189864115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3140799368545794793242743 4711199052818692189864115)
              ·
                refine ⟨7066798579228038284796173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4711199052818692189864115 7066798579228038284796173)
                ·
                  refine ⟨2650049467210514356798565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7066798579228038284796173 2650049467210514356798565)
                  ·
                    refine ⟨496884275101971441899731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2650049467210514356798565 496884275101971441899731)
                    ·
                      rfl

theorem cell22_1451518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_1451518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451518 prefixEnd_1451518 := by exact prefixLift 1451518
  have htrace : WordTrace (prefixWord ++ tailWord_1451518) baseStart_1451518 baseEnd_1451518 := by
    simpa [prefixWord, tailWord_1451518, baseEnd_1451518] using wordTrace_append hprefix tailTrace_1451518
  have hstable : (prefixWord ++ tailWord_1451518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451518).length < 2 ^ (prefixWord ++ tailWord_1451518).sum := by decide
  have hdescent : baseEnd_1451518 < baseStart_1451518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451529 : List Nat := [1, 2, 1, 1, 3, 1, 6, 1, 2, 4]
def baseStart_1451529 : Nat := 118140960795 + 1451529 * 2 ^ 59
def prefixEnd_1451529 : Nat := 4983230072969 + 3 ^ 40 * 1451529 * 2
def baseEnd_1451529 : Nat := 496888040626771079874697

theorem tailTrace_1451529 : CollatzResearch.WordTrace tailWord_1451529 prefixEnd_1451529 496888040626771079874697 := by
  unfold tailWord_1451529
  simp only [CollatzResearch.WordTrace]
  refine ⟨52941611958365809261869641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35294407972243872841246427 52941611958365809261869641)
  ·
    refine ⟨39706208968774356946402231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52941611958365809261869641 39706208968774356946402231)
    ·
      refine ⟨59559313453161535419603347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39706208968774356946402231 59559313453161535419603347)
      ·
        refine ⟨89338970179742303129405021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59559313453161535419603347 89338970179742303129405021)
        ·
          refine ⟨33502113817403363673526883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89338970179742303129405021 33502113817403363673526883)
          ·
            refine ⟨50253170726105045510290325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33502113817403363673526883 50253170726105045510290325)
            ·
              refine ⟨2355617377786174008294859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50253170726105045510290325 2355617377786174008294859)
              ·
                refine ⟨3533426066679261012442289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2355617377786174008294859 3533426066679261012442289)
                ·
                  refine ⟨2650069550009445759331717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3533426066679261012442289 2650069550009445759331717)
                  ·
                    refine ⟨496888040626771079874697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2650069550009445759331717 496888040626771079874697)
                    ·
                      rfl

theorem cell22_1451529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 4].length) (baseStart_1451529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451529 prefixEnd_1451529 := by exact prefixLift 1451529
  have htrace : WordTrace (prefixWord ++ tailWord_1451529) baseStart_1451529 baseEnd_1451529 := by
    simpa [prefixWord, tailWord_1451529, baseEnd_1451529] using wordTrace_append hprefix tailTrace_1451529
  have hstable : (prefixWord ++ tailWord_1451529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451529).length < 2 ^ (prefixWord ++ tailWord_1451529).sum := by decide
  have hdescent : baseEnd_1451529 < baseStart_1451529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451544 : List Nat := [2, 1, 2, 3, 5, 9]
def baseStart_1451544 : Nat := 118140960795 + 1451544 * 2 ^ 59
def prefixEnd_1451544 : Nat := 4983230072969 + 3 ^ 40 * 1451544 * 2
def baseEnd_1451544 : Nat := 6134483647324889391971

theorem tailTrace_1451544 : CollatzResearch.WordTrace tailWord_1451544 prefixEnd_1451544 6134483647324889391971 := by
  unfold tailWord_1451544
  simp only [CollatzResearch.WordTrace]
  refine ⟨26471079526655733411832843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35294772702207644549110457 26471079526655733411832843)
  ·
    refine ⟨39706619289983600117749265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26471079526655733411832843 39706619289983600117749265)
    ·
      refine ⟨29779964467487700088311949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39706619289983600117749265 29779964467487700088311949)
      ·
        refine ⟨11167486675307887533116981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29779964467487700088311949 11167486675307887533116981)
        ·
          refine ⟨1046951875810114456229717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11167486675307887533116981 1046951875810114456229717)
          ·
            refine ⟨6134483647324889391971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1046951875810114456229717 6134483647324889391971)
            ·
              rfl

theorem cell22_1451544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 9].length) (baseStart_1451544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451544 prefixEnd_1451544 := by exact prefixLift 1451544
  have htrace : WordTrace (prefixWord ++ tailWord_1451544) baseStart_1451544 baseEnd_1451544 := by
    simpa [prefixWord, tailWord_1451544, baseEnd_1451544] using wordTrace_append hprefix tailTrace_1451544
  have hstable : (prefixWord ++ tailWord_1451544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451544).length < 2 ^ (prefixWord ++ tailWord_1451544).sum := by decide
  have hdescent : baseEnd_1451544 < baseStart_1451544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451576 : List Nat := [2, 1, 2, 1, 4, 3, 1, 2, 3, 3]
def baseStart_1451576 : Nat := 118140960795 + 1451576 * 2 ^ 59
def prefixEnd_1451576 : Nat := 4983230072969 + 3 ^ 40 * 1451576 * 2
def baseEnd_1451576 : Nat := 496904129687278623949553

theorem tailTrace_1451576 : CollatzResearch.WordTrace tailWord_1451576 prefixEnd_1451576 496904129687278623949553 := by
  unfold tailWord_1451576
  simp only [CollatzResearch.WordTrace]
  refine ⟨26471663094597768144415291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35295550792797024192553721 26471663094597768144415291)
  ·
    refine ⟨39707494641896652216622937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26471663094597768144415291 39707494641896652216622937)
    ·
      refine ⟨29780620981422489162467203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39707494641896652216622937 29780620981422489162467203)
      ·
        refine ⟨44670931472133733743700805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29780620981422489162467203 44670931472133733743700805)
        ·
          refine ⟨8375799651025075076943901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44670931472133733743700805 8375799651025075076943901)
          ·
            refine ⟨3140924869134403153853963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8375799651025075076943901 3140924869134403153853963)
            ·
              refine ⟨4711387303701604730780945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3140924869134403153853963 4711387303701604730780945)
              ·
                refine ⟨3533540477776203548085709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4711387303701604730780945 3533540477776203548085709)
                ·
                  refine ⟨1325077679166076330532141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3533540477776203548085709 1325077679166076330532141)
                  ·
                    refine ⟨496904129687278623949553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1325077679166076330532141 496904129687278623949553)
                    ·
                      rfl

theorem cell22_1451576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 3, 3].length) (baseStart_1451576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451576 prefixEnd_1451576 := by exact prefixLift 1451576
  have htrace : WordTrace (prefixWord ++ tailWord_1451576) baseStart_1451576 baseEnd_1451576 := by
    simpa [prefixWord, tailWord_1451576, baseEnd_1451576] using wordTrace_append hprefix tailTrace_1451576
  have hstable : (prefixWord ++ tailWord_1451576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451576).length < 2 ^ (prefixWord ++ tailWord_1451576).sum := by decide
  have hdescent : baseEnd_1451576 < baseStart_1451576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451604 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_1451604 : Nat := 118140960795 + 1451604 * 2 ^ 59
def prefixEnd_1451604 : Nat := 4983230072969 + 3 ^ 40 * 1451604 * 2
def baseEnd_1451604 : Nat := 496913714659495884249467

theorem tailTrace_1451604 : CollatzResearch.WordTrace tailWord_1451604 prefixEnd_1451604 496913714659495884249467 := by
  unfold tailWord_1451604
  simp only [CollatzResearch.WordTrace]
  refine ⟨26472173716547048535424933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35296231622062731380566577 26472173716547048535424933)
  ·
    refine ⟨4963532571852571600392175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26472173716547048535424933 4963532571852571600392175)
    ·
      refine ⟨7445298857778857400588263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4963532571852571600392175 7445298857778857400588263)
      ·
        refine ⟨11167948286668286100882395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7445298857778857400588263 11167948286668286100882395)
        ·
          refine ⟨16751922430002429151323593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11167948286668286100882395 16751922430002429151323593)
          ·
            refine ⟨12563941822501821863492695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16751922430002429151323593 12563941822501821863492695)
            ·
              refine ⟨18845912733752732795239043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12563941822501821863492695 18845912733752732795239043)
              ·
                refine ⟨28268869100629099192858565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18845912733752732795239043 28268869100629099192858565)
                ·
                  refine ⟨5300412956367956098660981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28268869100629099192858565 5300412956367956098660981)
                  ·
                    refine ⟨496913714659495884249467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5300412956367956098660981 496913714659495884249467)
                    ·
                      rfl

theorem cell22_1451604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_1451604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451604 prefixEnd_1451604 := by exact prefixLift 1451604
  have htrace : WordTrace (prefixWord ++ tailWord_1451604) baseStart_1451604 baseEnd_1451604 := by
    simpa [prefixWord, tailWord_1451604, baseEnd_1451604] using wordTrace_append hprefix tailTrace_1451604
  have hstable : (prefixWord ++ tailWord_1451604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451604).length < 2 ^ (prefixWord ++ tailWord_1451604).sum := by decide
  have hdescent : baseEnd_1451604 < baseStart_1451604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451786 : List Nat := [3, 1, 2, 2, 1, 3, 1, 3, 6]
def baseStart_1451786 : Nat := 118140960795 + 1451786 * 2 ^ 59
def prefixEnd_1451786 : Nat := 4983230072969 + 3 ^ 40 * 1451786 * 2
def baseEnd_1451786 : Nat := 165658672326302692066303

theorem tailTrace_1451786 : CollatzResearch.WordTrace tailWord_1451786 prefixEnd_1451786 165658672326302692066303 := by
  unfold tailWord_1451786
  simp only [CollatzResearch.WordTrace]
  refine ⟨13237746379608685538493803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35300657012289828102650141 13237746379608685538493803)
  ·
    refine ⟨19856619569413028307740705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13237746379608685538493803 19856619569413028307740705)
    ·
      refine ⟨14892464677059771230805529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19856619569413028307740705 14892464677059771230805529)
      ·
        refine ⟨11169348507794828423104147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14892464677059771230805529 11169348507794828423104147)
        ·
          refine ⟨16754022761692242634656221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11169348507794828423104147 16754022761692242634656221)
          ·
            refine ⟨6282758535634590987996083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16754022761692242634656221 6282758535634590987996083)
            ·
              refine ⟨9424137803451886481994125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6282758535634590987996083 9424137803451886481994125)
              ·
                refine ⟨3534051676294457430747797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9424137803451886481994125 3534051676294457430747797)
                ·
                  refine ⟨165658672326302692066303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3534051676294457430747797 165658672326302692066303)
                  ·
                    rfl

theorem cell22_1451786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 6].length) (baseStart_1451786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451786 prefixEnd_1451786 := by exact prefixLift 1451786
  have htrace : WordTrace (prefixWord ++ tailWord_1451786) baseStart_1451786 baseEnd_1451786 := by
    simpa [prefixWord, tailWord_1451786, baseEnd_1451786] using wordTrace_append hprefix tailTrace_1451786
  have hstable : (prefixWord ++ tailWord_1451786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451786).length < 2 ^ (prefixWord ++ tailWord_1451786).sum := by decide
  have hdescent : baseEnd_1451786 < baseStart_1451786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451820 : List Nat := [2, 2, 1, 1, 1, 7, 1, 3, 4]
def baseStart_1451820 : Nat := 118140960795 + 1451820 * 2 ^ 59
def prefixEnd_1451820 : Nat := 4983230072969 + 3 ^ 40 * 1451820 * 2
def baseEnd_1451820 : Nat := 165662551957914440282935

theorem tailTrace_1451820 : CollatzResearch.WordTrace tailWord_1451820 prefixEnd_1451820 165662551957914440282935 := by
  unfold tailWord_1451820
  simp only [CollatzResearch.WordTrace]
  refine ⟨26476112800155782980356457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35301483733541043973808609 26476112800155782980356457)
  ·
    refine ⟨19857084600116837235267343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26476112800155782980356457 19857084600116837235267343)
    ·
      refine ⟨29785626900175255852901015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19857084600116837235267343 29785626900175255852901015)
      ·
        refine ⟨44678440350262883779351523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29785626900175255852901015 44678440350262883779351523)
        ·
          refine ⟨67017660525394325669027285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44678440350262883779351523 67017660525394325669027285)
          ·
            refine ⟨1570726418563929507867827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 67017660525394325669027285 1570726418563929507867827)
            ·
              refine ⟨2356089627845894261801741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1570726418563929507867827 2356089627845894261801741)
              ·
                refine ⟨883533610442210348175653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2356089627845894261801741 883533610442210348175653)
                ·
                  refine ⟨165662551957914440282935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 883533610442210348175653 165662551957914440282935)
                  ·
                    rfl

theorem cell22_1451820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3, 4].length) (baseStart_1451820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451820 prefixEnd_1451820 := by exact prefixLift 1451820
  have htrace : WordTrace (prefixWord ++ tailWord_1451820) baseStart_1451820 baseEnd_1451820 := by
    simpa [prefixWord, tailWord_1451820, baseEnd_1451820] using wordTrace_append hprefix tailTrace_1451820
  have hstable : (prefixWord ++ tailWord_1451820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451820).length < 2 ^ (prefixWord ++ tailWord_1451820).sum := by decide
  have hdescent : baseEnd_1451820 < baseStart_1451820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451837 : List Nat := [1, 4, 1, 4, 1, 2, 3, 2, 4]
def baseStart_1451837 : Nat := 118140960795 + 1451837 * 2 ^ 59
def prefixEnd_1451837 : Nat := 4983230072969 + 3 ^ 40 * 1451837 * 2
def baseEnd_1451837 : Nat := 165664491773720314391251

theorem tailTrace_1451837 : CollatzResearch.WordTrace tailWord_1451837 prefixEnd_1451837 165664491773720314391251 := by
  unfold tailWord_1451837
  simp only [CollatzResearch.WordTrace]
  refine ⟨52952845641249977864081765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35301897094166651909387843 52952845641249977864081765)
  ·
    refine ⟨9928658557734370849515331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52952845641249977864081765 9928658557734370849515331)
    ·
      refine ⟨14892987836601556274272997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9928658557734370849515331 14892987836601556274272997)
      ·
        refine ⟨2792435219362791801426187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14892987836601556274272997 2792435219362791801426187)
        ·
          refine ⟨4188652829044187702139281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2792435219362791801426187 4188652829044187702139281)
          ·
            refine ⟨3141489621783140776604461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4188652829044187702139281 3141489621783140776604461)
            ·
              refine ⟨1178058608168677791226673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3141489621783140776604461 1178058608168677791226673)
              ·
                refine ⟨883543956126508343420005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1178058608168677791226673 883543956126508343420005)
                ·
                  refine ⟨165664491773720314391251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 883543956126508343420005 165664491773720314391251)
                  ·
                    rfl

theorem cell22_1451837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_1451837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451837 prefixEnd_1451837 := by exact prefixLift 1451837
  have htrace : WordTrace (prefixWord ++ tailWord_1451837) baseStart_1451837 baseEnd_1451837 := by
    simpa [prefixWord, tailWord_1451837, baseEnd_1451837] using wordTrace_append hprefix tailTrace_1451837
  have hstable : (prefixWord ++ tailWord_1451837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451837).length < 2 ^ (prefixWord ++ tailWord_1451837).sum := by decide
  have hdescent : baseEnd_1451837 < baseStart_1451837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451891 : List Nat := [1, 1, 1, 2, 2, 1, 3, 4, 2, 5]
def baseStart_1451891 : Nat := 118140960795 + 1451891 * 2 ^ 59
def prefixEnd_1451891 : Nat := 4983230072969 + 3 ^ 40 * 1451891 * 2
def baseEnd_1451891 : Nat := 497011960624722802323587

theorem tailTrace_1451891 : CollatzResearch.WordTrace tailWord_1451891 prefixEnd_1451891 497011960624722802323587 := by
  unfold tailWord_1451891
  simp only [CollatzResearch.WordTrace]
  refine ⟨52954815183054345086547527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35303210122036230057698351 52954815183054345086547527)
  ·
    refine ⟨79432222774581517629821291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52954815183054345086547527 79432222774581517629821291)
    ·
      refine ⟨119148334161872276444731937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79432222774581517629821291 119148334161872276444731937)
      ·
        refine ⟨89361250621404207333548953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119148334161872276444731937 89361250621404207333548953)
        ·
          refine ⟨67020937966053155500161715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89361250621404207333548953 67020937966053155500161715)
          ·
            refine ⟨100531406949079733250242573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67020937966053155500161715 100531406949079733250242573)
            ·
              refine ⟨37699277605904899968840965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100531406949079733250242573 37699277605904899968840965)
              ·
                refine ⟨7068614551107168744157681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37699277605904899968840965 7068614551107168744157681)
                ·
                  refine ⟨5301460913330376558118261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7068614551107168744157681 5301460913330376558118261)
                  ·
                    refine ⟨497011960624722802323587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5301460913330376558118261 497011960624722802323587)
                    ·
                      rfl

theorem cell22_1451891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 5].length) (baseStart_1451891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451891 prefixEnd_1451891 := by exact prefixLift 1451891
  have htrace : WordTrace (prefixWord ++ tailWord_1451891) baseStart_1451891 baseEnd_1451891 := by
    simpa [prefixWord, tailWord_1451891, baseEnd_1451891] using wordTrace_append hprefix tailTrace_1451891
  have hstable : (prefixWord ++ tailWord_1451891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451891).length < 2 ^ (prefixWord ++ tailWord_1451891).sum := by decide
  have hdescent : baseEnd_1451891 < baseStart_1451891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451921 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 8]
def baseStart_1451921 : Nat := 118140960795 + 1451921 * 2 ^ 59
def prefixEnd_1451921 : Nat := 4983230072969 + 3 ^ 40 * 1451921 * 2
def baseEnd_1451921 : Nat := 165674076745937574691165

theorem tailTrace_1451921 : CollatzResearch.WordTrace tailWord_1451921 prefixEnd_1451921 165674076745937574691165 := by
  unfold tailWord_1451921
  simp only [CollatzResearch.WordTrace]
  refine ⟨52955909372945660210139617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35303939581963773473426411 52955909372945660210139617)
  ·
    refine ⟨39716932029709245157604713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52955909372945660210139617 39716932029709245157604713)
    ·
      refine ⟨29787699022281933868203535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39716932029709245157604713 29787699022281933868203535)
      ·
        refine ⟨44681548533422900802305303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29787699022281933868203535 44681548533422900802305303)
        ·
          refine ⟨67022322800134351203457955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44681548533422900802305303 67022322800134351203457955)
          ·
            refine ⟨100533484200201526805186933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67022322800134351203457955 100533484200201526805186933)
            ·
              refine ⟨9425014143768893137986275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100533484200201526805186933 9425014143768893137986275)
              ·
                refine ⟨14137521215653339706979413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9425014143768893137986275 14137521215653339706979413)
                ·
                  refine ⟨165674076745937574691165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14137521215653339706979413 165674076745937574691165)
                  ·
                    rfl

theorem cell22_1451921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 8].length) (baseStart_1451921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451921 prefixEnd_1451921 := by exact prefixLift 1451921
  have htrace : WordTrace (prefixWord ++ tailWord_1451921) baseStart_1451921 baseEnd_1451921 := by
    simpa [prefixWord, tailWord_1451921, baseEnd_1451921] using wordTrace_append hprefix tailTrace_1451921
  have hstable : (prefixWord ++ tailWord_1451921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451921).length < 2 ^ (prefixWord ++ tailWord_1451921).sum := by decide
  have hdescent : baseEnd_1451921 < baseStart_1451921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451940 : List Nat := [2, 3, 1, 2, 1, 4, 1, 3, 1, 4]
def baseStart_1451940 : Nat := 118140960795 + 1451940 * 2 ^ 59
def prefixEnd_1451940 : Nat := 4983230072969 + 3 ^ 40 * 1451940 * 2
def baseEnd_1451940 : Nat := 497028734326103007848437

theorem tailTrace_1451940 : CollatzResearch.WordTrace tailWord_1451940 prefixEnd_1451940 497028734326103007848437 := by
  unfold tailWord_1451940
  simp only [CollatzResearch.WordTrace]
  refine ⟨26478301179938413227540637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35304401573251217636720849 26478301179938413227540637)
  ·
    refine ⟨9929362942476904960327739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26478301179938413227540637 9929362942476904960327739)
    ·
      refine ⟨14894044413715357440491609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9929362942476904960327739 14894044413715357440491609)
      ·
        refine ⟨11170533310286518080368707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14894044413715357440491609 11170533310286518080368707)
        ·
          refine ⟨16755799965429777120553061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11170533310286518080368707 16755799965429777120553061)
          ·
            refine ⟨3141712493518083210103699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16755799965429777120553061 3141712493518083210103699)
            ·
              refine ⟨4712568740277124815155549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3141712493518083210103699 4712568740277124815155549)
              ·
                refine ⟨1767213277603921805683331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4712568740277124815155549 1767213277603921805683331)
                ·
                  refine ⟨2650819916405882708524997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1767213277603921805683331 2650819916405882708524997)
                  ·
                    refine ⟨497028734326103007848437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2650819916405882708524997 497028734326103007848437)
                    ·
                      rfl

theorem cell22_1451940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_1451940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451940 prefixEnd_1451940 := by exact prefixLift 1451940
  have htrace : WordTrace (prefixWord ++ tailWord_1451940) baseStart_1451940 baseEnd_1451940 := by
    simpa [prefixWord, tailWord_1451940, baseEnd_1451940] using wordTrace_append hprefix tailTrace_1451940
  have hstable : (prefixWord ++ tailWord_1451940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451940).length < 2 ^ (prefixWord ++ tailWord_1451940).sum := by decide
  have hdescent : baseEnd_1451940 < baseStart_1451940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451944 : List Nat := [2, 1, 6, 2, 1, 2, 1, 2, 5]
def baseStart_1451944 : Nat := 118140960795 + 1451944 * 2 ^ 59
def prefixEnd_1451944 : Nat := 4983230072969 + 3 ^ 40 * 1451944 * 2
def baseEnd_1451944 : Nat := 165676701202616110249475

theorem tailTrace_1451944 : CollatzResearch.WordTrace tailWord_1451944 prefixEnd_1451944 165676701202616110249475 := by
  unfold tailWord_1451944
  simp only [CollatzResearch.WordTrace]
  refine ⟨26478374125931167569113443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35304498834574890092151257 26478374125931167569113443)
  ·
    refine ⟨39717561188896751353670165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26478374125931167569113443 39717561188896751353670165)
    ·
      refine ⟨1861760680729535219703289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39717561188896751353670165 1861760680729535219703289)
      ·
        refine ⟨1396320510547151414777467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1861760680729535219703289 1396320510547151414777467)
        ·
          refine ⟨2094480765820727122166201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1396320510547151414777467 2094480765820727122166201)
          ·
            refine ⟨1570860574365545341624651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2094480765820727122166201 1570860574365545341624651)
            ·
              refine ⟨2356290861548318012436977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1570860574365545341624651 2356290861548318012436977)
              ·
                refine ⟨1767218146161238509327733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2356290861548318012436977 1767218146161238509327733)
                ·
                  refine ⟨165676701202616110249475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1767218146161238509327733 165676701202616110249475)
                  ·
                    rfl

theorem cell22_1451944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 5].length) (baseStart_1451944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1451944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1451944 prefixEnd_1451944 := by exact prefixLift 1451944
  have htrace : WordTrace (prefixWord ++ tailWord_1451944) baseStart_1451944 baseEnd_1451944 := by
    simpa [prefixWord, tailWord_1451944, baseEnd_1451944] using wordTrace_append hprefix tailTrace_1451944
  have hstable : (prefixWord ++ tailWord_1451944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451944).length < 2 ^ (prefixWord ++ tailWord_1451944).sum := by decide
  have hdescent : baseEnd_1451944 < baseStart_1451944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452105 : List Nat := [1, 2, 1, 1, 2, 2, 4, 2, 4, 3]
def baseStart_1452105 : Nat := 118140960795 + 1452105 * 2 ^ 59
def prefixEnd_1452105 : Nat := 4983230072969 + 3 ^ 40 * 1452105 * 2
def baseEnd_1452105 : Nat := 497085217198097577472931

theorem tailTrace_1452105 : CollatzResearch.WordTrace tailWord_1452105 prefixEnd_1452105 497085217198097577472931 := by
  unfold tailWord_1452105
  simp only [CollatzResearch.WordTrace]
  refine ⟨52962620404279059634837769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35308413602852706423225179 52962620404279059634837769)
  ·
    refine ⟨39721965303209294726128327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52962620404279059634837769 39721965303209294726128327)
    ·
      refine ⟨59582947954813942089192491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39721965303209294726128327 59582947954813942089192491)
      ·
        refine ⟨89374421932220913133788737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59582947954813942089192491 89374421932220913133788737)
        ·
          refine ⟨67030816449165684850341553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89374421932220913133788737 67030816449165684850341553)
          ·
            refine ⟨50273112336874263637756165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67030816449165684850341553 50273112336874263637756165)
            ·
              refine ⟨9426208563163924432079281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50273112336874263637756165 9426208563163924432079281)
              ·
                refine ⟨7069656422372943324059461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9426208563163924432079281 7069656422372943324059461)
                ·
                  refine ⟨1325560579194926873261149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7069656422372943324059461 1325560579194926873261149)
                  ·
                    refine ⟨497085217198097577472931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1325560579194926873261149 497085217198097577472931)
                    ·
                      rfl

theorem cell22_1452105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4, 3].length) (baseStart_1452105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1452105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1452105 prefixEnd_1452105 := by exact prefixLift 1452105
  have htrace : WordTrace (prefixWord ++ tailWord_1452105) baseStart_1452105 baseEnd_1452105 := by
    simpa [prefixWord, tailWord_1452105, baseEnd_1452105] using wordTrace_append hprefix tailTrace_1452105
  have hstable : (prefixWord ++ tailWord_1452105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452105).length < 2 ^ (prefixWord ++ tailWord_1452105).sum := by decide
  have hdescent : baseEnd_1452105 < baseStart_1452105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452190 : List Nat := [4, 3, 1, 1, 4, 1, 2, 1, 2, 3]
def baseStart_1452190 : Nat := 118140960795 + 1452190 * 2 ^ 59
def prefixEnd_1452190 : Nat := 4983230072969 + 3 ^ 40 * 1452190 * 2
def baseEnd_1452190 : Nat := 497114314435185689097671

theorem tailTrace_1452190 : CollatzResearch.WordTrace tailWord_1452190 prefixEnd_1452190 497114314435185689097671 := by
  unfold tailWord_1452190
  simp only [CollatzResearch.WordTrace]
  refine ⟨6620715076121389893960253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35310480405980746101121349 6620715076121389893960253)
  ·
    refine ⟨2482768153545521210235095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6620715076121389893960253 2482768153545521210235095)
    ·
      refine ⟨3724152230318281815352643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2482768153545521210235095 3724152230318281815352643)
      ·
        refine ⟨5586228345477422723028965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3724152230318281815352643 5586228345477422723028965)
        ·
          refine ⟨1047417814777016760567931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5586228345477422723028965 1047417814777016760567931)
          ·
            refine ⟨1571126722165525140851897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1047417814777016760567931 1571126722165525140851897)
            ·
              refine ⟨1178345041624143855638923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1571126722165525140851897 1178345041624143855638923)
              ·
                refine ⟨1767517562436215783458385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1178345041624143855638923 1767517562436215783458385)
                ·
                  refine ⟨1325638171827161837593789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1767517562436215783458385 1325638171827161837593789)
                  ·
                    refine ⟨497114314435185689097671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1325638171827161837593789 497114314435185689097671)
                    ·
                      rfl

theorem cell22_1452190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_1452190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1452190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1452190 prefixEnd_1452190 := by exact prefixLift 1452190
  have htrace : WordTrace (prefixWord ++ tailWord_1452190) baseStart_1452190 baseEnd_1452190 := by
    simpa [prefixWord, tailWord_1452190, baseEnd_1452190] using wordTrace_append hprefix tailTrace_1452190
  have hstable : (prefixWord ++ tailWord_1452190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452190).length < 2 ^ (prefixWord ++ tailWord_1452190).sum := by decide
  have hdescent : baseEnd_1452190 < baseStart_1452190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452255 : List Nat := [1, 1, 2, 3, 2, 1, 1, 4, 1, 6]
def baseStart_1452255 : Nat := 118140960795 + 1452255 * 2 ^ 59
def prefixEnd_1452255 : Nat := 4983230072969 + 3 ^ 40 * 1452255 * 2
def baseEnd_1452255 : Nat := 497136565263547186222471

theorem tailTrace_1452255 : CollatzResearch.WordTrace tailWord_1452255 prefixEnd_1452255 497136565263547186222471 := by
  unfold tailWord_1452255
  simp only [CollatzResearch.WordTrace]
  refine ⟨52968091353735635252798219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35312060902490423501865479 52968091353735635252798219)
  ·
    refine ⟨79452137030603452879197329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52968091353735635252798219 79452137030603452879197329)
    ·
      refine ⟨59589102772952589659397997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79452137030603452879197329 59589102772952589659397997)
      ·
        refine ⟨22345913539857221122274249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59589102772952589659397997 22345913539857221122274249)
        ·
          refine ⟨16759435154892915841705687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22345913539857221122274249 16759435154892915841705687)
          ·
            refine ⟨25139152732339373762558531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16759435154892915841705687 25139152732339373762558531)
            ·
              refine ⟨37708729098509060643837797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25139152732339373762558531 37708729098509060643837797)
              ·
                refine ⟨7070386705970448870719587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37708729098509060643837797 7070386705970448870719587)
                ·
                  refine ⟨10605580058955673306079381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7070386705970448870719587 10605580058955673306079381)
                  ·
                    refine ⟨497136565263547186222471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10605580058955673306079381 497136565263547186222471)
                    ·
                      rfl

theorem cell22_1452255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 6].length) (baseStart_1452255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1452255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1452255 prefixEnd_1452255 := by exact prefixLift 1452255
  have htrace : WordTrace (prefixWord ++ tailWord_1452255) baseStart_1452255 baseEnd_1452255 := by
    simpa [prefixWord, tailWord_1452255, baseEnd_1452255] using wordTrace_append hprefix tailTrace_1452255
  have hstable : (prefixWord ++ tailWord_1452255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452255).length < 2 ^ (prefixWord ++ tailWord_1452255).sum := by decide
  have hdescent : baseEnd_1452255 < baseStart_1452255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452257 : List Nat := [1, 2, 3, 1, 3, 1, 4, 1, 1, 5]
def baseStart_1452257 : Nat := 118140960795 + 1452257 * 2 ^ 59
def prefixEnd_1452257 : Nat := 4983230072969 + 3 ^ 40 * 1452257 * 2
def baseEnd_1452257 : Nat := 497137249904419847672465

theorem tailTrace_1452257 : CollatzResearch.WordTrace tailWord_1452257 prefixEnd_1452257 497137249904419847672465 := by
  unfold tailWord_1452257
  simp only [CollatzResearch.WordTrace]
  refine ⟨52968164299728389594371025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35312109533152259729580683 52968164299728389594371025)
  ·
    refine ⟨39726123224796292195778269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52968164299728389594371025 39726123224796292195778269)
    ·
      refine ⟨14897296209298609573416851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39726123224796292195778269 14897296209298609573416851)
      ·
        refine ⟨22345944313947914360125277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14897296209298609573416851 22345944313947914360125277)
        ·
          refine ⟨8379729117730467885046979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22345944313947914360125277 8379729117730467885046979)
          ·
            refine ⟨12569593676595701827570469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8379729117730467885046979 12569593676595701827570469)
            ·
              refine ⟨2356798814361694092669463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12569593676595701827570469 2356798814361694092669463)
              ·
                refine ⟨3535198221542541139004195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2356798814361694092669463 3535198221542541139004195)
                ·
                  refine ⟨5302797332313811708506293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3535198221542541139004195 5302797332313811708506293)
                  ·
                    refine ⟨497137249904419847672465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5302797332313811708506293 497137249904419847672465)
                    ·
                      rfl

theorem cell22_1452257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_1452257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1452257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1452257 prefixEnd_1452257 := by exact prefixLift 1452257
  have htrace : WordTrace (prefixWord ++ tailWord_1452257) baseStart_1452257 baseEnd_1452257 := by
    simpa [prefixWord, tailWord_1452257, baseEnd_1452257] using wordTrace_append hprefix tailTrace_1452257
  have hstable : (prefixWord ++ tailWord_1452257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452257).length < 2 ^ (prefixWord ++ tailWord_1452257).sum := by decide
  have hdescent : baseEnd_1452257 < baseStart_1452257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452259 : List Nat := [1, 1, 1, 8, 1, 1, 1, 2, 6]
def baseStart_1452259 : Nat := 118140960795 + 1452259 * 2 ^ 59
def prefixEnd_1452259 : Nat := 4983230072969 + 3 ^ 40 * 1452259 * 2
def baseEnd_1452259 : Nat := 165712644848430836374153

theorem tailTrace_1452259 : CollatzResearch.WordTrace tailWord_1452259 prefixEnd_1452259 165712644848430836374153 := by
  unfold tailWord_1452259
  simp only [CollatzResearch.WordTrace]
  refine ⟨52968237245721143935943831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35312158163814095957295887 52968237245721143935943831)
  ·
    refine ⟨79452355868581715903915747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52968237245721143935943831 79452355868581715903915747)
    ·
      refine ⟨119178533802872573855873621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79452355868581715903915747 119178533802872573855873621)
      ·
        refine ⟨1396623443002412974873519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 119178533802872573855873621 1396623443002412974873519)
        ·
          refine ⟨2094935164503619462310279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1396623443002412974873519 2094935164503619462310279)
          ·
            refine ⟨3142402746755429193465419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2094935164503619462310279 3142402746755429193465419)
            ·
              refine ⟨4713604120133143790198129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3142402746755429193465419 4713604120133143790198129)
              ·
                refine ⟨3535203090099857842648597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4713604120133143790198129 3535203090099857842648597)
                ·
                  refine ⟨165712644848430836374153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3535203090099857842648597 165712644848430836374153)
                  ·
                    rfl

theorem cell22_1452259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 6].length) (baseStart_1452259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1452259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1452259 prefixEnd_1452259 := by exact prefixLift 1452259
  have htrace : WordTrace (prefixWord ++ tailWord_1452259) baseStart_1452259 baseEnd_1452259 := by
    simpa [prefixWord, tailWord_1452259, baseEnd_1452259] using wordTrace_append hprefix tailTrace_1452259
  have hstable : (prefixWord ++ tailWord_1452259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452259).length < 2 ^ (prefixWord ++ tailWord_1452259).sum := by decide
  have hdescent : baseEnd_1452259 < baseStart_1452259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452285 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 1, 9]
def baseStart_1452285 : Nat := 118140960795 + 1452285 * 2 ^ 59
def prefixEnd_1452285 : Nat := 4983230072969 + 3 ^ 40 * 1452285 * 2
def baseEnd_1452285 : Nat := 497146834876637107972379

theorem tailTrace_1452285 : CollatzResearch.WordTrace tailWord_1452285 prefixEnd_1452285 497146834876637107972379 := by
  unfold tailWord_1452285
  simp only [CollatzResearch.WordTrace]
  refine ⟨52969185543626950376390309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35312790362417966917593539 52969185543626950376390309)
  ·
    refine ⟨9931722289430053195573183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52969185543626950376390309 9931722289430053195573183)
    ·
      refine ⟨14897583434145079793359775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9931722289430053195573183 14897583434145079793359775)
      ·
        refine ⟨22346375151217619690039663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14897583434145079793359775 22346375151217619690039663)
        ·
          refine ⟨33519562726826429535059495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22346375151217619690039663 33519562726826429535059495)
          ·
            refine ⟨50279344090239644302589243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33519562726826429535059495 50279344090239644302589243)
            ·
              refine ⟨75419016135359466453883865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50279344090239644302589243 75419016135359466453883865)
              ·
                refine ⟨56564262101519599840412899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75419016135359466453883865 56564262101519599840412899)
                ·
                  refine ⟨84846393152279399760619349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56564262101519599840412899 84846393152279399760619349)
                  ·
                    refine ⟨497146834876637107972379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 84846393152279399760619349 497146834876637107972379)
                    ·
                      rfl

theorem cell22_1452285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_1452285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1452285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1452285 prefixEnd_1452285 := by exact prefixLift 1452285
  have htrace : WordTrace (prefixWord ++ tailWord_1452285) baseStart_1452285 baseEnd_1452285 := by
    simpa [prefixWord, tailWord_1452285, baseEnd_1452285] using wordTrace_append hprefix tailTrace_1452285
  have hstable : (prefixWord ++ tailWord_1452285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452285).length < 2 ^ (prefixWord ++ tailWord_1452285).sum := by decide
  have hdescent : baseEnd_1452285 < baseStart_1452285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452319 : List Nat := [1, 1, 2, 4, 3, 1, 2, 2, 3, 3]
def baseStart_1452319 : Nat := 118140960795 + 1452319 * 2 ^ 59
def prefixEnd_1452319 : Nat := 4983230072969 + 3 ^ 40 * 1452319 * 2
def baseEnd_1452319 : Nat := 497158473771472352622275

theorem tailTrace_1452319 : CollatzResearch.WordTrace tailWord_1452319 prefixEnd_1452319 497158473771472352622275 := by
  unfold tailWord_1452319
  simp only [CollatzResearch.WordTrace]
  refine ⟨52970425625503774183128011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35313617083669182788752007 52970425625503774183128011)
  ·
    refine ⟨79455638438255661274692017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52970425625503774183128011 79455638438255661274692017)
    ·
      refine ⟨59591728828691745956019013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79455638438255661274692017 59591728828691745956019013)
      ·
        refine ⟨11173449155379702366753565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59591728828691745956019013 11173449155379702366753565)
        ·
          refine ⟨4190043433267388387532587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11173449155379702366753565 4190043433267388387532587)
          ·
            refine ⟨6285065149901082581298881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4190043433267388387532587 6285065149901082581298881)
            ·
              refine ⟨4713798862425811935974161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6285065149901082581298881 4713798862425811935974161)
              ·
                refine ⟨3535349146819358951980621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4713798862425811935974161 3535349146819358951980621)
                ·
                  refine ⟨1325755930057259606992733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3535349146819358951980621 1325755930057259606992733)
                  ·
                    refine ⟨497158473771472352622275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1325755930057259606992733 497158473771472352622275)
                    ·
                      rfl

theorem cell22_1452319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3, 3].length) (baseStart_1452319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1452319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1452319 prefixEnd_1452319 := by exact prefixLift 1452319
  have htrace : WordTrace (prefixWord ++ tailWord_1452319) baseStart_1452319 baseEnd_1452319 := by
    simpa [prefixWord, tailWord_1452319, baseEnd_1452319] using wordTrace_append hprefix tailTrace_1452319
  have hstable : (prefixWord ++ tailWord_1452319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452319).length < 2 ^ (prefixWord ++ tailWord_1452319).sum := by decide
  have hdescent : baseEnd_1452319 < baseStart_1452319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452327 : List Nat := [1, 1, 8, 1, 2, 1, 1, 3, 4]
def baseStart_1452327 : Nat := 118140960795 + 1452327 * 2 ^ 59
def prefixEnd_1452327 : Nat := 4983230072969 + 3 ^ 40 * 1452327 * 2
def baseEnd_1452327 : Nat := 165720404111654332807417

theorem tailTrace_1452327 : CollatzResearch.WordTrace tailWord_1452327 prefixEnd_1452327 165720404111654332807417 := by
  unfold tailWord_1452327
  simp only [CollatzResearch.WordTrace]
  refine ⟨52970717409474791549419235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35313811606316527699612823 52970717409474791549419235)
  ·
    refine ⟨79456076114212187324128853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52970717409474791549419235 79456076114212187324128853)
    ·
      refine ⟨931125891963424070204635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 79456076114212187324128853 931125891963424070204635)
      ·
        refine ⟨1396688837945136105306953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 931125891963424070204635 1396688837945136105306953)
        ·
          refine ⟨1047516628458852078980215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1396688837945136105306953 1047516628458852078980215)
          ·
            refine ⟨1571274942688278118470323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1047516628458852078980215 1571274942688278118470323)
            ·
              refine ⟨2356912414032417177705485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1571274942688278118470323 2356912414032417177705485)
              ·
                refine ⟨883842155262156441639557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2356912414032417177705485 883842155262156441639557)
                ·
                  refine ⟨165720404111654332807417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 883842155262156441639557 165720404111654332807417)
                  ·
                    rfl

theorem cell22_1452327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 3, 4].length) (baseStart_1452327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1452327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1452327 prefixEnd_1452327 := by exact prefixLift 1452327
  have htrace : WordTrace (prefixWord ++ tailWord_1452327) baseStart_1452327 baseEnd_1452327 := by
    simpa [prefixWord, tailWord_1452327, baseEnd_1452327] using wordTrace_append hprefix tailTrace_1452327
  have hstable : (prefixWord ++ tailWord_1452327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452327).length < 2 ^ (prefixWord ++ tailWord_1452327).sum := by decide
  have hdescent : baseEnd_1452327 < baseStart_1452327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452353 : List Nat := [1, 2, 5, 2, 2, 2, 1, 1, 3, 3]
def baseStart_1452353 : Nat := 118140960795 + 1452353 * 2 ^ 59
def prefixEnd_1452353 : Nat := 4983230072969 + 3 ^ 40 * 1452353 * 2
def baseEnd_1452353 : Nat := 497170112666307597272171

theorem tailTrace_1452353 : CollatzResearch.WordTrace tailWord_1452353 prefixEnd_1452353 497170112666307597272171 := by
  unfold tailWord_1452353
  simp only [CollatzResearch.WordTrace]
  refine ⟨52971665707380597989865713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35314443804920398659910475 52971665707380597989865713)
  ·
    refine ⟨39728749280535448492399285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52971665707380597989865713 39728749280535448492399285)
    ·
      refine ⟨3724570245050198296162433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39728749280535448492399285 3724570245050198296162433)
      ·
        refine ⟨2793427683787648722121825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3724570245050198296162433 2793427683787648722121825)
        ·
          refine ⟨2095070762840736541591369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2793427683787648722121825 2095070762840736541591369)
          ·
            refine ⟨1571303072130552406193527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2095070762840736541591369 1571303072130552406193527)
            ·
              refine ⟨2356954608195828609290291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1571303072130552406193527 2356954608195828609290291)
              ·
                refine ⟨3535431912293742913935437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2356954608195828609290291 3535431912293742913935437)
                ·
                  refine ⟨1325786967110153592725789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3535431912293742913935437 1325786967110153592725789)
                  ·
                    refine ⟨497170112666307597272171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1325786967110153592725789 497170112666307597272171)
                    ·
                      rfl

theorem cell22_1452353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_1452353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1452353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1452353 prefixEnd_1452353 := by exact prefixLift 1452353
  have htrace : WordTrace (prefixWord ++ tailWord_1452353) baseStart_1452353 baseEnd_1452353 := by
    simpa [prefixWord, tailWord_1452353, baseEnd_1452353] using wordTrace_append hprefix tailTrace_1452353
  have hstable : (prefixWord ++ tailWord_1452353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452353).length < 2 ^ (prefixWord ++ tailWord_1452353).sum := by decide
  have hdescent : baseEnd_1452353 < baseStart_1452353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452407 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 4, 4]
def baseStart_1452407 : Nat := 118140960795 + 1452407 * 2 ^ 59
def prefixEnd_1452407 : Nat := 4983230072969 + 3 ^ 40 * 1452407 * 2
def baseEnd_1452407 : Nat := 497188597969869456422005

theorem tailTrace_1452407 : CollatzResearch.WordTrace tailWord_1452407 prefixEnd_1452407 497188597969869456422005 := by
  unfold tailWord_1452407
  simp only [CollatzResearch.WordTrace]
  refine ⟨52973635249184965212331475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35315756832789976808220983 52973635249184965212331475)
  ·
    refine ⟨79460452873777447818497213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52973635249184965212331475 79460452873777447818497213)
    ·
      refine ⟨29797669827666542931936455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79460452873777447818497213 29797669827666542931936455)
      ·
        refine ⟨44696504741499814397904683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29797669827666542931936455 44696504741499814397904683)
        ·
          refine ⟨67044757112249721596857025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44696504741499814397904683 67044757112249721596857025)
          ·
            refine ⟨50283567834187291197642769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67044757112249721596857025 50283567834187291197642769)
            ·
              refine ⟨37712675875640468398232077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50283567834187291197642769 37712675875640468398232077)
              ·
                refine ⟨14142253453365175649337029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37712675875640468398232077 14142253453365175649337029)
                ·
                  refine ⟨2651672522505970434250693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14142253453365175649337029 2651672522505970434250693)
                  ·
                    refine ⟨497188597969869456422005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2651672522505970434250693 497188597969869456422005)
                    ·
                      rfl

theorem cell22_1452407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_1452407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1452407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1452407 prefixEnd_1452407 := by exact prefixLift 1452407
  have htrace : WordTrace (prefixWord ++ tailWord_1452407) baseStart_1452407 baseEnd_1452407 := by
    simpa [prefixWord, tailWord_1452407, baseEnd_1452407] using wordTrace_append hprefix tailTrace_1452407
  have hstable : (prefixWord ++ tailWord_1452407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452407).length < 2 ^ (prefixWord ++ tailWord_1452407).sum := by decide
  have hdescent : baseEnd_1452407 < baseStart_1452407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452411 : List Nat := [1, 1, 1, 1, 1, 7, 4, 2, 4]
def baseStart_1452411 : Nat := 118140960795 + 1452411 * 2 ^ 59
def prefixEnd_1452411 : Nat := 4983230072969 + 3 ^ 40 * 1452411 * 2
def baseEnd_1452411 : Nat := 165729989083871593107331

theorem tailTrace_1452411 : CollatzResearch.WordTrace tailWord_1452411 prefixEnd_1452411 165729989083871593107331 := by
  unfold tailWord_1452411
  simp only [CollatzResearch.WordTrace]
  refine ⟨52973781141170473895477087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35315854094113649263651391 52973781141170473895477087)
  ·
    refine ⟨79460671711755710843215631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52973781141170473895477087 79460671711755710843215631)
    ·
      refine ⟨119191007567633566264823447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79460671711755710843215631 119191007567633566264823447)
      ·
        refine ⟨178786511351450349397235171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119191007567633566264823447 178786511351450349397235171)
        ·
          refine ⟨268179767027175524095852757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178786511351450349397235171 268179767027175524095852757)
          ·
            refine ⟨6285463289699426345996549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 268179767027175524095852757 6285463289699426345996549)
            ·
              refine ⟨1178524366818642439874353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6285463289699426345996549 1178524366818642439874353)
              ·
                refine ⟨883893275113981829905765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1178524366818642439874353 883893275113981829905765)
                ·
                  refine ⟨165729989083871593107331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 883893275113981829905765 165729989083871593107331)
                  ·
                    rfl

theorem cell22_1452411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2, 4].length) (baseStart_1452411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1452411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1452411 prefixEnd_1452411 := by exact prefixLift 1452411
  have htrace : WordTrace (prefixWord ++ tailWord_1452411) baseStart_1452411 baseEnd_1452411 := by
    simpa [prefixWord, tailWord_1452411, baseEnd_1452411] using wordTrace_append hprefix tailTrace_1452411
  have hstable : (prefixWord ++ tailWord_1452411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452411).length < 2 ^ (prefixWord ++ tailWord_1452411).sum := by decide
  have hdescent : baseEnd_1452411 < baseStart_1452411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452471 : List Nat := [1, 1, 3, 1, 3, 4, 2, 1, 3, 3]
def baseStart_1452471 : Nat := 118140960795 + 1452471 * 2 ^ 59
def prefixEnd_1452471 : Nat := 4983230072969 + 3 ^ 40 * 1452471 * 2
def baseEnd_1452471 : Nat := 497210506477794622821809

theorem tailTrace_1452471 : CollatzResearch.WordTrace tailWord_1452471 prefixEnd_1452471 497210506477794622821809 := by
  unfold tailWord_1452471
  simp only [CollatzResearch.WordTrace]
  refine ⟨52975969520953104142661267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35317313013968736095107511 52975969520953104142661267)
  ·
    refine ⟨79463954281429656213991901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52975969520953104142661267 79463954281429656213991901)
    ·
      refine ⟨29798982855536121080246963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79463954281429656213991901 29798982855536121080246963)
      ·
        refine ⟨44698474283304181620370445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29798982855536121080246963 44698474283304181620370445)
        ·
          refine ⟨16761927856239068107638917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44698474283304181620370445 16761927856239068107638917)
          ·
            refine ⟨3142861473044825270182297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16761927856239068107638917 3142861473044825270182297)
            ·
              refine ⟨2357146104783618952636723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3142861473044825270182297 2357146104783618952636723)
              ·
                refine ⟨3535719157175428428955085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2357146104783618952636723 3535719157175428428955085)
                ·
                  refine ⟨1325894683940785660858157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3535719157175428428955085 1325894683940785660858157)
                  ·
                    refine ⟨497210506477794622821809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1325894683940785660858157 497210506477794622821809)
                    ·
                      rfl

theorem cell22_1452471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3, 3].length) (baseStart_1452471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1452471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1452471 prefixEnd_1452471 := by exact prefixLift 1452471
  have htrace : WordTrace (prefixWord ++ tailWord_1452471) baseStart_1452471 baseEnd_1452471 := by
    simpa [prefixWord, tailWord_1452471, baseEnd_1452471] using wordTrace_append hprefix tailTrace_1452471
  have hstable : (prefixWord ++ tailWord_1452471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452471).length < 2 ^ (prefixWord ++ tailWord_1452471).sum := by decide
  have hdescent : baseEnd_1452471 < baseStart_1452471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452497 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 2, 8]
def baseStart_1452497 : Nat := 118140960795 + 1452497 * 2 ^ 59
def prefixEnd_1452497 : Nat := 4983230072969 + 3 ^ 40 * 1452497 * 2
def baseEnd_1452497 : Nat := 497219406809139221671729

theorem tailTrace_1452497 : CollatzResearch.WordTrace tailWord_1452497 prefixEnd_1452497 497219406809139221671729 := by
  unfold tailWord_1452497
  simp only [CollatzResearch.WordTrace]
  refine ⟨52976917818858910583107745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35317945212572607055405163 52976917818858910583107745)
  ·
    refine ⟨39732688364144182937330809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52976917818858910583107745 39732688364144182937330809)
    ·
      refine ⟨29799516273108137202998107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39732688364144182937330809 29799516273108137202998107)
      ·
        refine ⟨44699274409662205804497161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29799516273108137202998107 44699274409662205804497161)
        ·
          refine ⟨33524455807246654353372871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44699274409662205804497161 33524455807246654353372871)
          ·
            refine ⟨50286683710869981530059307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33524455807246654353372871 50286683710869981530059307)
            ·
              refine ⟨75430025566304972295088961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50286683710869981530059307 75430025566304972295088961)
              ·
                refine ⟨56572519174728729221316721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75430025566304972295088961 56572519174728729221316721)
                ·
                  refine ⟨42429389381046546915987541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56572519174728729221316721 42429389381046546915987541)
                  ·
                    refine ⟨497219406809139221671729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42429389381046546915987541 497219406809139221671729)
                    ·
                      rfl

theorem cell22_1452497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_1452497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1452497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1452497 prefixEnd_1452497 := by exact prefixLift 1452497
  have htrace : WordTrace (prefixWord ++ tailWord_1452497) baseStart_1452497 baseEnd_1452497 := by
    simpa [prefixWord, tailWord_1452497, baseEnd_1452497] using wordTrace_append hprefix tailTrace_1452497
  have hstable : (prefixWord ++ tailWord_1452497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452497).length < 2 ^ (prefixWord ++ tailWord_1452497).sum := by decide
  have hdescent : baseEnd_1452497 < baseStart_1452497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452548 : List Nat := [2, 3, 2, 3, 1, 1, 3, 2, 1, 4]
def baseStart_1452548 : Nat := 118140960795 + 1452548 * 2 ^ 59
def prefixEnd_1452548 : Nat := 4983230072969 + 3 ^ 40 * 1452548 * 2
def baseEnd_1452548 : Nat := 497236865151392088646573

theorem tailTrace_1452548 : CollatzResearch.WordTrace tailWord_1452548 prefixEnd_1452548 497236865151392088646573 := by
  unfold tailWord_1452548
  simp only [CollatzResearch.WordTrace]
  refine ⟨26489388970837073146607149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35319185294449430862142865 26489388970837073146607149)
  ·
    refine ⟨9933520864063902429977681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26489388970837073146607149 9933520864063902429977681)
    ·
      refine ⟨7450140648047926822483261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9933520864063902429977681 7450140648047926822483261)
      ·
        refine ⟨2793802743017972558431223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7450140648047926822483261 2793802743017972558431223)
        ·
          refine ⟨4190704114526958837646835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2793802743017972558431223 4190704114526958837646835)
          ·
            refine ⟨6286056171790438256470253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4190704114526958837646835 6286056171790438256470253)
            ·
              refine ⟨2357271064421414346176345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6286056171790438256470253 2357271064421414346176345)
              ·
                refine ⟨1767953298316060759632259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2357271064421414346176345 1767953298316060759632259)
                ·
                  refine ⟨2651929947474091139448389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1767953298316060759632259 2651929947474091139448389)
                  ·
                    refine ⟨497236865151392088646573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2651929947474091139448389 497236865151392088646573)
                    ·
                      rfl

theorem cell22_1452548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_1452548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1452548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1452548 prefixEnd_1452548 := by exact prefixLift 1452548
  have htrace : WordTrace (prefixWord ++ tailWord_1452548) baseStart_1452548 baseEnd_1452548 := by
    simpa [prefixWord, tailWord_1452548, baseEnd_1452548] using wordTrace_append hprefix tailTrace_1452548
  have hstable : (prefixWord ++ tailWord_1452548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452548).length < 2 ^ (prefixWord ++ tailWord_1452548).sum := by decide
  have hdescent : baseEnd_1452548 < baseStart_1452548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452559 : List Nat := [1, 1, 2, 1, 1, 1, 2, 7, 2, 4]
def baseStart_1452559 : Nat := 118140960795 + 1452559 * 2 ^ 59
def prefixEnd_1452559 : Nat := 4983230072969 + 3 ^ 40 * 1452559 * 2
def baseEnd_1452559 : Nat := 497240630676191726621539

theorem tailTrace_1452559 : CollatzResearch.WordTrace tailWord_1452559 prefixEnd_1452559 497240630676191726621539 := by
  unfold tailWord_1452559
  simp only [CollatzResearch.WordTrace]
  refine ⟨52979179144634295171864731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35319452763089530114576487 52979179144634295171864731)
  ·
    refine ⟨79468768716951442757797097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52979179144634295171864731 79468768716951442757797097)
    ·
      refine ⟨59601576537713582068347823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79468768716951442757797097 59601576537713582068347823)
      ·
        refine ⟨89402364806570373102521735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59601576537713582068347823 89402364806570373102521735)
        ·
          refine ⟨134103547209855559653782603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89402364806570373102521735 134103547209855559653782603)
          ·
            refine ⟨201155320814783339480673905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134103547209855559653782603 201155320814783339480673905)
            ·
              refine ⟨150866490611087504610505429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201155320814783339480673905 150866490611087504610505429)
              ·
                refine ⟨3535933373697363389308721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 150866490611087504610505429 3535933373697363389308721)
                ·
                  refine ⟨2651950030273022541981541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3535933373697363389308721 2651950030273022541981541)
                  ·
                    refine ⟨497240630676191726621539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2651950030273022541981541 497240630676191726621539)
                    ·
                      rfl

theorem cell22_1452559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 4].length) (baseStart_1452559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1452559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1452559 prefixEnd_1452559 := by exact prefixLift 1452559
  have htrace : WordTrace (prefixWord ++ tailWord_1452559) baseStart_1452559 baseEnd_1452559 := by
    simpa [prefixWord, tailWord_1452559, baseEnd_1452559] using wordTrace_append hprefix tailTrace_1452559
  have hstable : (prefixWord ++ tailWord_1452559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452559).length < 2 ^ (prefixWord ++ tailWord_1452559).sum := by decide
  have hdescent : baseEnd_1452559 < baseStart_1452559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452580 : List Nat := [2, 3, 1, 5, 1, 1, 1, 4, 4]
def baseStart_1452580 : Nat := 118140960795 + 1452580 * 2 ^ 59
def prefixEnd_1452580 : Nat := 4983230072969 + 3 ^ 40 * 1452580 * 2
def baseEnd_1452580 : Nat := 165749273135118223948825

theorem tailTrace_1452580 : CollatzResearch.WordTrace tailWord_1452580 prefixEnd_1452580 165749273135118223948825 := by
  unfold tailWord_1452580
  simp only [CollatzResearch.WordTrace]
  refine ⟨26489972538779107879189597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35319963385038810505586129 26489972538779107879189597)
  ·
    refine ⟨9933739702042165454696099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26489972538779107879189597 9933739702042165454696099)
    ·
      refine ⟨14900609553063248182044149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9933739702042165454696099 14900609553063248182044149)
      ·
        refine ⟨1396932145599679517066639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14900609553063248182044149 1396932145599679517066639)
        ·
          refine ⟨2095398218399519275599959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1396932145599679517066639 2095398218399519275599959)
          ·
            refine ⟨3143097327599278913399939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2095398218399519275599959 3143097327599278913399939)
            ·
              refine ⟨4714645991398918370099909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3143097327599278913399939 4714645991398918370099909)
              ·
                refine ⟨883996123387297194393733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4714645991398918370099909 883996123387297194393733)
                ·
                  refine ⟨165749273135118223948825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 883996123387297194393733 165749273135118223948825)
                  ·
                    rfl

theorem cell22_1452580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_1452580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1452580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1452580 prefixEnd_1452580 := by exact prefixLift 1452580
  have htrace : WordTrace (prefixWord ++ tailWord_1452580) baseStart_1452580 baseEnd_1452580 := by
    simpa [prefixWord, tailWord_1452580, baseEnd_1452580] using wordTrace_append hprefix tailTrace_1452580
  have hstable : (prefixWord ++ tailWord_1452580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452580).length < 2 ^ (prefixWord ++ tailWord_1452580).sum := by decide
  have hdescent : baseEnd_1452580 < baseStart_1452580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452623 : List Nat := [1, 1, 2, 1, 1, 2, 5, 5, 1, 3]
def baseStart_1452623 : Nat := 118140960795 + 1452623 * 2 ^ 59
def prefixEnd_1452623 : Nat := 4983230072969 + 3 ^ 40 * 1452623 * 2
def baseEnd_1452623 : Nat := 497262539184116893021343

theorem tailTrace_1452623 : CollatzResearch.WordTrace tailWord_1452623 prefixEnd_1452623 497262539184116893021343 := by
  unfold tailWord_1452623
  simp only [CollatzResearch.WordTrace]
  refine ⟨52981513416402434102194523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35321008944268289401463015 52981513416402434102194523)
  ·
    refine ⟨79472270124603651153291785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52981513416402434102194523 79472270124603651153291785)
    ·
      refine ⟨59604202593452738364968839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79472270124603651153291785 59604202593452738364968839)
      ·
        refine ⟨89406303890179107547453259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59604202593452738364968839 89406303890179107547453259)
        ·
          refine ⟨134109455835268661321179889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89406303890179107547453259 134109455835268661321179889)
          ·
            refine ⟨100582091876451495990884917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134109455835268661321179889 100582091876451495990884917)
            ·
              refine ⟨9429571113417327749145461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100582091876451495990884917 9429571113417327749145461)
              ·
                refine ⟨884022291882874476482387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9429571113417327749145461 884022291882874476482387)
                ·
                  refine ⟨1326033437824311714723581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 884022291882874476482387 1326033437824311714723581)
                  ·
                    refine ⟨497262539184116893021343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1326033437824311714723581 497262539184116893021343)
                    ·
                      rfl

theorem cell22_1452623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 1, 3].length) (baseStart_1452623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1452623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1452623 prefixEnd_1452623 := by exact prefixLift 1452623
  have htrace : WordTrace (prefixWord ++ tailWord_1452623) baseStart_1452623 baseEnd_1452623 := by
    simpa [prefixWord, tailWord_1452623, baseEnd_1452623] using wordTrace_append hprefix tailTrace_1452623
  have hstable : (prefixWord ++ tailWord_1452623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452623).length < 2 ^ (prefixWord ++ tailWord_1452623).sum := by decide
  have hdescent : baseEnd_1452623 < baseStart_1452623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452863 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 4, 4]
def baseStart_1452863 : Nat := 118140960795 + 1452863 * 2 ^ 59
def prefixEnd_1452863 : Nat := 4983230072969 + 3 ^ 40 * 1452863 * 2
def baseEnd_1452863 : Nat := 497344696088836267020607

theorem tailTrace_1452863 : CollatzResearch.WordTrace tailWord_1452863 prefixEnd_1452863 497344696088836267020607 := by
  unfold tailWord_1452863
  simp only [CollatzResearch.WordTrace]
  refine ⟨52990266935532955090931243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35326844623688636727287495 52990266935532955090931243)
  ·
    refine ⟨79485400403299432636396865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52990266935532955090931243 79485400403299432636396865)
    ·
      refine ⟨59614050302474574477297649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79485400403299432636396865 59614050302474574477297649)
      ·
        refine ⟨44710537726855930857973237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59614050302474574477297649 44710537726855930857973237)
        ·
          refine ⟨4191612911892743517934991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44710537726855930857973237 4191612911892743517934991)
          ·
            refine ⟨6287419367839115276902487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4191612911892743517934991 6287419367839115276902487)
            ·
              refine ⟨9431129051758672915353731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6287419367839115276902487 9431129051758672915353731)
              ·
                refine ⟨14146693577638009373030597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9431129051758672915353731 14146693577638009373030597)
                ·
                  refine ⟨2652505045807126757443237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14146693577638009373030597 2652505045807126757443237)
                  ·
                    refine ⟨497344696088836267020607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2652505045807126757443237 497344696088836267020607)
                    ·
                      rfl

theorem cell22_1452863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 4].length) (baseStart_1452863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1452863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1452863 prefixEnd_1452863 := by exact prefixLift 1452863
  have htrace : WordTrace (prefixWord ++ tailWord_1452863) baseStart_1452863 baseEnd_1452863 := by
    simpa [prefixWord, tailWord_1452863, baseEnd_1452863] using wordTrace_append hprefix tailTrace_1452863
  have hstable : (prefixWord ++ tailWord_1452863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452863).length < 2 ^ (prefixWord ++ tailWord_1452863).sum := by decide
  have hdescent : baseEnd_1452863 < baseStart_1452863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452923 : List Nat := [1, 1, 1, 1, 1, 5, 3, 4, 5]
def baseStart_1452923 : Nat := 118140960795 + 1452923 * 2 ^ 59
def prefixEnd_1452923 : Nat := 4983230072969 + 3 ^ 40 * 1452923 * 2
def baseEnd_1452923 : Nat := 165788411771672036840141

theorem tailTrace_1452923 : CollatzResearch.WordTrace tailWord_1452923 prefixEnd_1452923 165788411771672036840141 := by
  unfold tailWord_1452923
  simp only [CollatzResearch.WordTrace]
  refine ⟨52992455315315585338115423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35328303543543723558743615 52992455315315585338115423)
  ·
    refine ⟨79488682972973378007173135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52992455315315585338115423 79488682972973378007173135)
    ·
      refine ⟨119233024459460067010759703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79488682972973378007173135 119233024459460067010759703)
      ·
        refine ⟨178849536689190100516139555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119233024459460067010759703 178849536689190100516139555)
        ·
          refine ⟨268274305033785150774209333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178849536689190100516139555 268274305033785150774209333)
          ·
            refine ⟨25150716096917357885082125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 268274305033785150774209333 25150716096917357885082125)
            ·
              refine ⟨9431518536344009206905797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25150716096917357885082125 9431518536344009206905797)
              ·
                refine ⟨1768409725564501726294837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9431518536344009206905797 1768409725564501726294837)
                ·
                  refine ⟨165788411771672036840141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1768409725564501726294837 165788411771672036840141)
                  ·
                    rfl

theorem cell22_1452923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 5].length) (baseStart_1452923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1452923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1452923 prefixEnd_1452923 := by exact prefixLift 1452923
  have htrace : WordTrace (prefixWord ++ tailWord_1452923) baseStart_1452923 baseEnd_1452923 := by
    simpa [prefixWord, tailWord_1452923, baseEnd_1452923] using wordTrace_append hprefix tailTrace_1452923
  have hstable : (prefixWord ++ tailWord_1452923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452923).length < 2 ^ (prefixWord ++ tailWord_1452923).sum := by decide
  have hdescent : baseEnd_1452923 < baseStart_1452923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452983 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 3, 5]
def baseStart_1452983 : Nat := 118140960795 + 1452983 * 2 ^ 59
def prefixEnd_1452983 : Nat := 4983230072969 + 3 ^ 40 * 1452983 * 2
def baseEnd_1452983 : Nat := 497385774541195954020239

theorem tailTrace_1452983 : CollatzResearch.WordTrace tailWord_1452983 prefixEnd_1452983 497385774541195954020239 := by
  unfold tailWord_1452983
  simp only [CollatzResearch.WordTrace]
  refine ⟨52994643695098215585299603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35329762463398810390199735 52994643695098215585299603)
  ·
    refine ⟨79491965542647323377949405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52994643695098215585299603 79491965542647323377949405)
    ·
      refine ⟨29809487078492746266731027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79491965542647323377949405 29809487078492746266731027)
      ·
        refine ⟨44714230617739119400096541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29809487078492746266731027 44714230617739119400096541)
        ·
          refine ⟨16767836481652169775036203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44714230617739119400096541 16767836481652169775036203)
          ·
            refine ⟨25151754722478254662554305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16767836481652169775036203 25151754722478254662554305)
            ·
              refine ⟨18863816041858690996915729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25151754722478254662554305 18863816041858690996915729)
              ·
                refine ⟨14147862031394018247686797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18863816041858690996915729 14147862031394018247686797)
                ·
                  refine ⟨5305448261772756842882549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14147862031394018247686797 5305448261772756842882549)
                  ·
                    refine ⟨497385774541195954020239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5305448261772756842882549 497385774541195954020239)
                    ·
                      rfl

theorem cell22_1452983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_1452983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1452983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1452983 prefixEnd_1452983 := by exact prefixLift 1452983
  have htrace : WordTrace (prefixWord ++ tailWord_1452983) baseStart_1452983 baseEnd_1452983 := by
    simpa [prefixWord, tailWord_1452983, baseEnd_1452983] using wordTrace_append hprefix tailTrace_1452983
  have hstable : (prefixWord ++ tailWord_1452983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452983).length < 2 ^ (prefixWord ++ tailWord_1452983).sum := by decide
  have hdescent : baseEnd_1452983 < baseStart_1452983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452985 : List Nat := [1, 2, 1, 4, 2, 3, 2, 1, 6]
def baseStart_1452985 : Nat := 118140960795 + 1452985 * 2 ^ 59
def prefixEnd_1452985 : Nat := 4983230072969 + 3 ^ 40 * 1452985 * 2
def baseEnd_1452985 : Nat := 165795486394022871823411

theorem tailTrace_1452985 : CollatzResearch.WordTrace tailWord_1452985 prefixEnd_1452985 165795486394022871823411 := by
  unfold tailWord_1452985
  simp only [CollatzResearch.WordTrace]
  refine ⟨52994716641090969926872409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35329811094060646617914939 52994716641090969926872409)
  ·
    refine ⟨39746037480818227445154307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52994716641090969926872409 39746037480818227445154307)
    ·
      refine ⟨59619056221227341167731461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39746037480818227445154307 59619056221227341167731461)
      ·
        refine ⟨11178573041480126468949649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59619056221227341167731461 11178573041480126468949649)
        ·
          refine ⟨8383929781110094851712237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11178573041480126468949649 8383929781110094851712237)
          ·
            refine ⟨3143973667916285569392089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8383929781110094851712237 3143973667916285569392089)
            ·
              refine ⟨2357980250937214177044067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3143973667916285569392089 2357980250937214177044067)
              ·
                refine ⟨3536970376405821265566101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2357980250937214177044067 3536970376405821265566101)
                ·
                  refine ⟨165795486394022871823411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3536970376405821265566101 165795486394022871823411)
                  ·
                    rfl

theorem cell22_1452985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 6].length) (baseStart_1452985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1452985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1452985 prefixEnd_1452985 := by exact prefixLift 1452985
  have htrace : WordTrace (prefixWord ++ tailWord_1452985) baseStart_1452985 baseEnd_1452985 := by
    simpa [prefixWord, tailWord_1452985, baseEnd_1452985] using wordTrace_append hprefix tailTrace_1452985
  have hstable : (prefixWord ++ tailWord_1452985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452985).length < 2 ^ (prefixWord ++ tailWord_1452985).sum := by decide
  have hdescent : baseEnd_1452985 < baseStart_1452985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453092 : List Nat := [2, 3, 1, 4, 1, 1, 1, 4, 5]
def baseStart_1453092 : Nat := 118140960795 + 1453092 * 2 ^ 59
def prefixEnd_1453092 : Nat := 4983230072969 + 3 ^ 40 * 1453092 * 2
def baseEnd_1453092 : Nat := 165807695822918667681635

theorem tailTrace_1453092 : CollatzResearch.WordTrace tailWord_1453092 prefixEnd_1453092 165807695822918667681635 := by
  unfold tailWord_1453092
  simp only [CollatzResearch.WordTrace]
  refine ⟨26499309625851663600508765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35332412834468884800678353 26499309625851663600508765)
  ·
    refine ⟨9937241109694373850190787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26499309625851663600508765 9937241109694373850190787)
    ·
      refine ⟨14905861664541560775286181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9937241109694373850190787 14905861664541560775286181)
      ·
        refine ⟨2794849062101542645366159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14905861664541560775286181 2794849062101542645366159)
        ·
          refine ⟨4192273593152313968049239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2794849062101542645366159 4192273593152313968049239)
          ·
            refine ⟨6288410389728470952073859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4192273593152313968049239 6288410389728470952073859)
            ·
              refine ⟨9432615584592706428110789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6288410389728470952073859 9432615584592706428110789)
              ·
                refine ⟨1768615422111132455270773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9432615584592706428110789 1768615422111132455270773)
                ·
                  refine ⟨165807695822918667681635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1768615422111132455270773 165807695822918667681635)
                  ·
                    rfl

theorem cell22_1453092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_1453092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1453092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1453092 prefixEnd_1453092 := by exact prefixLift 1453092
  have htrace : WordTrace (prefixWord ++ tailWord_1453092) baseStart_1453092 baseEnd_1453092 := by
    simpa [prefixWord, tailWord_1453092, baseEnd_1453092] using wordTrace_append hprefix tailTrace_1453092
  have hstable : (prefixWord ++ tailWord_1453092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453092).length < 2 ^ (prefixWord ++ tailWord_1453092).sum := by decide
  have hdescent : baseEnd_1453092 < baseStart_1453092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453105 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 5, 4]
def baseStart_1453105 : Nat := 118140960795 + 1453105 * 2 ^ 59
def prefixEnd_1453105 : Nat := 4983230072969 + 3 ^ 40 * 1453105 * 2
def baseEnd_1453105 : Nat := 497427537634428302469865

theorem tailTrace_1453105 : CollatzResearch.WordTrace tailWord_1453105 prefixEnd_1453105 497427537634428302469865 := by
  unfold tailWord_1453105
  simp only [CollatzResearch.WordTrace]
  refine ⟨52999093400656230421240769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35332728933770820280827179 52999093400656230421240769)
  ·
    refine ⟨39749320050492172815930577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52999093400656230421240769 39749320050492172815930577)
    ·
      refine ⟨29811990037869129611947933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39749320050492172815930577 29811990037869129611947933)
      ·
        refine ⟨11179496264200923604480475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29811990037869129611947933 11179496264200923604480475)
        ·
          refine ⟨16769244396301385406720713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11179496264200923604480475 16769244396301385406720713)
          ·
            refine ⟨12576933297226039055040535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16769244396301385406720713 12576933297226039055040535)
            ·
              refine ⟨18865399945839058582560803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12576933297226039055040535 18865399945839058582560803)
              ·
                refine ⟨28298099918758587873841205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18865399945839058582560803 28298099918758587873841205)
                ·
                  refine ⟨2652946867383617613172613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28298099918758587873841205 2652946867383617613172613)
                  ·
                    refine ⟨497427537634428302469865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2652946867383617613172613 497427537634428302469865)
                    ·
                      rfl

theorem cell22_1453105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_1453105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1453105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1453105 prefixEnd_1453105 := by exact prefixLift 1453105
  have htrace : WordTrace (prefixWord ++ tailWord_1453105) baseStart_1453105 baseEnd_1453105 := by
    simpa [prefixWord, tailWord_1453105, baseEnd_1453105] using wordTrace_append hprefix tailTrace_1453105
  have hstable : (prefixWord ++ tailWord_1453105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453105).length < 2 ^ (prefixWord ++ tailWord_1453105).sum := by decide
  have hdescent : baseEnd_1453105 < baseStart_1453105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453120 : List Nat := [2, 1, 1, 2, 2, 3, 3, 2, 6]
def baseStart_1453120 : Nat := 118140960795 + 1453120 * 2 ^ 59
def prefixEnd_1453120 : Nat := 4983230072969 + 3 ^ 40 * 1453120 * 2
def baseEnd_1453120 : Nat := 165810890813657754448273

theorem tailTrace_1453120 : CollatzResearch.WordTrace tailWord_1453120 prefixEnd_1453120 165810890813657754448273 := by
  unfold tailWord_1453120
  simp only [CollatzResearch.WordTrace]
  refine ⟨26499820247800943991518407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35333093663734591988691209 26499820247800943991518407)
  ·
    refine ⟨39749730371701415987277611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26499820247800943991518407 39749730371701415987277611)
    ·
      refine ⟨59624595557552123980916417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39749730371701415987277611 59624595557552123980916417)
      ·
        refine ⟨44718446668164092985687313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59624595557552123980916417 44718446668164092985687313)
        ·
          refine ⟨33538835001123069739265485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44718446668164092985687313 33538835001123069739265485)
          ·
            refine ⟨12577063125421151152224557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33538835001123069739265485 12577063125421151152224557)
            ·
              refine ⟨4716398672032931682084209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12577063125421151152224557 4716398672032931682084209)
              ·
                refine ⟨3537299004024698761563157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4716398672032931682084209 3537299004024698761563157)
                ·
                  refine ⟨165810890813657754448273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3537299004024698761563157 165810890813657754448273)
                  ·
                    rfl

theorem cell22_1453120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 6].length) (baseStart_1453120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1453120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1453120 prefixEnd_1453120 := by exact prefixLift 1453120
  have htrace : WordTrace (prefixWord ++ tailWord_1453120) baseStart_1453120 baseEnd_1453120 := by
    simpa [prefixWord, tailWord_1453120, baseEnd_1453120] using wordTrace_append hprefix tailTrace_1453120
  have hstable : (prefixWord ++ tailWord_1453120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453120).length < 2 ^ (prefixWord ++ tailWord_1453120).sum := by decide
  have hdescent : baseEnd_1453120 < baseStart_1453120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453137 : List Nat := [1, 2, 2, 1, 3, 1, 3, 5, 4]
def baseStart_1453137 : Nat := 118140960795 + 1453137 * 2 ^ 59
def prefixEnd_1453137 : Nat := 4983230072969 + 3 ^ 40 * 1453137 * 2
def baseEnd_1453137 : Nat := 165812830629463628556589

theorem tailTrace_1453137 : CollatzResearch.WordTrace tailWord_1453137 prefixEnd_1453137 165812830629463628556589 := by
  unfold tailWord_1453137
  simp only [CollatzResearch.WordTrace]
  refine ⟨53000260536540299886405665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35333507024360199924270443 53000260536540299886405665)
  ·
    refine ⟨39750195402405224914804249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53000260536540299886405665 39750195402405224914804249)
    ·
      refine ⟨29812646551803918686103187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39750195402405224914804249 29812646551803918686103187)
      ·
        refine ⟨44718969827705878029154781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29812646551803918686103187 44718969827705878029154781)
        ·
          refine ⟨16769613685389704260933043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44718969827705878029154781 16769613685389704260933043)
          ·
            refine ⟨25154420528084556391399565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16769613685389704260933043 25154420528084556391399565)
            ·
              refine ⟨9432907698031708646774837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25154420528084556391399565 9432907698031708646774837)
              ·
                refine ⟨884335096690472685635141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9432907698031708646774837 884335096690472685635141)
                ·
                  refine ⟨165812830629463628556589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 884335096690472685635141 165812830629463628556589)
                  ·
                    rfl

theorem cell22_1453137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5, 4].length) (baseStart_1453137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1453137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1453137 prefixEnd_1453137 := by exact prefixLift 1453137
  have htrace : WordTrace (prefixWord ++ tailWord_1453137) baseStart_1453137 baseEnd_1453137 := by
    simpa [prefixWord, tailWord_1453137, baseEnd_1453137] using wordTrace_append hprefix tailTrace_1453137
  have hstable : (prefixWord ++ tailWord_1453137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453137).length < 2 ^ (prefixWord ++ tailWord_1453137).sum := by decide
  have hdescent : baseEnd_1453137 < baseStart_1453137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453152 : List Nat := [2, 1, 1, 3, 2, 2, 3, 1, 4, 3]
def baseStart_1453152 : Nat := 118140960795 + 1453152 * 2 ^ 59
def prefixEnd_1453152 : Nat := 4983230072969 + 3 ^ 40 * 1453152 * 2
def baseEnd_1453152 : Nat := 497443626694935846544721

theorem tailTrace_1453152 : CollatzResearch.WordTrace tailWord_1453152 prefixEnd_1453152 497443626694935846544721 := by
  unfold tailWord_1453152
  simp only [CollatzResearch.WordTrace]
  refine ⟨26500403815742978724100855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35333871754323971632134473 26500403815742978724100855)
  ·
    refine ⟨39750605723614468086151283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26500403815742978724100855 39750605723614468086151283)
    ·
      refine ⟨59625908585421702129226925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39750605723614468086151283 59625908585421702129226925)
      ·
        refine ⟨22359715719533138298460097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59625908585421702129226925 22359715719533138298460097)
        ·
          refine ⟨16769786789649853723845073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22359715719533138298460097 16769786789649853723845073)
          ·
            refine ⟨12577340092237390292883805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16769786789649853723845073 12577340092237390292883805)
            ·
              refine ⟨4716502534589021359831427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12577340092237390292883805 4716502534589021359831427)
              ·
                refine ⟨7074753801883532039747141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4716502534589021359831427 7074753801883532039747141)
                ·
                  refine ⟨1326516337853162257452589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7074753801883532039747141 1326516337853162257452589)
                  ·
                    refine ⟨497443626694935846544721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1326516337853162257452589 497443626694935846544721)
                    ·
                      rfl

theorem cell22_1453152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 4, 3].length) (baseStart_1453152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1453152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1453152 prefixEnd_1453152 := by exact prefixLift 1453152
  have htrace : WordTrace (prefixWord ++ tailWord_1453152) baseStart_1453152 baseEnd_1453152 := by
    simpa [prefixWord, tailWord_1453152, baseEnd_1453152] using wordTrace_append hprefix tailTrace_1453152
  have hstable : (prefixWord ++ tailWord_1453152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453152).length < 2 ^ (prefixWord ++ tailWord_1453152).sum := by decide
  have hdescent : baseEnd_1453152 < baseStart_1453152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453154 : List Nat := [3, 3, 2, 2, 1, 2, 2, 1, 6]
def baseStart_1453154 : Nat := 118140960795 + 1453154 * 2 ^ 59
def prefixEnd_1453154 : Nat := 4983230072969 + 3 ^ 40 * 1453154 * 2
def baseEnd_1453154 : Nat := 165814770445269502664905

theorem tailTrace_1453154 : CollatzResearch.WordTrace tailWord_1453154 prefixEnd_1453154 165814770445269502664905 := by
  unfold tailWord_1453154
  simp only [CollatzResearch.WordTrace]
  refine ⟨13250220144369677947443629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35333920384985807859849677 13250220144369677947443629)
  ·
    refine ⟨4968832554138629230291361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13250220144369677947443629 4968832554138629230291361)
    ·
      refine ⟨3726624415603971922718521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4968832554138629230291361 3726624415603971922718521)
      ·
        refine ⟨2794968311702978942038891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3726624415603971922718521 2794968311702978942038891)
        ·
          refine ⟨4192452467554468413058337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2794968311702978942038891 4192452467554468413058337)
          ·
            refine ⟨3144339350665851309793753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4192452467554468413058337 3144339350665851309793753)
            ·
              refine ⟨2358254512999388482345315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3144339350665851309793753 2358254512999388482345315)
              ·
                refine ⟨3537381769499082723517973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2358254512999388482345315 3537381769499082723517973)
                ·
                  refine ⟨165814770445269502664905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3537381769499082723517973 165814770445269502664905)
                  ·
                    rfl

theorem cell22_1453154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_1453154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1453154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1453154 prefixEnd_1453154 := by exact prefixLift 1453154
  have htrace : WordTrace (prefixWord ++ tailWord_1453154) baseStart_1453154 baseEnd_1453154 := by
    simpa [prefixWord, tailWord_1453154, baseEnd_1453154] using wordTrace_append hprefix tailTrace_1453154
  have hstable : (prefixWord ++ tailWord_1453154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453154).length < 2 ^ (prefixWord ++ tailWord_1453154).sum := by decide
  have hdescent : baseEnd_1453154 < baseStart_1453154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453180 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 2, 7]
def baseStart_1453180 : Nat := 118140960795 + 1453180 * 2 ^ 59
def prefixEnd_1453180 : Nat := 4983230072969 + 3 ^ 40 * 1453180 * 2
def baseEnd_1453180 : Nat := 497453211667153106844635

theorem tailTrace_1453180 : CollatzResearch.WordTrace tailWord_1453180 prefixEnd_1453180 497453211667153106844635 := by
  unfold tailWord_1453180
  simp only [CollatzResearch.WordTrace]
  refine ⟨26500914437692259115110497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35334552583589678820147329 26500914437692259115110497)
  ·
    refine ⟨19875685828269194336332873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26500914437692259115110497 19875685828269194336332873)
    ·
      refine ⟨14906764371201895752249655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19875685828269194336332873 14906764371201895752249655)
      ·
        refine ⟨22360146556802843628374483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14906764371201895752249655 22360146556802843628374483)
        ·
          refine ⟨33540219835204265442561725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22360146556802843628374483 33540219835204265442561725)
          ·
            refine ⟨12577582438201599540960647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33540219835204265442561725 12577582438201599540960647)
            ·
              refine ⟨18866373657302399311440971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12577582438201599540960647 18866373657302399311440971)
              ·
                refine ⟨28299560485953598967161457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18866373657302399311440971 28299560485953598967161457)
                ·
                  refine ⟨21224670364465199225371093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28299560485953598967161457 21224670364465199225371093)
                  ·
                    refine ⟨497453211667153106844635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21224670364465199225371093 497453211667153106844635)
                    ·
                      rfl

theorem cell22_1453180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_1453180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1453180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1453180 prefixEnd_1453180 := by exact prefixLift 1453180
  have htrace : WordTrace (prefixWord ++ tailWord_1453180) baseStart_1453180 baseEnd_1453180 := by
    simpa [prefixWord, tailWord_1453180, baseEnd_1453180] using wordTrace_append hprefix tailTrace_1453180
  have hstable : (prefixWord ++ tailWord_1453180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453180).length < 2 ^ (prefixWord ++ tailWord_1453180).sum := by decide
  have hdescent : baseEnd_1453180 < baseStart_1453180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453308 : List Nat := [2, 2, 2, 1, 5, 2, 2, 1, 1, 4]
def baseStart_1453308 : Nat := 118140960795 + 1453308 * 2 ^ 59
def prefixEnd_1453308 : Nat := 4983230072969 + 3 ^ 40 * 1453308 * 2
def baseEnd_1453308 : Nat := 497497028683003439644243

theorem tailTrace_1453308 : CollatzResearch.WordTrace tailWord_1453308 prefixEnd_1453308 497497028683003439644243 := by
  unfold tailWord_1453308
  simp only [CollatzResearch.WordTrace]
  refine ⟨26503248709460398045440289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35337664945947197393920385 26503248709460398045440289)
  ·
    refine ⟨19877436532095298534080217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26503248709460398045440289 19877436532095298534080217)
    ·
      refine ⟨14908077399071473900560163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19877436532095298534080217 14908077399071473900560163)
      ·
        refine ⟨22362116098607210850840245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14908077399071473900560163 22362116098607210850840245)
        ·
          refine ⟨2096448384244426017266273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22362116098607210850840245 2096448384244426017266273)
          ·
            refine ⟨1572336288183319512949705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2096448384244426017266273 1572336288183319512949705)
            ·
              refine ⟨1179252216137489634712279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1572336288183319512949705 1179252216137489634712279)
              ·
                refine ⟨1768878324206234452068419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1179252216137489634712279 1768878324206234452068419)
                ·
                  refine ⟨2653317486309351678102629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1768878324206234452068419 2653317486309351678102629)
                  ·
                    refine ⟨497497028683003439644243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2653317486309351678102629 497497028683003439644243)
                    ·
                      rfl

theorem cell22_1453308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_1453308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1453308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1453308 prefixEnd_1453308 := by exact prefixLift 1453308
  have htrace : WordTrace (prefixWord ++ tailWord_1453308) baseStart_1453308 baseEnd_1453308 := by
    simpa [prefixWord, tailWord_1453308, baseEnd_1453308] using wordTrace_append hprefix tailTrace_1453308
  have hstable : (prefixWord ++ tailWord_1453308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453308).length < 2 ^ (prefixWord ++ tailWord_1453308).sum := by decide
  have hdescent : baseEnd_1453308 < baseStart_1453308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453338 : List Nat := [3, 1, 1, 3, 3, 2, 3, 1, 2, 3]
def baseStart_1453338 : Nat := 118140960795 + 1453338 * 2 ^ 59
def prefixEnd_1453338 : Nat := 4983230072969 + 3 ^ 40 * 1453338 * 2
def baseEnd_1453338 : Nat := 497507298296093361394151

theorem tailTrace_1453338 : CollatzResearch.WordTrace tailWord_1453338 prefixEnd_1453338 497507298296093361394151 := by
  unfold tailWord_1453338
  simp only [CollatzResearch.WordTrace]
  refine ⟨13251897902203027803618167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35338394405874740809648445 13251897902203027803618167)
  ·
    refine ⟨19877846853304541705427251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13251897902203027803618167 19877846853304541705427251)
    ·
      refine ⟨29816770279956812558140877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19877846853304541705427251 29816770279956812558140877)
      ·
        refine ⟨11181288854983804709302829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29816770279956812558140877 11181288854983804709302829)
        ·
          refine ⟨4192983320618926765988561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11181288854983804709302829 4192983320618926765988561)
          ·
            refine ⟨3144737490464195074491421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4192983320618926765988561 3144737490464195074491421)
            ·
              refine ⟨1179276558924073152934283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3144737490464195074491421 1179276558924073152934283)
              ·
                refine ⟨1768914838386109729401425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1179276558924073152934283 1768914838386109729401425)
                ·
                  refine ⟨1326686128789582297051069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1768914838386109729401425 1326686128789582297051069)
                  ·
                    refine ⟨497507298296093361394151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1326686128789582297051069 497507298296093361394151)
                    ·
                      rfl

theorem cell22_1453338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 2, 3].length) (baseStart_1453338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1453338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1453338 prefixEnd_1453338 := by exact prefixLift 1453338
  have htrace : WordTrace (prefixWord ++ tailWord_1453338) baseStart_1453338 baseEnd_1453338 := by
    simpa [prefixWord, tailWord_1453338, baseEnd_1453338] using wordTrace_append hprefix tailTrace_1453338
  have hstable : (prefixWord ++ tailWord_1453338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453338).length < 2 ^ (prefixWord ++ tailWord_1453338).sum := by decide
  have hdescent : baseEnd_1453338 < baseStart_1453338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453389 : List Nat := [1, 6, 1, 3, 2, 1, 2, 1, 2, 3]
def baseStart_1453389 : Nat := 118140960795 + 1453389 * 2 ^ 59
def prefixEnd_1453389 : Nat := 4983230072969 + 3 ^ 40 * 1453389 * 2
def baseEnd_1453389 : Nat := 497524756638346228368995

theorem tailTrace_1453389 : CollatzResearch.WordTrace tailWord_1453389 prefixEnd_1453389 497524756638346228368995 := by
  unfold tailWord_1453389
  simp only [CollatzResearch.WordTrace]
  refine ⟨53009451731627346924579221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35339634487751564616386147 53009451731627346924579221)
  ·
    refine ⟨2484818049920031887089651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 53009451731627346924579221 2484818049920031887089651)
    ·
      refine ⟨3727227074880047830634477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2484818049920031887089651 3727227074880047830634477)
      ·
        refine ⟨1397710153080017936487929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3727227074880047830634477 1397710153080017936487929)
        ·
          refine ⟨1048282614810013452365947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1397710153080017936487929 1048282614810013452365947)
          ·
            refine ⟨1572423922215020178548921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1048282614810013452365947 1572423922215020178548921)
            ·
              refine ⟨1179317941661265133911691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1572423922215020178548921 1179317941661265133911691)
              ·
                refine ⟨1768976912491897700867537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1179317941661265133911691 1768976912491897700867537)
                ·
                  refine ⟨1326732684368923275650653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1768976912491897700867537 1326732684368923275650653)
                  ·
                    refine ⟨497524756638346228368995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1326732684368923275650653 497524756638346228368995)
                    ·
                      rfl

theorem cell22_1453389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_1453389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1453389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1453389 prefixEnd_1453389 := by exact prefixLift 1453389
  have htrace : WordTrace (prefixWord ++ tailWord_1453389) baseStart_1453389 baseEnd_1453389 := by
    simpa [prefixWord, tailWord_1453389, baseEnd_1453389] using wordTrace_append hprefix tailTrace_1453389
  have hstable : (prefixWord ++ tailWord_1453389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453389).length < 2 ^ (prefixWord ++ tailWord_1453389).sum := by decide
  have hdescent : baseEnd_1453389 < baseStart_1453389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453407 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 8]
def baseStart_1453407 : Nat := 118140960795 + 1453407 * 2 ^ 59
def prefixEnd_1453407 : Nat := 4983230072969 + 3 ^ 40 * 1453407 * 2
def baseEnd_1453407 : Nat := 165843639468733393806313

theorem tailTrace_1453407 : CollatzResearch.WordTrace tailWord_1453407 prefixEnd_1453407 165843639468733393806313 := by
  unfold tailWord_1453407
  simp only [CollatzResearch.WordTrace]
  refine ⟨53010108245562135998734475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35340072163708090665822983 53010108245562135998734475)
  ·
    refine ⟨79515162368343203998101713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53010108245562135998734475 79515162368343203998101713)
    ·
      refine ⟨59636371776257402998576285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79515162368343203998101713 59636371776257402998576285)
      ·
        refine ⟨22363639416096526124466107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59636371776257402998576285 22363639416096526124466107)
        ·
          refine ⟨33545459124144789186699161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22363639416096526124466107 33545459124144789186699161)
          ·
            refine ⟨25159094343108591890024371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33545459124144789186699161 25159094343108591890024371)
            ·
              refine ⟨37738641514662887835036557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25159094343108591890024371 37738641514662887835036557)
              ·
                refine ⟨14151990567998582938138709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37738641514662887835036557 14151990567998582938138709)
                ·
                  refine ⟨165843639468733393806313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14151990567998582938138709 165843639468733393806313)
                  ·
                    rfl

theorem cell22_1453407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 8].length) (baseStart_1453407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1453407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1453407 prefixEnd_1453407 := by exact prefixLift 1453407
  have htrace : WordTrace (prefixWord ++ tailWord_1453407) baseStart_1453407 baseEnd_1453407 := by
    simpa [prefixWord, tailWord_1453407, baseEnd_1453407] using wordTrace_append hprefix tailTrace_1453407
  have hstable : (prefixWord ++ tailWord_1453407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453407).length < 2 ^ (prefixWord ++ tailWord_1453407).sum := by decide
  have hdescent : baseEnd_1453407 < baseStart_1453407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453458 : List Nat := [3, 2, 3, 3, 1, 1, 1, 2, 6]
def baseStart_1453458 : Nat := 118140960795 + 1453458 * 2 ^ 59
def prefixEnd_1453458 : Nat := 4983230072969 + 3 ^ 40 * 1453458 * 2
def baseEnd_1453458 : Nat := 165849458916151016131261

theorem tailTrace_1453458 : CollatzResearch.WordTrace tailWord_1453458 prefixEnd_1453458 165849458916151016131261 := by
  unfold tailWord_1453458
  simp only [CollatzResearch.WordTrace]
  refine ⟨13252992092094342927210257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35341312245584914472560685 13252992092094342927210257)
  ·
    refine ⟨9939744069070757195407693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13252992092094342927210257 9939744069070757195407693)
    ·
      refine ⟨3727404025901533948277885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9939744069070757195407693 3727404025901533948277885)
      ·
        refine ⟨1397776509713075230604207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3727404025901533948277885 1397776509713075230604207)
        ·
          refine ⟨2096664764569612845906311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1397776509713075230604207 2096664764569612845906311)
          ·
            refine ⟨3144997146854419268859467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2096664764569612845906311 3144997146854419268859467)
            ·
              refine ⟨4717495720281628903289201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3144997146854419268859467 4717495720281628903289201)
              ·
                refine ⟨3538121790211221677466901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4717495720281628903289201 3538121790211221677466901)
                ·
                  refine ⟨165849458916151016131261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3538121790211221677466901 165849458916151016131261)
                  ·
                    rfl

theorem cell22_1453458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_1453458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1453458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1453458 prefixEnd_1453458 := by exact prefixLift 1453458
  have htrace : WordTrace (prefixWord ++ tailWord_1453458) baseStart_1453458 baseEnd_1453458 := by
    simpa [prefixWord, tailWord_1453458, baseEnd_1453458] using wordTrace_append hprefix tailTrace_1453458
  have hstable : (prefixWord ++ tailWord_1453458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453458).length < 2 ^ (prefixWord ++ tailWord_1453458).sum := by decide
  have hdescent : baseEnd_1453458 < baseStart_1453458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453471 : List Nat := [1, 1, 2, 5, 1, 2, 3, 1, 2, 4]
def baseStart_1453471 : Nat := 118140960795 + 1453471 * 2 ^ 59
def prefixEnd_1453471 : Nat := 4983230072969 + 3 ^ 40 * 1453471 * 2
def baseEnd_1453471 : Nat := 497552826914125347818743

theorem tailTrace_1453471 : CollatzResearch.WordTrace tailWord_1453471 prefixEnd_1453471 497552826914125347818743 := by
  unfold tailWord_1453471
  simp only [CollatzResearch.WordTrace]
  refine ⟨53012442517330274929064267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35341628344886849952709511 53012442517330274929064267)
  ·
    refine ⟨79518663775995412393596401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53012442517330274929064267 79518663775995412393596401)
    ·
      refine ⟨59638997831996559295197301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79518663775995412393596401 59638997831996559295197301)
      ·
        refine ⟨5591156046749677433924747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59638997831996559295197301 5591156046749677433924747)
        ·
          refine ⟨8386734070124516150887121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5591156046749677433924747 8386734070124516150887121)
          ·
            refine ⟨6290050552593387113165341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8386734070124516150887121 6290050552593387113165341)
            ·
              refine ⟨2358768957222520167437003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6290050552593387113165341 2358768957222520167437003)
              ·
                refine ⟨3538153435833780251155505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2358768957222520167437003 3538153435833780251155505)
                ·
                  refine ⟨2653615076875335188366629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3538153435833780251155505 2653615076875335188366629)
                  ·
                    refine ⟨497552826914125347818743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2653615076875335188366629 497552826914125347818743)
                    ·
                      rfl

theorem cell22_1453471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 4].length) (baseStart_1453471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1453471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1453471 prefixEnd_1453471 := by exact prefixLift 1453471
  have htrace : WordTrace (prefixWord ++ tailWord_1453471) baseStart_1453471 baseEnd_1453471 := by
    simpa [prefixWord, tailWord_1453471, baseEnd_1453471] using wordTrace_append hprefix tailTrace_1453471
  have hstable : (prefixWord ++ tailWord_1453471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453471).length < 2 ^ (prefixWord ++ tailWord_1453471).sum := by decide
  have hdescent : baseEnd_1453471 < baseStart_1453471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453559 : List Nat := [1, 1, 3, 1, 1, 1, 1, 7, 6]
def baseStart_1453559 : Nat := 118140960795 + 1453559 * 2 ^ 59
def prefixEnd_1453559 : Nat := 4983230072969 + 3 ^ 40 * 1453559 * 2
def baseEnd_1453559 : Nat := 165860983704174150539491

theorem tailTrace_1453559 : CollatzResearch.WordTrace tailWord_1453559 prefixEnd_1453559 165860983704174150539491 := by
  unfold tailWord_1453559
  simp only [CollatzResearch.WordTrace]
  refine ⟨53015652141011465958267731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35343768094007643972178487 53015652141011465958267731)
  ·
    refine ⟨79523478211517198937401597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53015652141011465958267731 79523478211517198937401597)
    ·
      refine ⟨29821304329318949601525599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79523478211517198937401597 29821304329318949601525599)
      ·
        refine ⟨44731956493978424402288399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29821304329318949601525599 44731956493978424402288399)
        ·
          refine ⟨67097934740967636603432599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44731956493978424402288399 67097934740967636603432599)
          ·
            refine ⟨100646902111451454905148899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67097934740967636603432599 100646902111451454905148899)
            ·
              refine ⟨150970353167177182357723349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100646902111451454905148899 150970353167177182357723349)
              ·
                refine ⟨3538367652355715211509141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 150970353167177182357723349 3538367652355715211509141)
                ·
                  refine ⟨165860983704174150539491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3538367652355715211509141 165860983704174150539491)
                  ·
                    rfl

theorem cell22_1453559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 6].length) (baseStart_1453559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1453559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1453559 prefixEnd_1453559 := by exact prefixLift 1453559
  have htrace : WordTrace (prefixWord ++ tailWord_1453559) baseStart_1453559 baseEnd_1453559 := by
    simpa [prefixWord, tailWord_1453559, baseEnd_1453559] using wordTrace_append hprefix tailTrace_1453559
  have hstable : (prefixWord ++ tailWord_1453559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453559).length < 2 ^ (prefixWord ++ tailWord_1453559).sum := by decide
  have hdescent : baseEnd_1453559 < baseStart_1453559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453578 : List Nat := [3, 1, 2, 2, 2, 2, 3, 2, 1, 4]
def baseStart_1453578 : Nat := 118140960795 + 1453578 * 2 ^ 59
def prefixEnd_1453578 : Nat := 4983230072969 + 3 ^ 40 * 1453578 * 2
def baseEnd_1453578 : Nat := 497589455200812735393415

theorem tailTrace_1453578 : CollatzResearch.WordTrace tailWord_1453578 prefixEnd_1453578 497589455200812735393415 := by
  unfold tailWord_1453578
  simp only [CollatzResearch.WordTrace]
  refine ⟨13254086281985658050802347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35344230085295088135472925 13254086281985658050802347)
  ·
    refine ⟨19881129422978487076203521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13254086281985658050802347 19881129422978487076203521)
    ·
      refine ⟨14910847067233865307152641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19881129422978487076203521 14910847067233865307152641)
      ·
        refine ⟨11183135300425398980364481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14910847067233865307152641 11183135300425398980364481)
        ·
          refine ⟨8387351475319049235273361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11183135300425398980364481 8387351475319049235273361)
          ·
            refine ⟨6290513606489286926455021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8387351475319049235273361 6290513606489286926455021)
            ·
              refine ⟨2358942602433482597420633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6290513606489286926455021 2358942602433482597420633)
              ·
                refine ⟨1769206951825111948065475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2358942602433482597420633 1769206951825111948065475)
                ·
                  refine ⟨2653810427737667922098213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1769206951825111948065475 2653810427737667922098213)
                  ·
                    refine ⟨497589455200812735393415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2653810427737667922098213 497589455200812735393415)
                    ·
                      rfl

theorem cell22_1453578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_1453578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1453578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1453578 prefixEnd_1453578 := by exact prefixLift 1453578
  have htrace : WordTrace (prefixWord ++ tailWord_1453578) baseStart_1453578 baseEnd_1453578 := by
    simpa [prefixWord, tailWord_1453578, baseEnd_1453578] using wordTrace_append hprefix tailTrace_1453578
  have hstable : (prefixWord ++ tailWord_1453578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453578).length < 2 ^ (prefixWord ++ tailWord_1453578).sum := by decide
  have hdescent : baseEnd_1453578 < baseStart_1453578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453604 : List Nat := [2, 3, 1, 16]
def baseStart_1453604 : Nat := 118140960795 + 1453604 * 2 ^ 59
def prefixEnd_1453604 : Nat := 4983230072969 + 3 ^ 40 * 1453604 * 2
def baseEnd_1453604 : Nat := 682576619385675355615

theorem tailTrace_1453604 : CollatzResearch.WordTrace tailWord_1453604 prefixEnd_1453604 682576619385675355615 := by
  unfold tailWord_1453604
  simp only [CollatzResearch.WordTrace]
  refine ⟨26508646712924219321827933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35344862283898959095770577 26508646712924219321827933)
  ·
    refine ⟨9940742517346582245685475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26508646712924219321827933 9940742517346582245685475)
    ·
      refine ⟨14911113776019873368528213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9940742517346582245685475 14911113776019873368528213)
      ·
        refine ⟨682576619385675355615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 14911113776019873368528213 682576619385675355615)
        ·
          rfl

theorem cell22_1453604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 16].length) (baseStart_1453604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1453604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1453604 prefixEnd_1453604 := by exact prefixLift 1453604
  have htrace : WordTrace (prefixWord ++ tailWord_1453604) baseStart_1453604 baseEnd_1453604 := by
    simpa [prefixWord, tailWord_1453604, baseEnd_1453604] using wordTrace_append hprefix tailTrace_1453604
  have hstable : (prefixWord ++ tailWord_1453604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453604).length < 2 ^ (prefixWord ++ tailWord_1453604).sum := by decide
  have hdescent : baseEnd_1453604 < baseStart_1453604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453621 : List Nat := [1, 3, 3, 1, 1, 3, 3, 7]
def baseStart_1453621 : Nat := 118140960795 + 1453621 * 2 ^ 59
def prefixEnd_1453621 : Nat := 4983230072969 + 3 ^ 40 * 1453621 * 2
def baseEnd_1453621 : Nat := 55289352775508328507587

theorem tailTrace_1453621 : CollatzResearch.WordTrace tailWord_1453621 prefixEnd_1453621 55289352775508328507587 := by
  unfold tailWord_1453621
  simp only [CollatzResearch.WordTrace]
  refine ⟨53017913466786850547024717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35345275644524567031349811 53017913466786850547024717)
  ·
    refine ⟨19881717550045068955134269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53017913466786850547024717 19881717550045068955134269)
    ·
      refine ⟨7455644081266900858175351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19881717550045068955134269 7455644081266900858175351)
      ·
        refine ⟨11183466121900351287263027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7455644081266900858175351 11183466121900351287263027)
        ·
          refine ⟨16775199182850526930894541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11183466121900351287263027 16775199182850526930894541)
          ·
            refine ⟨6290699693568947599085453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16775199182850526930894541 6290699693568947599085453)
            ·
              refine ⟨2359012385088355349657045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6290699693568947599085453 2359012385088355349657045)
              ·
                refine ⟨55289352775508328507587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2359012385088355349657045 55289352775508328507587)
                ·
                  rfl

theorem cell22_1453621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 7].length) (baseStart_1453621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1453621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1453621 prefixEnd_1453621 := by exact prefixLift 1453621
  have htrace : WordTrace (prefixWord ++ tailWord_1453621) baseStart_1453621 baseEnd_1453621 := by
    simpa [prefixWord, tailWord_1453621, baseEnd_1453621] using wordTrace_append hprefix tailTrace_1453621
  have hstable : (prefixWord ++ tailWord_1453621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453621).length < 2 ^ (prefixWord ++ tailWord_1453621).sum := by decide
  have hdescent : baseEnd_1453621 < baseStart_1453621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453728 : List Nat := [2, 1, 1, 4, 3, 1, 3, 1, 6]
def baseStart_1453728 : Nat := 118140960795 + 1453728 * 2 ^ 59
def prefixEnd_1453728 : Nat := 4983230072969 + 3 ^ 40 * 1453728 * 2
def baseEnd_1453728 : Nat := 165880267755420781380985

theorem tailTrace_1453728 : CollatzResearch.WordTrace tailWord_1453728 prefixEnd_1453728 165880267755420781380985 := by
  unfold tailWord_1453728
  simp only [CollatzResearch.WordTrace]
  refine ⟨26510908038699603910584919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35347877384932805214113225 26510908038699603910584919)
  ·
    refine ⟨39766362058049405865877379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26510908038699603910584919 39766362058049405865877379)
    ·
      refine ⟨59649543087074108798816069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39766362058049405865877379 59649543087074108798816069)
      ·
        refine ⟨11184289328826395399778013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59649543087074108798816069 11184289328826395399778013)
        ·
          refine ⟨4194108498309898274916755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11184289328826395399778013 4194108498309898274916755)
          ·
            refine ⟨6291162747464847412375133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4194108498309898274916755 6291162747464847412375133)
            ·
              refine ⟨2359186030299317779640675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6291162747464847412375133 2359186030299317779640675)
              ·
                refine ⟨3538779045448976669461013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2359186030299317779640675 3538779045448976669461013)
                ·
                  refine ⟨165880267755420781380985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3538779045448976669461013 165880267755420781380985)
                  ·
                    rfl

theorem cell22_1453728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 6].length) (baseStart_1453728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1453728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1453728 prefixEnd_1453728 := by exact prefixLift 1453728
  have htrace : WordTrace (prefixWord ++ tailWord_1453728) baseStart_1453728 baseEnd_1453728 := by
    simpa [prefixWord, tailWord_1453728, baseEnd_1453728] using wordTrace_append hprefix tailTrace_1453728
  have hstable : (prefixWord ++ tailWord_1453728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453728).length < 2 ^ (prefixWord ++ tailWord_1453728).sum := by decide
  have hdescent : baseEnd_1453728 < baseStart_1453728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453801 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 9]
def baseStart_1453801 : Nat := 118140960795 + 1453801 * 2 ^ 59
def prefixEnd_1453801 : Nat := 4983230072969 + 3 ^ 40 * 1453801 * 2
def baseEnd_1453801 : Nat := 165888597552704829022577

theorem tailTrace_1453801 : CollatzResearch.WordTrace tailWord_1453801 prefixEnd_1453801 165888597552704829022577 := by
  unfold tailWord_1453801
  simp only [CollatzResearch.WordTrace]
  refine ⟨53024478606134741288577257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35349652404089827525718171 53024478606134741288577257)
  ·
    refine ⟨39768358954601055966432943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53024478606134741288577257 39768358954601055966432943)
    ·
      refine ⟨59652538431901583949649415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39768358954601055966432943 59652538431901583949649415)
      ·
        refine ⟨89478807647852375924474123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59652538431901583949649415 89478807647852375924474123)
        ·
          refine ⟨134218211471778563886711185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89478807647852375924474123 134218211471778563886711185)
          ·
            refine ⟨100663658603833922915033389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134218211471778563886711185 100663658603833922915033389)
            ·
              refine ⟨37748871976437721093137521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100663658603833922915033389 37748871976437721093137521)
              ·
                refine ⟨28311653982328290819853141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37748871976437721093137521 28311653982328290819853141)
                ·
                  refine ⟨165888597552704829022577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28311653982328290819853141 165888597552704829022577)
                  ·
                    rfl

theorem cell22_1453801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 9].length) (baseStart_1453801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1453801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1453801 prefixEnd_1453801 := by exact prefixLift 1453801
  have htrace : WordTrace (prefixWord ++ tailWord_1453801) baseStart_1453801 baseEnd_1453801 := by
    simpa [prefixWord, tailWord_1453801, baseEnd_1453801] using wordTrace_append hprefix tailTrace_1453801
  have hstable : (prefixWord ++ tailWord_1453801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453801).length < 2 ^ (prefixWord ++ tailWord_1453801).sum := by decide
  have hdescent : baseEnd_1453801 < baseStart_1453801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453805 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 5, 3]
def baseStart_1453805 : Nat := 118140960795 + 1453805 * 2 ^ 59
def prefixEnd_1453805 : Nat := 4983230072969 + 3 ^ 40 * 1453805 * 2
def baseEnd_1453805 : Nat := 497667161939859809967719

theorem tailTrace_1453805 : CollatzResearch.WordTrace tailWord_1453805 prefixEnd_1453805 497667161939859809967719 := by
  unfold tailWord_1453805
  simp only [CollatzResearch.WordTrace]
  refine ⟨53024624498120249971722869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35349749665413499981148579 53024624498120249971722869)
  ·
    refine ⟨4971058546698773434849019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53024624498120249971722869 4971058546698773434849019)
    ·
      refine ⟨7456587820048160152273529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4971058546698773434849019 7456587820048160152273529)
      ·
        refine ⟨5592440865036120114205147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7456587820048160152273529 5592440865036120114205147)
        ·
          refine ⟨8388661297554180171307721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5592440865036120114205147 8388661297554180171307721)
          ·
            refine ⟨6291495973165635128480791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8388661297554180171307721 6291495973165635128480791)
            ·
              refine ⟨9437243959748452692721187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6291495973165635128480791 9437243959748452692721187)
              ·
                refine ⟨14155865939622679039081781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9437243959748452692721187 14155865939622679039081781)
                ·
                  refine ⟨1327112431839626159913917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14155865939622679039081781 1327112431839626159913917)
                  ·
                    refine ⟨497667161939859809967719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1327112431839626159913917 497667161939859809967719)
                    ·
                      rfl

theorem cell22_1453805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_1453805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1453805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1453805 prefixEnd_1453805 := by exact prefixLift 1453805
  have htrace : WordTrace (prefixWord ++ tailWord_1453805) baseStart_1453805 baseEnd_1453805 := by
    simpa [prefixWord, tailWord_1453805, baseEnd_1453805] using wordTrace_append hprefix tailTrace_1453805
  have hstable : (prefixWord ++ tailWord_1453805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453805).length < 2 ^ (prefixWord ++ tailWord_1453805).sum := by decide
  have hdescent : baseEnd_1453805 < baseStart_1453805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453848 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 5, 4]
def baseStart_1453848 : Nat := 118140960795 + 1453848 * 2 ^ 59
def prefixEnd_1453848 : Nat := 4983230072969 + 3 ^ 40 * 1453848 * 2
def baseEnd_1453848 : Nat := 497681881718622031142587

theorem tailTrace_1453848 : CollatzResearch.WordTrace tailWord_1453848 prefixEnd_1453848 497681881718622031142587 := by
  unfold tailWord_1453848
  simp only [CollatzResearch.WordTrace]
  refine ⟨26513096418482234157769099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35350795224642978877025465 26513096418482234157769099)
  ·
    refine ⟨39769644627723351236653649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26513096418482234157769099 39769644627723351236653649)
    ·
      refine ⟨29827233470792513427490237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39769644627723351236653649 29827233470792513427490237)
      ·
        refine ⟨11185212551547192535308839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29827233470792513427490237 11185212551547192535308839)
        ·
          refine ⟨16777818827320788802963259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11185212551547192535308839 16777818827320788802963259)
          ·
            refine ⟨25166728240981183204444889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16777818827320788802963259 25166728240981183204444889)
            ·
              refine ⟨18875046180735887403333667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25166728240981183204444889 18875046180735887403333667)
              ·
                refine ⟨28312569271103831105000501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18875046180735887403333667 28312569271103831105000501)
                ·
                  refine ⟨2654303369165984166093797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28312569271103831105000501 2654303369165984166093797)
                  ·
                    refine ⟨497681881718622031142587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2654303369165984166093797 497681881718622031142587)
                    ·
                      rfl

theorem cell22_1453848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_1453848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1453848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1453848 prefixEnd_1453848 := by exact prefixLift 1453848
  have htrace : WordTrace (prefixWord ++ tailWord_1453848) baseStart_1453848 baseEnd_1453848 := by
    simpa [prefixWord, tailWord_1453848, baseEnd_1453848] using wordTrace_append hprefix tailTrace_1453848
  have hstable : (prefixWord ++ tailWord_1453848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453848).length < 2 ^ (prefixWord ++ tailWord_1453848).sum := by decide
  have hdescent : baseEnd_1453848 < baseStart_1453848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453895 : List Nat := [1, 1, 4, 1, 2, 1, 4, 1, 4, 3]
def baseStart_1453895 : Nat := 118140960795 + 1453895 * 2 ^ 59
def prefixEnd_1453895 : Nat := 4983230072969 + 3 ^ 40 * 1453895 * 2
def baseEnd_1453895 : Nat := 497697970779129575217443

theorem tailTrace_1453895 : CollatzResearch.WordTrace tailWord_1453895 prefixEnd_1453895 497697970779129575217443 := by
  unfold tailWord_1453895
  simp only [CollatzResearch.WordTrace]
  refine ⟨53027907067794195342499139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35351938045196130228332759 53027907067794195342499139)
  ·
    refine ⟨79541860601691293013748709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53027907067794195342499139 79541860601691293013748709)
    ·
      refine ⟨14914098862817117440077883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79541860601691293013748709 14914098862817117440077883)
      ·
        refine ⟨22371148294225676160116825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14914098862817117440077883 22371148294225676160116825)
        ·
          refine ⟨16778361220669257120087619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22371148294225676160116825 16778361220669257120087619)
          ·
            refine ⟨25167541831003885680131429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16778361220669257120087619 25167541831003885680131429)
            ·
              refine ⟨4718914093313228565024643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25167541831003885680131429 4718914093313228565024643)
              ·
                refine ⟨7078371139969842847536965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4718914093313228565024643 7078371139969842847536965)
                ·
                  refine ⟨1327194588744345533913181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7078371139969842847536965 1327194588744345533913181)
                  ·
                    refine ⟨497697970779129575217443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1327194588744345533913181 497697970779129575217443)
                    ·
                      rfl

theorem cell22_1453895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_1453895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1453895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1453895 prefixEnd_1453895 := by exact prefixLift 1453895
  have htrace : WordTrace (prefixWord ++ tailWord_1453895) baseStart_1453895 baseEnd_1453895 := by
    simpa [prefixWord, tailWord_1453895, baseEnd_1453895] using wordTrace_append hprefix tailTrace_1453895
  have hstable : (prefixWord ++ tailWord_1453895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453895).length < 2 ^ (prefixWord ++ tailWord_1453895).sum := by decide
  have hdescent : baseEnd_1453895 < baseStart_1453895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453897 : List Nat := [1, 2, 1, 1, 2, 4, 5, 2, 4]
def baseStart_1453897 : Nat := 118140960795 + 1453897 * 2 ^ 59
def prefixEnd_1453897 : Nat := 4983230072969 + 3 ^ 40 * 1453897 * 2
def baseEnd_1453897 : Nat := 165899551806667412222479

theorem tailTrace_1453897 : CollatzResearch.WordTrace tailWord_1453897 prefixEnd_1453897 165899551806667412222479 := by
  unfold tailWord_1453897
  simp only [CollatzResearch.WordTrace]
  refine ⟨53027980013786949684071945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35351986675857966456047963 53027980013786949684071945)
  ·
    refine ⟨39770985010340212263053959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53027980013786949684071945 39770985010340212263053959)
    ·
      refine ⟨59656477515510318394580939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39770985010340212263053959 59656477515510318394580939)
      ·
        refine ⟨89484716273265477591871409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59656477515510318394580939 89484716273265477591871409)
        ·
          refine ⟨67113537204949108193903557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89484716273265477591871409 67113537204949108193903557)
          ·
            refine ⟨12583788225927957786356917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67113537204949108193903557 12583788225927957786356917)
            ·
              refine ⟨1179730146180746042470961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12583788225927957786356917 1179730146180746042470961)
              ·
                refine ⟨884797609635559531853221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1179730146180746042470961 884797609635559531853221)
                ·
                  refine ⟨165899551806667412222479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 884797609635559531853221 165899551806667412222479)
                  ·
                    rfl

theorem cell22_1453897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2, 4].length) (baseStart_1453897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1453897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1453897 prefixEnd_1453897 := by exact prefixLift 1453897
  have htrace : WordTrace (prefixWord ++ tailWord_1453897) baseStart_1453897 baseEnd_1453897 := by
    simpa [prefixWord, tailWord_1453897, baseEnd_1453897] using wordTrace_append hprefix tailTrace_1453897
  have hstable : (prefixWord ++ tailWord_1453897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453897).length < 2 ^ (prefixWord ++ tailWord_1453897).sum := by decide
  have hdescent : baseEnd_1453897 < baseStart_1453897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453916 : List Nat := [2, 2, 4, 2, 3, 1, 1, 2, 1, 4]
def baseStart_1453916 : Nat := 118140960795 + 1453916 * 2 ^ 59
def prefixEnd_1453916 : Nat := 4983230072969 + 3 ^ 40 * 1453916 * 2
def baseEnd_1453916 : Nat := 497705159508292520442379

theorem tailTrace_1453916 : CollatzResearch.WordTrace tailWord_1453916 prefixEnd_1453916 497705159508292520442379 := by
  unfold tailWord_1453916
  simp only [CollatzResearch.WordTrace]
  refine ⟨26514336500359057964506801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35352448667145410619342401 26514336500359057964506801)
  ·
    refine ⟨19885752375269293473380101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26514336500359057964506801 19885752375269293473380101)
    ·
      refine ⟨3728578570362992526258769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19885752375269293473380101 3728578570362992526258769)
      ·
        refine ⟨2796433927772244394694077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3728578570362992526258769 2796433927772244394694077)
        ·
          refine ⟨1048662722914591648010279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2796433927772244394694077 1048662722914591648010279)
          ·
            refine ⟨1572994084371887472015419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1048662722914591648010279 1572994084371887472015419)
            ·
              refine ⟨2359491126557831208023129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1572994084371887472015419 2359491126557831208023129)
              ·
                refine ⟨1769618344918373406017347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2359491126557831208023129 1769618344918373406017347)
                ·
                  refine ⟨2654427517377560109026021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1769618344918373406017347 2654427517377560109026021)
                  ·
                    refine ⟨497705159508292520442379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2654427517377560109026021 497705159508292520442379)
                    ·
                      rfl

theorem cell22_1453916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_1453916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1453916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1453916 prefixEnd_1453916 := by exact prefixLift 1453916
  have htrace : WordTrace (prefixWord ++ tailWord_1453916) baseStart_1453916 baseEnd_1453916 := by
    simpa [prefixWord, tailWord_1453916, baseEnd_1453916] using wordTrace_append hprefix tailTrace_1453916
  have hstable : (prefixWord ++ tailWord_1453916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453916).length < 2 ^ (prefixWord ++ tailWord_1453916).sum := by decide
  have hdescent : baseEnd_1453916 < baseStart_1453916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453942 : List Nat := [5, 1, 1, 3, 3, 9]
def baseStart_1453942 : Nat := 118140960795 + 1453942 * 2 ^ 59
def prefixEnd_1453942 : Nat := 4983230072969 + 3 ^ 40 * 1453942 * 2
def baseEnd_1453942 : Nat := 6144618022711569373979

theorem tailTrace_1453942 : CollatzResearch.WordTrace tailWord_1453942 prefixEnd_1453942 6144618022711569373979 := by
  unfold tailWord_1453942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3314351331163995148091255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35353080865749281579640053 3314351331163995148091255)
  ·
    refine ⟨4971526996745992722136883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3314351331163995148091255 4971526996745992722136883)
    ·
      refine ⟨7457290495118989083205325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4971526996745992722136883 7457290495118989083205325)
      ·
        refine ⟨2796483935669620906201997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7457290495118989083205325 2796483935669620906201997)
        ·
          refine ⟨1048681475876107839825749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2796483935669620906201997 1048681475876107839825749)
          ·
            refine ⟨6144618022711569373979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1048681475876107839825749 6144618022711569373979)
            ·
              rfl

theorem cell22_1453942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 9].length) (baseStart_1453942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1453942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1453942 prefixEnd_1453942 := by exact prefixLift 1453942
  have htrace : WordTrace (prefixWord ++ tailWord_1453942) baseStart_1453942 baseEnd_1453942 := by
    simpa [prefixWord, tailWord_1453942, baseEnd_1453942] using wordTrace_append hprefix tailTrace_1453942
  have hstable : (prefixWord ++ tailWord_1453942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453942).length < 2 ^ (prefixWord ++ tailWord_1453942).sum := by decide
  have hdescent : baseEnd_1453942 < baseStart_1453942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453968 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 1, 7]
def baseStart_1453968 : Nat := 118140960795 + 1453968 * 2 ^ 59
def prefixEnd_1453968 : Nat := 4983230072969 + 3 ^ 40 * 1453968 * 2
def baseEnd_1453968 : Nat := 497722960170981718142219

theorem tailTrace_1453968 : CollatzResearch.WordTrace tailWord_1453968 prefixEnd_1453968 497722960170981718142219 := by
  unfold tailWord_1453968
  simp only [CollatzResearch.WordTrace]
  refine ⟨26515284798264864404953279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35353713064353152539937705 26515284798264864404953279)
  ·
    refine ⟨39772927197397296607429919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26515284798264864404953279 39772927197397296607429919)
    ·
      refine ⟨59659390796095944911144879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39772927197397296607429919 59659390796095944911144879)
      ·
        refine ⟨89489086194143917366717319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59659390796095944911144879 89489086194143917366717319)
        ·
          refine ⟨134233629291215876050075979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89489086194143917366717319 134233629291215876050075979)
          ·
            refine ⟨201350443936823814075113969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134233629291215876050075979 201350443936823814075113969)
            ·
              refine ⟨151012832952617860556335477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201350443936823814075113969 151012832952617860556335477)
              ·
                refine ⟨14157453089307924427156451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 151012832952617860556335477 14157453089307924427156451)
                ·
                  refine ⟨21236179633961886640734677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14157453089307924427156451 21236179633961886640734677)
                  ·
                    refine ⟨497722960170981718142219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21236179633961886640734677 497722960170981718142219)
                    ·
                      rfl

theorem cell22_1453968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 1, 7].length) (baseStart_1453968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1453968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1453968 prefixEnd_1453968 := by exact prefixLift 1453968
  have htrace : WordTrace (prefixWord ++ tailWord_1453968) baseStart_1453968 baseEnd_1453968 := by
    simpa [prefixWord, tailWord_1453968, baseEnd_1453968] using wordTrace_append hprefix tailTrace_1453968
  have hstable : (prefixWord ++ tailWord_1453968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453968).length < 2 ^ (prefixWord ++ tailWord_1453968).sum := by decide
  have hdescent : baseEnd_1453968 < baseStart_1453968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453991 : List Nat := [1, 1, 6, 1, 2, 2, 2, 3, 1, 3]
def baseStart_1453991 : Nat := 118140960795 + 1453991 * 2 ^ 59
def prefixEnd_1453991 : Nat := 4983230072969 + 3 ^ 40 * 1453991 * 2
def baseEnd_1453991 : Nat := 497730833541017324817149

theorem tailTrace_1453991 : CollatzResearch.WordTrace tailWord_1453991 prefixEnd_1453991 497730833541017324817149 := by
  unfold tailWord_1453991
  simp only [CollatzResearch.WordTrace]
  refine ⟨53031408475446403737993827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35354272316964269158662551 53031408475446403737993827)
  ·
    refine ⟨79547112713169605606990741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53031408475446403737993827 79547112713169605606990741)
    ·
      refine ⟨3728770908429825262827691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 79547112713169605606990741 3728770908429825262827691)
      ·
        refine ⟨5593156362644737894241537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3728770908429825262827691 5593156362644737894241537)
        ·
          refine ⟨4194867271983553420681153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5593156362644737894241537 4194867271983553420681153)
          ·
            refine ⟨3146150453987665065510865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4194867271983553420681153 3146150453987665065510865)
            ·
              refine ⟨2359612840490748799133149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3146150453987665065510865 2359612840490748799133149)
              ·
                refine ⟨884854815184030799674931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2359612840490748799133149 884854815184030799674931)
                ·
                  refine ⟨1327282222776046199512397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 884854815184030799674931 1327282222776046199512397)
                  ·
                    refine ⟨497730833541017324817149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1327282222776046199512397 497730833541017324817149)
                    ·
                      rfl

theorem cell22_1453991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_1453991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1453991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1453991 prefixEnd_1453991 := by exact prefixLift 1453991
  have htrace : WordTrace (prefixWord ++ tailWord_1453991) baseStart_1453991 baseEnd_1453991 := by
    simpa [prefixWord, tailWord_1453991, baseEnd_1453991] using wordTrace_append hprefix tailTrace_1453991
  have hstable : (prefixWord ++ tailWord_1453991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453991).length < 2 ^ (prefixWord ++ tailWord_1453991).sum := by decide
  have hdescent : baseEnd_1453991 < baseStart_1453991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454004 : List Nat := [2, 5, 2, 1, 2, 1, 1, 1, 7]
def baseStart_1454004 : Nat := 118140960795 + 1454004 * 2 ^ 59
def prefixEnd_1454004 : Nat := 4983230072969 + 3 ^ 40 * 1454004 * 2
def baseEnd_1454004 : Nat := 165911761235563208080703

theorem tailTrace_1454004 : CollatzResearch.WordTrace tailWord_1454004 prefixEnd_1454004 165911761235563208080703 := by
  unfold tailWord_1454004
  simp only [CollatzResearch.WordTrace]
  refine ⟨26515941312199653479108533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35354588416266204638811377 26515941312199653479108533)
  ·
    refine ⟨2485869498018717513666425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26515941312199653479108533 2485869498018717513666425)
    ·
      refine ⟨1864402123514038135249819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2485869498018717513666425 1864402123514038135249819)
      ·
        refine ⟨2796603185271057202874729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1864402123514038135249819 2796603185271057202874729)
        ·
          refine ⟨2097452388953292902156047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2796603185271057202874729 2097452388953292902156047)
          ·
            refine ⟨3146178583429939353234071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2097452388953292902156047 3146178583429939353234071)
            ·
              refine ⟨4719267875144909029851107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3146178583429939353234071 4719267875144909029851107)
              ·
                refine ⟨7078901812717363544776661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4719267875144909029851107 7078901812717363544776661)
                ·
                  refine ⟨165911761235563208080703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7078901812717363544776661 165911761235563208080703)
                  ·
                    rfl

theorem cell22_1454004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_1454004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1454004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1454004 prefixEnd_1454004 := by exact prefixLift 1454004
  have htrace : WordTrace (prefixWord ++ tailWord_1454004) baseStart_1454004 baseEnd_1454004 := by
    simpa [prefixWord, tailWord_1454004, baseEnd_1454004] using wordTrace_append hprefix tailTrace_1454004
  have hstable : (prefixWord ++ tailWord_1454004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454004).length < 2 ^ (prefixWord ++ tailWord_1454004).sum := by decide
  have hdescent : baseEnd_1454004 < baseStart_1454004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454015 : List Nat := [1, 1, 2, 2, 2, 1, 6, 1, 6]
def baseStart_1454015 : Nat := 118140960795 + 1454015 * 2 ^ 59
def prefixEnd_1454015 : Nat := 4983230072969 + 3 ^ 40 * 1454015 * 2
def baseEnd_1454015 : Nat := 165913016410496420739025

theorem tailTrace_1454015 : CollatzResearch.WordTrace tailWord_1454015 prefixEnd_1454015 165913016410496420739025 := by
  unfold tailWord_1454015
  simp only [CollatzResearch.WordTrace]
  refine ⟨53032283827359455836867499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35354855884906303891244999 53032283827359455836867499)
  ·
    refine ⟨79548425741039183755301249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53032283827359455836867499 79548425741039183755301249)
    ·
      refine ⟨59661319305779387816475937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79548425741039183755301249 59661319305779387816475937)
      ·
        refine ⟨44745989479334540862356953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59661319305779387816475937 44745989479334540862356953)
        ·
          refine ⟨33559492109500905646767715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44745989479334540862356953 33559492109500905646767715)
          ·
            refine ⟨50339238164251358470151573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33559492109500905646767715 50339238164251358470151573)
            ·
              refine ⟨2359651788949282428288355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50339238164251358470151573 2359651788949282428288355)
              ·
                refine ⟨3539477683423923642432533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2359651788949282428288355 3539477683423923642432533)
                ·
                  refine ⟨165913016410496420739025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3539477683423923642432533 165913016410496420739025)
                  ·
                    rfl

theorem cell22_1454015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 6].length) (baseStart_1454015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1454015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1454015 prefixEnd_1454015 := by exact prefixLift 1454015
  have htrace : WordTrace (prefixWord ++ tailWord_1454015) baseStart_1454015 baseEnd_1454015 := by
    simpa [prefixWord, tailWord_1454015, baseEnd_1454015] using wordTrace_append hprefix tailTrace_1454015
  have hstable : (prefixWord ++ tailWord_1454015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454015).length < 2 ^ (prefixWord ++ tailWord_1454015).sum := by decide
  have hdescent : baseEnd_1454015 < baseStart_1454015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454047 : List Nat := [1, 1, 2, 3, 4, 1, 1, 2, 4, 3]
def baseStart_1454047 : Nat := 118140960795 + 1454047 * 2 ^ 59
def prefixEnd_1454047 : Nat := 4983230072969 + 3 ^ 40 * 1454047 * 2
def baseEnd_1454047 : Nat := 497750003485451845416977

theorem tailTrace_1454047 : CollatzResearch.WordTrace tailWord_1454047 prefixEnd_1454047 497750003485451845416977 := by
  unfold tailWord_1454047
  simp only [CollatzResearch.WordTrace]
  refine ⟨53033450963243525302032395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35355633975495683534688263 53033450963243525302032395)
  ·
    refine ⟨79550176444865287953048593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53033450963243525302032395 79550176444865287953048593)
    ·
      refine ⟨59662632333648965964786445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79550176444865287953048593 59662632333648965964786445)
      ·
        refine ⟨22373487125118362236794917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59662632333648965964786445 22373487125118362236794917)
        ·
          refine ⟨4195028835959692919399047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22373487125118362236794917 4195028835959692919399047)
          ·
            refine ⟨6292543253939539379098571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4195028835959692919399047 6292543253939539379098571)
            ·
              refine ⟨9438814880909309068647857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6292543253939539379098571 9438814880909309068647857)
              ·
                refine ⟨7079111160681981801485893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9438814880909309068647857 7079111160681981801485893)
                ·
                  refine ⟨1327333342627871587778605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7079111160681981801485893 1327333342627871587778605)
                  ·
                    refine ⟨497750003485451845416977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1327333342627871587778605 497750003485451845416977)
                    ·
                      rfl

theorem cell22_1454047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4, 3].length) (baseStart_1454047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1454047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1454047 prefixEnd_1454047 := by exact prefixLift 1454047
  have htrace : WordTrace (prefixWord ++ tailWord_1454047) baseStart_1454047 baseEnd_1454047 := by
    simpa [prefixWord, tailWord_1454047, baseEnd_1454047] using wordTrace_append hprefix tailTrace_1454047
  have hstable : (prefixWord ++ tailWord_1454047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454047).length < 2 ^ (prefixWord ++ tailWord_1454047).sum := by decide
  have hdescent : baseEnd_1454047 < baseStart_1454047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454062 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 4, 4]
def baseStart_1454062 : Nat := 118140960795 + 1454062 * 2 ^ 59
def prefixEnd_1454062 : Nat := 4983230072969 + 3 ^ 40 * 1454062 * 2
def baseEnd_1454062 : Nat := 497755138291996806291931

theorem tailTrace_1454062 : CollatzResearch.WordTrace tailWord_1454062 prefixEnd_1454062 497755138291996806291931 := by
  unfold tailWord_1454062
  simp only [CollatzResearch.WordTrace]
  refine ⟨6629249757273647857978555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35355998705459455242552293 6629249757273647857978555)
  ·
    refine ⟨9943874635910471786967833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6629249757273647857978555 9943874635910471786967833)
    ·
      refine ⟨7457905976932853840225875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9943874635910471786967833 7457905976932853840225875)
      ·
        refine ⟨11186858965399280760338813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7457905976932853840225875 11186858965399280760338813)
        ·
          refine ⟨4195072112024730285127055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11186858965399280760338813 4195072112024730285127055)
          ·
            refine ⟨6292608168037095427690583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4195072112024730285127055 6292608168037095427690583)
            ·
              refine ⟨9438912252055643141535875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6292608168037095427690583 9438912252055643141535875)
              ·
                refine ⟨14158368378083464712303813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9438912252055643141535875 14158368378083464712303813)
                ·
                  refine ⟨2654694070890649633556965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14158368378083464712303813 2654694070890649633556965)
                  ·
                    refine ⟨497755138291996806291931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2654694070890649633556965 497755138291996806291931)
                    ·
                      rfl

theorem cell22_1454062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_1454062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1454062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1454062 prefixEnd_1454062 := by exact prefixLift 1454062
  have htrace : WordTrace (prefixWord ++ tailWord_1454062) baseStart_1454062 baseEnd_1454062 := by
    simpa [prefixWord, tailWord_1454062, baseEnd_1454062] using wordTrace_append hprefix tailTrace_1454062
  have hstable : (prefixWord ++ tailWord_1454062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454062).length < 2 ^ (prefixWord ++ tailWord_1454062).sum := by decide
  have hdescent : baseEnd_1454062 < baseStart_1454062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454092 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 5, 3]
def baseStart_1454092 : Nat := 118140960795 + 1454092 * 2 ^ 59
def prefixEnd_1454092 : Nat := 4983230072969 + 3 ^ 40 * 1454092 * 2
def baseEnd_1454092 : Nat := 497765407905086728041839

theorem tailTrace_1454092 : CollatzResearch.WordTrace tailWord_1454092 prefixEnd_1454092 497765407905086728041839 := by
  unfold tailWord_1454092
  simp only [CollatzResearch.WordTrace]
  refine ⟨26517546124040248993710265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35356728165386998658280353 26517546124040248993710265)
  ·
    refine ⟨19888159593030186745282699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26517546124040248993710265 19888159593030186745282699)
    ·
      refine ⟨29832239389545280117924049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19888159593030186745282699 29832239389545280117924049)
      ·
        refine ⟨22374179542158960088443037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29832239389545280117924049 22374179542158960088443037)
        ·
          refine ⟨8390317328309610033166139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22374179542158960088443037 8390317328309610033166139)
          ·
            refine ⟨12585475992464415049749209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8390317328309610033166139 12585475992464415049749209)
            ·
              refine ⟨9439106994348311287311907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12585475992464415049749209 9439106994348311287311907)
              ·
                refine ⟨14158660491522466930967861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9439106994348311287311907 14158660491522466930967861)
                ·
                  refine ⟨1327374421080231274778237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14158660491522466930967861 1327374421080231274778237)
                  ·
                    refine ⟨497765407905086728041839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1327374421080231274778237 497765407905086728041839)
                    ·
                      rfl

theorem cell22_1454092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 5, 3].length) (baseStart_1454092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1454092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1454092 prefixEnd_1454092 := by exact prefixLift 1454092
  have htrace : WordTrace (prefixWord ++ tailWord_1454092) baseStart_1454092 baseEnd_1454092 := by
    simpa [prefixWord, tailWord_1454092, baseEnd_1454092] using wordTrace_append hprefix tailTrace_1454092
  have hstable : (prefixWord ++ tailWord_1454092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454092).length < 2 ^ (prefixWord ++ tailWord_1454092).sum := by decide
  have hdescent : baseEnd_1454092 < baseStart_1454092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454199 : List Nat := [1, 1, 3, 1, 1, 7, 1, 1, 1, 5]
def baseStart_1454199 : Nat := 118140960795 + 1454199 * 2 ^ 59
def prefixEnd_1454199 : Nat := 4983230072969 + 3 ^ 40 * 1454199 * 2
def baseEnd_1454199 : Nat := 497802036191774115616511

theorem tailTrace_1454199 : CollatzResearch.WordTrace tailWord_1454199 prefixEnd_1454199 497802036191774115616511 := by
  unfold tailWord_1454199
  simp only [CollatzResearch.WordTrace]
  refine ⟨53038994858692855261565651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35359329905795236841043767 53038994858692855261565651)
  ·
    refine ⟨79558492288039282892348477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53038994858692855261565651 79558492288039282892348477)
    ·
      refine ⟨29834434608014731084630679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79558492288039282892348477 29834434608014731084630679)
      ·
        refine ⟨44751651912022096626946019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29834434608014731084630679 44751651912022096626946019)
        ·
          refine ⟨67127477868033144940419029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44751651912022096626946019 67127477868033144940419029)
          ·
            refine ⟨1573300262532026834541071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 67127477868033144940419029 1573300262532026834541071)
            ·
              refine ⟨2359950393798040251811607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1573300262532026834541071 2359950393798040251811607)
              ·
                refine ⟨3539925590697060377717411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2359950393798040251811607 3539925590697060377717411)
                ·
                  refine ⟨5309888386045590566576117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3539925590697060377717411 5309888386045590566576117)
                  ·
                    refine ⟨497802036191774115616511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5309888386045590566576117 497802036191774115616511)
                    ·
                      rfl

theorem cell22_1454199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 5].length) (baseStart_1454199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1454199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1454199 prefixEnd_1454199 := by exact prefixLift 1454199
  have htrace : WordTrace (prefixWord ++ tailWord_1454199) baseStart_1454199 baseEnd_1454199 := by
    simpa [prefixWord, tailWord_1454199, baseEnd_1454199] using wordTrace_append hprefix tailTrace_1454199
  have hstable : (prefixWord ++ tailWord_1454199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454199).length < 2 ^ (prefixWord ++ tailWord_1454199).sum := by decide
  have hdescent : baseEnd_1454199 < baseStart_1454199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454212 : List Nat := [2, 3, 2, 1, 2, 1, 3, 8]
def baseStart_1454212 : Nat := 118140960795 + 1454212 * 2 ^ 59
def prefixEnd_1454212 : Nat := 4983230072969 + 3 ^ 40 * 1454212 * 2
def baseEnd_1454212 : Nat := 55311831817494046115719

theorem tailTrace_1454212 : CollatzResearch.WordTrace tailWord_1454212 prefixEnd_1454212 55311831817494046115719 := by
  unfold tailWord_1454212
  simp only [CollatzResearch.WordTrace]
  refine ⟨26519734503822879240894445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35359646005097172321192593 26519734503822879240894445)
  ·
    refine ⟨9944900438933579715335417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26519734503822879240894445 9944900438933579715335417)
    ·
      refine ⟨7458675329200184786501563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9944900438933579715335417 7458675329200184786501563)
      ·
        refine ⟨11188012993800277179752345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7458675329200184786501563 11188012993800277179752345)
        ·
          refine ⟨8391009745350207884814259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11188012993800277179752345 8391009745350207884814259)
          ·
            refine ⟨12586514618025311827221389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8391009745350207884814259 12586514618025311827221389)
            ·
              refine ⟨4719942981759491935208021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12586514618025311827221389 4719942981759491935208021)
              ·
                refine ⟨55311831817494046115719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4719942981759491935208021 55311831817494046115719)
                ·
                  rfl

theorem cell22_1454212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 8].length) (baseStart_1454212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1454212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1454212 prefixEnd_1454212 := by exact prefixLift 1454212
  have htrace : WordTrace (prefixWord ++ tailWord_1454212) baseStart_1454212 baseEnd_1454212 := by
    simpa [prefixWord, tailWord_1454212, baseEnd_1454212] using wordTrace_append hprefix tailTrace_1454212
  have hstable : (prefixWord ++ tailWord_1454212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454212).length < 2 ^ (prefixWord ++ tailWord_1454212).sum := by decide
  have hdescent : baseEnd_1454212 < baseStart_1454212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454319 : List Nat := [1, 1, 2, 1, 6, 2, 1, 2, 6]
def baseStart_1454319 : Nat := 118140960795 + 1454319 * 2 ^ 59
def prefixEnd_1454319 : Nat := 4983230072969 + 3 ^ 40 * 1454319 * 2
def baseEnd_1454319 : Nat := 165947704881377934205381

theorem tailTrace_1454319 : CollatzResearch.WordTrace tailWord_1454319 prefixEnd_1454319 165947704881377934205381 := by
  unfold tailWord_1454319
  simp only [CollatzResearch.WordTrace]
  refine ⟨53043371618258115755934011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35362247745505410503956007 53043371618258115755934011)
  ·
    refine ⟨79565057427387173633901017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53043371618258115755934011 79565057427387173633901017)
    ·
      refine ⟨59673793070540380225425763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79565057427387173633901017 59673793070540380225425763)
      ·
        refine ⟨89510689605810570338138645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59673793070540380225425763 89510689605810570338138645)
        ·
          refine ⟨4195813575272370484600249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 89510689605810570338138645 4195813575272370484600249)
          ·
            refine ⟨3146860181454277863450187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4195813575272370484600249 3146860181454277863450187)
            ·
              refine ⟨4720290272181416795175281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3146860181454277863450187 4720290272181416795175281)
              ·
                refine ⟨3540217704136062596381461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4720290272181416795175281 3540217704136062596381461)
                ·
                  refine ⟨165947704881377934205381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3540217704136062596381461 165947704881377934205381)
                  ·
                    rfl

theorem cell22_1454319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 6].length) (baseStart_1454319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1454319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1454319 prefixEnd_1454319 := by exact prefixLift 1454319
  have htrace : WordTrace (prefixWord ++ tailWord_1454319) baseStart_1454319 baseEnd_1454319 := by
    simpa [prefixWord, tailWord_1454319, baseEnd_1454319] using wordTrace_append hprefix tailTrace_1454319
  have hstable : (prefixWord ++ tailWord_1454319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454319).length < 2 ^ (prefixWord ++ tailWord_1454319).sum := by decide
  have hdescent : baseEnd_1454319 < baseStart_1454319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454338 : List Nat := [3, 4, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_1454338 : Nat := 118140960795 + 1454338 * 2 ^ 59
def prefixEnd_1454338 : Nat := 4983230072969 + 3 ^ 40 * 1454338 * 2
def baseEnd_1454338 : Nat := 497849618732424086391085

theorem tailTrace_1454338 : CollatzResearch.WordTrace tailWord_1454338 prefixEnd_1454338 497849618732424086391085 := by
  unfold tailWord_1454338
  simp only [CollatzResearch.WordTrace]
  refine ⟨13261016151297320500218917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35362709736792854667250445 13261016151297320500218917)
  ·
    refine ⟨2486440528368247593791047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13261016151297320500218917 2486440528368247593791047)
    ·
      refine ⟨3729660792552371390686571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2486440528368247593791047 3729660792552371390686571)
      ·
        refine ⟨5594491188828557086029857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3729660792552371390686571 5594491188828557086029857)
        ·
          refine ⟨4195868391621417814522393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5594491188828557086029857 4195868391621417814522393)
          ·
            refine ⟨3146901293716063360891795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4195868391621417814522393 3146901293716063360891795)
            ·
              refine ⟨4720351940574095041337693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3146901293716063360891795 4720351940574095041337693)
              ·
                refine ⟨1770131977715285640501635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4720351940574095041337693 1770131977715285640501635)
                ·
                  refine ⟨2655197966572928460752453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1770131977715285640501635 2655197966572928460752453)
                  ·
                    refine ⟨497849618732424086391085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2655197966572928460752453 497849618732424086391085)
                    ·
                      rfl

theorem cell22_1454338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_1454338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1454338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1454338 prefixEnd_1454338 := by exact prefixLift 1454338
  have htrace : WordTrace (prefixWord ++ tailWord_1454338) baseStart_1454338 baseEnd_1454338 := by
    simpa [prefixWord, tailWord_1454338, baseEnd_1454338] using wordTrace_append hprefix tailTrace_1454338
  have hstable : (prefixWord ++ tailWord_1454338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454338).length < 2 ^ (prefixWord ++ tailWord_1454338).sum := by decide
  have hdescent : baseEnd_1454338 < baseStart_1454338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454347 : List Nat := [1, 1, 1, 1, 5, 2, 11]
def baseStart_1454347 : Nat := 118140960795 + 1454347 * 2 ^ 59
def prefixEnd_1454347 : Nat := 4983230072969 + 3 ^ 40 * 1454347 * 2
def baseEnd_1454347 : Nat := 18438988874679668996891

theorem tailTrace_1454347 : CollatzResearch.WordTrace tailWord_1454347 prefixEnd_1454347 18438988874679668996891 := by
  unfold tailWord_1454347
  simp only [CollatzResearch.WordTrace]
  refine ⟨53044392862156676537953295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35362928574771117691968863 53044392862156676537953295)
  ·
    refine ⟨79566589293235014806929943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53044392862156676537953295 79566589293235014806929943)
    ·
      refine ⟨119349883939852522210394915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79566589293235014806929943 119349883939852522210394915)
      ·
        refine ⟨179024825909778783315592373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119349883939852522210394915 179024825909778783315592373)
        ·
          refine ⟨16783577429041760935836785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 179024825909778783315592373 16783577429041760935836785)
          ·
            refine ⟨12587683071781320701877589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16783577429041760935836785 12587683071781320701877589)
            ·
              refine ⟨18438988874679668996891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 12587683071781320701877589 18438988874679668996891)
              ·
                rfl

theorem cell22_1454347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 11].length) (baseStart_1454347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1454347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1454347 prefixEnd_1454347 := by exact prefixLift 1454347
  have htrace : WordTrace (prefixWord ++ tailWord_1454347) baseStart_1454347 baseEnd_1454347 := by
    simpa [prefixWord, tailWord_1454347, baseEnd_1454347] using wordTrace_append hprefix tailTrace_1454347
  have hstable : (prefixWord ++ tailWord_1454347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454347).length < 2 ^ (prefixWord ++ tailWord_1454347).sum := by decide
  have hdescent : baseEnd_1454347 < baseStart_1454347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454409 : List Nat := [1, 2, 1, 1, 2, 3, 1, 6, 5]
def baseStart_1454409 : Nat := 118140960795 + 1454409 * 2 ^ 59
def prefixEnd_1454409 : Nat := 4983230072969 + 3 ^ 40 * 1454409 * 2
def baseEnd_1454409 : Nat := 165957974494467855955289

theorem tailTrace_1454409 : CollatzResearch.WordTrace tailWord_1454409 prefixEnd_1454409 165957974494467855955289 := by
  unfold tailWord_1454409
  simp only [CollatzResearch.WordTrace]
  refine ⟨53046654187932061126710281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35364436125288040751140187 53046654187932061126710281)
  ·
    refine ⟨39784990640949045845032711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53046654187932061126710281 39784990640949045845032711)
    ·
      refine ⟨59677485961423568767549067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39784990640949045845032711 59677485961423568767549067)
      ·
        refine ⟨89516228942135353151323601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59677485961423568767549067 89516228942135353151323601)
        ·
          refine ⟨67137171706601514863492701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89516228942135353151323601 67137171706601514863492701)
          ·
            refine ⟨25176439389975568073809763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67137171706601514863492701 25176439389975568073809763)
            ·
              refine ⟨37764659084963352110714645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25176439389975568073809763 37764659084963352110714645)
              ·
                refine ⟨1770218394607657130189749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37764659084963352110714645 1770218394607657130189749)
                ·
                  refine ⟨165957974494467855955289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1770218394607657130189749 165957974494467855955289)
                  ·
                    rfl

theorem cell22_1454409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 5].length) (baseStart_1454409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1454409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1454409 prefixEnd_1454409 := by exact prefixLift 1454409
  have htrace : WordTrace (prefixWord ++ tailWord_1454409) baseStart_1454409 baseEnd_1454409 := by
    simpa [prefixWord, tailWord_1454409, baseEnd_1454409] using wordTrace_append hprefix tailTrace_1454409
  have hstable : (prefixWord ++ tailWord_1454409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454409).length < 2 ^ (prefixWord ++ tailWord_1454409).sum := by decide
  have hdescent : baseEnd_1454409 < baseStart_1454409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454469 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 5, 5]
def baseStart_1454469 : Nat := 118140960795 + 1454469 * 2 ^ 59
def prefixEnd_1454469 : Nat := 4983230072969 + 3 ^ 40 * 1454469 * 2
def baseEnd_1454469 : Nat := 497894462709583411365683

theorem tailTrace_1454469 : CollatzResearch.WordTrace tailWord_1454469 prefixEnd_1454469 497894462709583411365683 := by
  unfold tailWord_1454469
  simp only [CollatzResearch.WordTrace]
  refine ⟨53048842567714691373894461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35365895045143127582596307 53048842567714691373894461)
  ·
    refine ⟨19893315962893009265210423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53048842567714691373894461 19893315962893009265210423)
    ·
      refine ⟨29839973944339513897815635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19893315962893009265210423 29839973944339513897815635)
      ·
        refine ⟨44759960916509270846723453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29839973944339513897815635 44759960916509270846723453)
        ·
          refine ⟨16784985343690976567521295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44759960916509270846723453 16784985343690976567521295)
          ·
            refine ⟨25177478015536464851281943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16784985343690976567521295 25177478015536464851281943)
            ·
              refine ⟨37766217023304697276922915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25177478015536464851281943 37766217023304697276922915)
              ·
                refine ⟨56649325534957045915384373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37766217023304697276922915 56649325534957045915384373)
                ·
                  refine ⟨5310874268902223054567285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56649325534957045915384373 5310874268902223054567285)
                  ·
                    refine ⟨497894462709583411365683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5310874268902223054567285 497894462709583411365683)
                    ·
                      rfl

theorem cell22_1454469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_1454469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1454469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1454469 prefixEnd_1454469 := by exact prefixLift 1454469
  have htrace : WordTrace (prefixWord ++ tailWord_1454469) baseStart_1454469 baseEnd_1454469 := by
    simpa [prefixWord, tailWord_1454469, baseEnd_1454469] using wordTrace_append hprefix tailTrace_1454469
  have hstable : (prefixWord ++ tailWord_1454469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454469).length < 2 ^ (prefixWord ++ tailWord_1454469).sum := by decide
  have hdescent : baseEnd_1454469 < baseStart_1454469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454544 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 11]
def baseStart_1454544 : Nat := 118140960795 + 1454544 * 2 ^ 59
def prefixEnd_1454544 : Nat := 4983230072969 + 3 ^ 40 * 1454544 * 2
def baseEnd_1454544 : Nat := 165973378914102738580151

theorem tailTrace_1454544 : CollatzResearch.WordTrace tailWord_1454544 prefixEnd_1454544 165973378914102738580151 := by
  unfold tailWord_1454544
  simp only [CollatzResearch.WordTrace]
  refine ⟨26525789021221489591437343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35367718694961986121916457 26525789021221489591437343)
  ·
    refine ⟨39788683531832234387156015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26525789021221489591437343 39788683531832234387156015)
    ·
      refine ⟨59683025297748351580734023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39788683531832234387156015 59683025297748351580734023)
      ·
        refine ⟨89524537946622527371101035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59683025297748351580734023 89524537946622527371101035)
        ·
          refine ⟨134286806919933791056651553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89524537946622527371101035 134286806919933791056651553)
          ·
            refine ⟨100715105189950343292488665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134286806919933791056651553 100715105189950343292488665)
            ·
              refine ⟨75536328892462757469366499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100715105189950343292488665 75536328892462757469366499)
              ·
                refine ⟨113304493338694136204049749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75536328892462757469366499 113304493338694136204049749)
                ·
                  refine ⟨165973378914102738580151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 113304493338694136204049749 165973378914102738580151)
                  ·
                    rfl

theorem cell22_1454544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 11].length) (baseStart_1454544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1454544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1454544 prefixEnd_1454544 := by exact prefixLift 1454544
  have htrace : WordTrace (prefixWord ++ tailWord_1454544) baseStart_1454544 baseEnd_1454544 := by
    simpa [prefixWord, tailWord_1454544, baseEnd_1454544] using wordTrace_append hprefix tailTrace_1454544
  have hstable : (prefixWord ++ tailWord_1454544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454544).length < 2 ^ (prefixWord ++ tailWord_1454544).sum := by decide
  have hdescent : baseEnd_1454544 < baseStart_1454544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454591 : List Nat := [1, 1, 2, 2, 1, 2, 4, 2, 3, 4]
def baseStart_1454591 : Nat := 118140960795 + 1454591 * 2 ^ 59
def prefixEnd_1454591 : Nat := 4983230072969 + 3 ^ 40 * 1454591 * 2
def baseEnd_1454591 : Nat := 497936225802815759815309

theorem tailTrace_1454591 : CollatzResearch.WordTrace tailWord_1454591 prefixEnd_1454591 497936225802815759815309 := by
  unfold tailWord_1454591
  simp only [CollatzResearch.WordTrace]
  refine ⟨53053292273272706209835627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35368861515515137473223751 53053292273272706209835627)
  ·
    refine ⟨79579938409909059314753441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53053292273272706209835627 79579938409909059314753441)
    ·
      refine ⟨59684953807431794486065081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79579938409909059314753441 59684953807431794486065081)
      ·
        refine ⟨44763715355573845864548811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59684953807431794486065081 44763715355573845864548811)
        ·
          refine ⟨67145573033360768796823217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44763715355573845864548811 67145573033360768796823217)
          ·
            refine ⟨50359179775020576597617413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67145573033360768796823217 50359179775020576597617413)
            ·
              refine ⟨9442346207816358112053265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50359179775020576597617413 9442346207816358112053265)
              ·
                refine ⟨7081759655862268584039949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9442346207816358112053265 7081759655862268584039949)
                ·
                  refine ⟨2655659870948350719014981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7081759655862268584039949 2655659870948350719014981)
                  ·
                    refine ⟨497936225802815759815309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2655659870948350719014981 497936225802815759815309)
                    ·
                      rfl

theorem cell22_1454591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 4].length) (baseStart_1454591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1454591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1454591 prefixEnd_1454591 := by exact prefixLift 1454591
  have htrace : WordTrace (prefixWord ++ tailWord_1454591) baseStart_1454591 baseEnd_1454591 := by
    simpa [prefixWord, tailWord_1454591, baseEnd_1454591] using wordTrace_append hprefix tailTrace_1454591
  have hstable : (prefixWord ++ tailWord_1454591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454591).length < 2 ^ (prefixWord ++ tailWord_1454591).sum := by decide
  have hdescent : baseEnd_1454591 < baseStart_1454591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454623 : List Nat := [1, 1, 2, 4, 1, 1, 1, 7, 4]
def baseStart_1454623 : Nat := 118140960795 + 1454623 * 2 ^ 59
def prefixEnd_1454623 : Nat := 4983230072969 + 3 ^ 40 * 1454623 * 2
def baseEnd_1454623 : Nat := 165982393352259447671737

theorem tailTrace_1454623 : CollatzResearch.WordTrace tailWord_1454623 prefixEnd_1454623 165982393352259447671737 := by
  unfold tailWord_1454623
  simp only [CollatzResearch.WordTrace]
  refine ⟨53054459409156775675000523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35369639606104517116667015 53054459409156775675000523)
  ·
    refine ⟨79581689113735163512500785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53054459409156775675000523 79581689113735163512500785)
    ·
      refine ⟨59686266835301372634375589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79581689113735163512500785 59686266835301372634375589)
      ·
        refine ⟨11191175031619007368945423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59686266835301372634375589 11191175031619007368945423)
        ·
          refine ⟨16786762547428511053418135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11191175031619007368945423 16786762547428511053418135)
          ·
            refine ⟨25180143821142766580127203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16786762547428511053418135 25180143821142766580127203)
            ·
              refine ⟨37770215731714149870190805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25180143821142766580127203 37770215731714149870190805)
              ·
                refine ⟨885239431212050387582597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 37770215731714149870190805 885239431212050387582597)
                ·
                  refine ⟨165982393352259447671737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 885239431212050387582597 165982393352259447671737)
                  ·
                    rfl

theorem cell22_1454623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7, 4].length) (baseStart_1454623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1454623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1454623 prefixEnd_1454623 := by exact prefixLift 1454623
  have htrace : WordTrace (prefixWord ++ tailWord_1454623) baseStart_1454623 baseEnd_1454623 := by
    simpa [prefixWord, tailWord_1454623, baseEnd_1454623] using wordTrace_append hprefix tailTrace_1454623
  have hstable : (prefixWord ++ tailWord_1454623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454623).length < 2 ^ (prefixWord ++ tailWord_1454623).sum := by decide
  have hdescent : baseEnd_1454623 < baseStart_1454623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454625 : List Nat := [1, 2, 3, 2, 2, 1, 5, 1, 1, 4]
def baseStart_1454625 : Nat := 118140960795 + 1454625 * 2 ^ 59
def prefixEnd_1454625 : Nat := 4983230072969 + 3 ^ 40 * 1454625 * 2
def baseEnd_1454625 : Nat := 497947864697651004465205

theorem tailTrace_1454625 : CollatzResearch.WordTrace tailWord_1454625 prefixEnd_1454625 497947864697651004465205 := by
  unfold tailWord_1454625
  simp only [CollatzResearch.WordTrace]
  refine ⟨53054532355149530016573329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35369688236766353344382219 53054532355149530016573329)
  ·
    refine ⟨39790899266362147512429997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53054532355149530016573329 39790899266362147512429997)
    ·
      refine ⟨14921587224885805317161249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39790899266362147512429997 14921587224885805317161249)
      ·
        refine ⟨11191190418664353987870937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14921587224885805317161249 11191190418664353987870937)
        ·
          refine ⟨8393392813998265490903203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11191190418664353987870937 8393392813998265490903203)
          ·
            refine ⟨12590089220997398236354805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8393392813998265490903203 12590089220997398236354805)
            ·
              refine ⟨1180320864468506084658263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12590089220997398236354805 1180320864468506084658263)
              ·
                refine ⟨1770481296702759126987395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1180320864468506084658263 1770481296702759126987395)
                ·
                  refine ⟨2655721945054138690481093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1770481296702759126987395 2655721945054138690481093)
                  ·
                    refine ⟨497947864697651004465205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2655721945054138690481093 497947864697651004465205)
                    ·
                      rfl

theorem cell22_1454625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_1454625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1454625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1454625 prefixEnd_1454625 := by exact prefixLift 1454625
  have htrace : WordTrace (prefixWord ++ tailWord_1454625) baseStart_1454625 baseEnd_1454625 := by
    simpa [prefixWord, tailWord_1454625, baseEnd_1454625] using wordTrace_append hprefix tailTrace_1454625
  have hstable : (prefixWord ++ tailWord_1454625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454625).length < 2 ^ (prefixWord ++ tailWord_1454625).sum := by decide
  have hdescent : baseEnd_1454625 < baseStart_1454625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454640 : List Nat := [2, 1, 1, 1, 2, 3, 6, 2, 4]
def baseStart_1454640 : Nat := 118140960795 + 1454640 * 2 ^ 59
def prefixEnd_1454640 : Nat := 4983230072969 + 3 ^ 40 * 1454640 * 2
def baseEnd_1454640 : Nat := 165984333168065321780053

theorem tailTrace_1454640 : CollatzResearch.WordTrace tailWord_1454640 prefixEnd_1454640 165984333168065321780053 := by
  unfold tailWord_1454640
  simp only [CollatzResearch.WordTrace]
  refine ⟨26527539725047593789184687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35370052966730125052246249 26527539725047593789184687)
  ·
    refine ⟨39791309587571390683777031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26527539725047593789184687 39791309587571390683777031)
    ·
      refine ⟨59686964381357086025665547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39791309587571390683777031 59686964381357086025665547)
      ·
        refine ⟨89530446572035629038498321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59686964381357086025665547 89530446572035629038498321)
        ·
          refine ⟨67147834929026721778873741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89530446572035629038498321 67147834929026721778873741)
          ·
            refine ⟨25180438098385020667077653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67147834929026721778873741 25180438098385020667077653)
            ·
              refine ⟨1180333035861797843769265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25180438098385020667077653 1180333035861797843769265)
              ·
                refine ⟨885249776896348382826949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1180333035861797843769265 885249776896348382826949)
                ·
                  refine ⟨165984333168065321780053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 885249776896348382826949 165984333168065321780053)
                  ·
                    rfl

theorem cell22_1454640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2, 4].length) (baseStart_1454640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1454640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1454640 prefixEnd_1454640 := by exact prefixLift 1454640
  have htrace : WordTrace (prefixWord ++ tailWord_1454640) baseStart_1454640 baseEnd_1454640 := by
    simpa [prefixWord, tailWord_1454640, baseEnd_1454640] using wordTrace_append hprefix tailTrace_1454640
  have hstable : (prefixWord ++ tailWord_1454640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454640).length < 2 ^ (prefixWord ++ tailWord_1454640).sum := by decide
  have hdescent : baseEnd_1454640 < baseStart_1454640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454668 : List Nat := [2, 2, 1, 3, 1, 2, 5, 6]
def baseStart_1454668 : Nat := 118140960795 + 1454668 * 2 ^ 59
def prefixEnd_1454668 : Nat := 4983230072969 + 3 ^ 40 * 1454668 * 2
def baseEnd_1454668 : Nat := 55329176052934802848897

theorem tailTrace_1454668 : CollatzResearch.WordTrace tailWord_1454668 prefixEnd_1454668 55329176052934802848897 := by
  unfold tailWord_1454668
  simp only [CollatzResearch.WordTrace]
  refine ⟨26528050346996874180194329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35370733795995832240259105 26528050346996874180194329)
  ·
    refine ⟨19896037760247655635145747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26528050346996874180194329 19896037760247655635145747)
    ·
      refine ⟨29844056640371483452718621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19896037760247655635145747 29844056640371483452718621)
      ·
        refine ⟨11191521240139306294769483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29844056640371483452718621 11191521240139306294769483)
        ·
          refine ⟨16787281860208959442154225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11191521240139306294769483 16787281860208959442154225)
          ·
            refine ⟨12590461395156719581615669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16787281860208959442154225 12590461395156719581615669)
            ·
              refine ⟨1180355755795942460776469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12590461395156719581615669 1180355755795942460776469)
              ·
                refine ⟨55329176052934802848897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1180355755795942460776469 55329176052934802848897)
                ·
                  rfl

theorem cell22_1454668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 6].length) (baseStart_1454668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1454668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1454668 prefixEnd_1454668 := by exact prefixLift 1454668
  have htrace : WordTrace (prefixWord ++ tailWord_1454668) baseStart_1454668 baseEnd_1454668 := by
    simpa [prefixWord, tailWord_1454668, baseEnd_1454668] using wordTrace_append hprefix tailTrace_1454668
  have hstable : (prefixWord ++ tailWord_1454668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454668).length < 2 ^ (prefixWord ++ tailWord_1454668).sum := by decide
  have hdescent : baseEnd_1454668 < baseStart_1454668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454807 : List Nat := [1, 1, 3, 2, 1, 5, 2, 2, 2, 3]
def baseStart_1454807 : Nat := 118140960795 + 1454807 * 2 ^ 59
def prefixEnd_1454807 : Nat := 4983230072969 + 3 ^ 40 * 1454807 * 2
def baseEnd_1454807 : Nat := 498010167017063196414647

theorem tailTrace_1454807 : CollatzResearch.WordTrace tailWord_1454807 prefixEnd_1454807 498010167017063196414647 := by
  unfold tailWord_1454807
  simp only [CollatzResearch.WordTrace]
  refine ⟨53061170440490175099698675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35374113626993450066465783 53061170440490175099698675)
  ·
    refine ⟨79591755660735262649548013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53061170440490175099698675 79591755660735262649548013)
    ·
      refine ⟨29846908372775723493580505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79591755660735262649548013 29846908372775723493580505)
      ·
        refine ⟨22385181279581792620185379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29846908372775723493580505 22385181279581792620185379)
        ·
          refine ⟨33577771919372688930278069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22385181279581792620185379 33577771919372688930278069)
          ·
            refine ⟨3147916117441189587213569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33577771919372688930278069 3147916117441189587213569)
            ·
              refine ⟨2360937088080892190410177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3147916117441189587213569 2360937088080892190410177)
              ·
                refine ⟨1770702816060669142807633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2360937088080892190410177 1770702816060669142807633)
                ·
                  refine ⟨1328027112045501857105725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1770702816060669142807633 1328027112045501857105725)
                  ·
                    refine ⟨498010167017063196414647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1328027112045501857105725 498010167017063196414647)
                    ·
                      rfl

theorem cell22_1454807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2, 3].length) (baseStart_1454807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1454807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1454807 prefixEnd_1454807 := by exact prefixLift 1454807
  have htrace : WordTrace (prefixWord ++ tailWord_1454807) baseStart_1454807 baseEnd_1454807 := by
    simpa [prefixWord, tailWord_1454807, baseEnd_1454807] using wordTrace_append hprefix tailTrace_1454807
  have hstable : (prefixWord ++ tailWord_1454807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454807).length < 2 ^ (prefixWord ++ tailWord_1454807).sum := by decide
  have hdescent : baseEnd_1454807 < baseStart_1454807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454820 : List Nat := [2, 3, 1, 1, 1, 6, 1, 7]
def baseStart_1454820 : Nat := 118140960795 + 1454820 * 2 ^ 59
def prefixEnd_1454820 : Nat := 4983230072969 + 3 ^ 40 * 1454820 * 2
def baseEnd_1454820 : Nat := 55334957464748388426623

theorem tailTrace_1454820 : CollatzResearch.WordTrace tailWord_1454820 prefixEnd_1454820 55334957464748388426623 := by
  unfold tailWord_1454820
  simp only [CollatzResearch.WordTrace]
  refine ⟨26530822294721539159960957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35374429726295385546614609 26530822294721539159960957)
  ·
    refine ⟨9949058360520577184985359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26530822294721539159960957 9949058360520577184985359)
    ·
      refine ⟨14923587540780865777478039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9949058360520577184985359 14923587540780865777478039)
      ·
        refine ⟨22385381311171298666217059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14923587540780865777478039 22385381311171298666217059)
        ·
          refine ⟨33578071966756947999325589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22385381311171298666217059 33578071966756947999325589)
          ·
            refine ⟨1573972123441731937468387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33578071966756947999325589 1573972123441731937468387)
            ·
              refine ⟨2360958185162597906202581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1573972123441731937468387 2360958185162597906202581)
              ·
                refine ⟨55334957464748388426623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2360958185162597906202581 55334957464748388426623)
                ·
                  rfl

theorem cell22_1454820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 7].length) (baseStart_1454820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1454820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1454820 prefixEnd_1454820 := by exact prefixLift 1454820
  have htrace : WordTrace (prefixWord ++ tailWord_1454820) baseStart_1454820 baseEnd_1454820 := by
    simpa [prefixWord, tailWord_1454820, baseEnd_1454820] using wordTrace_append hprefix tailTrace_1454820
  have hstable : (prefixWord ++ tailWord_1454820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454820).length < 2 ^ (prefixWord ++ tailWord_1454820).sum := by decide
  have hdescent : baseEnd_1454820 < baseStart_1454820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454833 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 2, 6]
def baseStart_1454833 : Nat := 118140960795 + 1454833 * 2 ^ 59
def prefixEnd_1454833 : Nat := 4983230072969 + 3 ^ 40 * 1454833 * 2
def baseEnd_1454833 : Nat := 498019067348407795264567

theorem tailTrace_1454833 : CollatzResearch.WordTrace tailWord_1454833 prefixEnd_1454833 498019067348407795264567 := by
  unfold tailWord_1454833
  simp only [CollatzResearch.WordTrace]
  refine ⟨53062118738395981540145153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35374745825597321026763435 53062118738395981540145153)
  ·
    refine ⟨39796589053796986155108865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53062118738395981540145153 39796589053796986155108865)
    ·
      refine ⟨29847441790347739616331649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39796589053796986155108865 29847441790347739616331649)
      ·
        refine ⟨22385581342760804712248737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29847441790347739616331649 22385581342760804712248737)
        ·
          refine ⟨16789186007070603534186553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22385581342760804712248737 16789186007070603534186553)
          ·
            refine ⟨12591889505302952650639915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16789186007070603534186553 12591889505302952650639915)
            ·
              refine ⟨18887834257954428975959873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12591889505302952650639915 18887834257954428975959873)
              ·
                refine ⟨14165875693465821731969905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18887834257954428975959873 14165875693465821731969905)
                ·
                  refine ⟨10624406770099366298977429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14165875693465821731969905 10624406770099366298977429)
                  ·
                    refine ⟨498019067348407795264567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10624406770099366298977429 498019067348407795264567)
                    ·
                      rfl

theorem cell22_1454833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_1454833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1454833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1454833 prefixEnd_1454833 := by exact prefixLift 1454833
  have htrace : WordTrace (prefixWord ++ tailWord_1454833) baseStart_1454833 baseEnd_1454833 := by
    simpa [prefixWord, tailWord_1454833, baseEnd_1454833] using wordTrace_append hprefix tailTrace_1454833
  have hstable : (prefixWord ++ tailWord_1454833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454833).length < 2 ^ (prefixWord ++ tailWord_1454833).sum := by decide
  have hdescent : baseEnd_1454833 < baseStart_1454833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454863 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 4, 5]
def baseStart_1454863 : Nat := 118140960795 + 1454863 * 2 ^ 59
def prefixEnd_1454863 : Nat := 4983230072969 + 3 ^ 40 * 1454863 * 2
def baseEnd_1454863 : Nat := 498029336961497717014475

theorem tailTrace_1454863 : CollatzResearch.WordTrace tailWord_1454863 prefixEnd_1454863 498029336961497717014475 := by
  unfold tailWord_1454863
  simp only [CollatzResearch.WordTrace]
  refine ⟨53063212928287296663737243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35375475285524864442491495 53063212928287296663737243)
  ·
    refine ⟨79594819392430944995605865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53063212928287296663737243 79594819392430944995605865)
    ·
      refine ⟨59696114544323208746704399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79594819392430944995605865 59696114544323208746704399)
      ·
        refine ⟨89544171816484813120056599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59696114544323208746704399 89544171816484813120056599)
        ·
          refine ⟨134316257724727219680084899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89544171816484813120056599 134316257724727219680084899)
          ·
            refine ⟨201474386587090829520127349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134316257724727219680084899 201474386587090829520127349)
            ·
              refine ⟨18888223742539765267511939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 201474386587090829520127349 18888223742539765267511939)
              ·
                refine ⟨28332335613809647901267909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18888223742539765267511939 28332335613809647901267909)
                ·
                  refine ⟨5312312927589308981487733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28332335613809647901267909 5312312927589308981487733)
                  ·
                    refine ⟨498029336961497717014475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5312312927589308981487733 498029336961497717014475)
                    ·
                      rfl

theorem cell22_1454863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 5].length) (baseStart_1454863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1454863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1454863 prefixEnd_1454863 := by exact prefixLift 1454863
  have htrace : WordTrace (prefixWord ++ tailWord_1454863) baseStart_1454863 baseEnd_1454863 := by
    simpa [prefixWord, tailWord_1454863, baseEnd_1454863] using wordTrace_append hprefix tailTrace_1454863
  have hstable : (prefixWord ++ tailWord_1454863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454863).length < 2 ^ (prefixWord ++ tailWord_1454863).sum := by decide
  have hdescent : baseEnd_1454863 < baseStart_1454863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454865 : List Nat := [1, 2, 2, 1, 1, 3, 5, 2, 5]
def baseStart_1454865 : Nat := 118140960795 + 1454865 * 2 ^ 59
def prefixEnd_1454865 : Nat := 4983230072969 + 3 ^ 40 * 1454865 * 2
def baseEnd_1454865 : Nat := 166010007200790126154823

theorem tailTrace_1454865 : CollatzResearch.WordTrace tailWord_1454865 prefixEnd_1454865 166010007200790126154823 := by
  unfold tailWord_1454865
  simp only [CollatzResearch.WordTrace]
  refine ⟨53063285874280051005310049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35375523916186700670206699 53063285874280051005310049)
  ·
    refine ⟨39797464405710038253982537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53063285874280051005310049 39797464405710038253982537)
    ·
      refine ⟨29848098304282528690486903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39797464405710038253982537 29848098304282528690486903)
      ·
        refine ⟨44772147456423793035730355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29848098304282528690486903 44772147456423793035730355)
        ·
          refine ⟨67158221184635689553595533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44772147456423793035730355 67158221184635689553595533)
          ·
            refine ⟨25184332944238383582598325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67158221184635689553595533 25184332944238383582598325)
            ·
              refine ⟨2361031213522348460868593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25184332944238383582598325 2361031213522348460868593)
              ·
                refine ⟨1770773410141761345651445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2361031213522348460868593 1770773410141761345651445)
                ·
                  refine ⟨166010007200790126154823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1770773410141761345651445 166010007200790126154823)
                  ·
                    rfl

theorem cell22_1454865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 5].length) (baseStart_1454865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1454865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1454865 prefixEnd_1454865 := by exact prefixLift 1454865
  have htrace : WordTrace (prefixWord ++ tailWord_1454865) baseStart_1454865 baseEnd_1454865 := by
    simpa [prefixWord, tailWord_1454865, baseEnd_1454865] using wordTrace_append hprefix tailTrace_1454865
  have hstable : (prefixWord ++ tailWord_1454865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454865).length < 2 ^ (prefixWord ++ tailWord_1454865).sum := by decide
  have hdescent : baseEnd_1454865 < baseStart_1454865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454880 : List Nat := [2, 1, 1, 5, 1, 2, 2, 1, 2, 5]
def baseStart_1454880 : Nat := 118140960795 + 1454880 * 2 ^ 59
def prefixEnd_1454880 : Nat := 4983230072969 + 3 ^ 40 * 1454880 * 2
def baseEnd_1454880 : Nat := 498035156408915339339423

theorem tailTrace_1454880 : CollatzResearch.WordTrace tailWord_1454880 prefixEnd_1454880 498035156408915339339423 := by
  unfold tailWord_1454880
  simp only [CollatzResearch.WordTrace]
  refine ⟨26531916484612854283553047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35375888646150472378070729 26531916484612854283553047)
  ·
    refine ⟨39797874726919281425329571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26531916484612854283553047 39797874726919281425329571)
    ·
      refine ⟨59696812090378922137994357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39797874726919281425329571 59696812090378922137994357)
      ·
        refine ⟨5596576133473023950436971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59696812090378922137994357 5596576133473023950436971)
        ·
          refine ⟨8394864200209535925655457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5596576133473023950436971 8394864200209535925655457)
          ·
            refine ⟨6296148150157151944241593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8394864200209535925655457 6296148150157151944241593)
            ·
              refine ⟨4722111112617863958181195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6296148150157151944241593 4722111112617863958181195)
              ·
                refine ⟨7083166668926795937271793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4722111112617863958181195 7083166668926795937271793)
                ·
                  refine ⟨5312375001695096952953845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7083166668926795937271793 5312375001695096952953845)
                  ·
                    refine ⟨498035156408915339339423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5312375001695096952953845 498035156408915339339423)
                    ·
                      rfl

theorem cell22_1454880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 2, 5].length) (baseStart_1454880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1454880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1454880 prefixEnd_1454880 := by exact prefixLift 1454880
  have htrace : WordTrace (prefixWord ++ tailWord_1454880) baseStart_1454880 baseEnd_1454880 := by
    simpa [prefixWord, tailWord_1454880, baseEnd_1454880] using wordTrace_append hprefix tailTrace_1454880
  have hstable : (prefixWord ++ tailWord_1454880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454880).length < 2 ^ (prefixWord ++ tailWord_1454880).sum := by decide
  have hdescent : baseEnd_1454880 < baseStart_1454880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454923 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 2, 10]
def baseStart_1454923 : Nat := 118140960795 + 1454923 * 2 ^ 59
def prefixEnd_1454923 : Nat := 4983230072969 + 3 ^ 40 * 1454923 * 2
def baseEnd_1454923 : Nat := 498049876187677560514291

theorem tailTrace_1454923 : CollatzResearch.WordTrace tailWord_1454923 prefixEnd_1454923 498049876187677560514291 := by
  unfold tailWord_1454923
  simp only [CollatzResearch.WordTrace]
  refine ⟨53065401308069926910921423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35376934205379951273947615 53065401308069926910921423)
  ·
    refine ⟨79598101962104890366382135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53065401308069926910921423 79598101962104890366382135)
    ·
      refine ⟨119397152943157335549573203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79598101962104890366382135 119397152943157335549573203)
      ·
        refine ⟨179095729414736003324359805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119397152943157335549573203 179095729414736003324359805)
        ·
          refine ⟨67160898530526001246634927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179095729414736003324359805 67160898530526001246634927)
          ·
            refine ⟨100741347795789001869952391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67160898530526001246634927 100741347795789001869952391)
            ·
              refine ⟨151112021693683502804928587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100741347795789001869952391 151112021693683502804928587)
              ·
                refine ⟨226668032540525254207392881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151112021693683502804928587 226668032540525254207392881)
                ·
                  refine ⟨170001024405393940655544661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226668032540525254207392881 170001024405393940655544661)
                  ·
                    refine ⟨498049876187677560514291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 170001024405393940655544661 498049876187677560514291)
                    ·
                      rfl

theorem cell22_1454923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 10].length) (baseStart_1454923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1454923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1454923 prefixEnd_1454923 := by exact prefixLift 1454923
  have htrace : WordTrace (prefixWord ++ tailWord_1454923) baseStart_1454923 baseEnd_1454923 := by
    simpa [prefixWord, tailWord_1454923, baseEnd_1454923] using wordTrace_append hprefix tailTrace_1454923
  have hstable : (prefixWord ++ tailWord_1454923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454923).length < 2 ^ (prefixWord ++ tailWord_1454923).sum := by decide
  have hdescent : baseEnd_1454923 < baseStart_1454923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454946 : List Nat := [3, 3, 2, 1, 3, 2, 1, 2, 1, 4]
def baseStart_1454946 : Nat := 118140960795 + 1454946 * 2 ^ 59
def prefixEnd_1454946 : Nat := 4983230072969 + 3 ^ 40 * 1454946 * 2
def baseEnd_1454946 : Nat := 498057749557713167189221

theorem tailTrace_1454946 : CollatzResearch.WordTrace tailWord_1454946 prefixEnd_1454946 498057749557713167189221 := by
  unfold tailWord_1454946
  simp only [CollatzResearch.WordTrace]
  refine ⟨13266560046746650459752173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35377493457991067892672461 13266560046746650459752173)
  ·
    refine ⟨4974960017529993922407065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13266560046746650459752173 4974960017529993922407065)
    ·
      refine ⟨3731220013147495441805299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4974960017529993922407065 3731220013147495441805299)
      ·
        refine ⟨5596830019721243162707949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3731220013147495441805299 5596830019721243162707949)
        ·
          refine ⟨2098811257395466186015481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5596830019721243162707949 2098811257395466186015481)
          ·
            refine ⟨1574108443046599639511611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2098811257395466186015481 1574108443046599639511611)
            ·
              refine ⟨2361162664569899459267417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1574108443046599639511611 2361162664569899459267417)
              ·
                refine ⟨1770871998427424594450563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2361162664569899459267417 1770871998427424594450563)
                ·
                  refine ⟨2656307997641136891675845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1770871998427424594450563 2656307997641136891675845)
                  ·
                    refine ⟨498057749557713167189221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2656307997641136891675845 498057749557713167189221)
                    ·
                      rfl

theorem cell22_1454946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_1454946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1454946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1454946 prefixEnd_1454946 := by exact prefixLift 1454946
  have htrace : WordTrace (prefixWord ++ tailWord_1454946) baseStart_1454946 baseEnd_1454946 := by
    simpa [prefixWord, tailWord_1454946, baseEnd_1454946] using wordTrace_append hprefix tailTrace_1454946
  have hstable : (prefixWord ++ tailWord_1454946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454946).length < 2 ^ (prefixWord ++ tailWord_1454946).sum := by decide
  have hdescent : baseEnd_1454946 < baseStart_1454946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454978 : List Nat := [3, 4, 2, 2, 1, 1, 1, 4, 4]
def baseStart_1454978 : Nat := 118140960795 + 1454978 * 2 ^ 59
def prefixEnd_1454978 : Nat := 4983230072969 + 3 ^ 40 * 1454978 * 2
def baseEnd_1454978 : Nat := 166022901270558583463041

theorem tailTrace_1454978 : CollatzResearch.WordTrace tailWord_1454978 prefixEnd_1454978 166022901270558583463041 := by
  unfold tailWord_1454978
  simp only [CollatzResearch.WordTrace]
  refine ⟨13266851830717667826043397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35378271548580447536115725 13266851830717667826043397)
  ·
    refine ⟨2487534718259562717383137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13266851830717667826043397 2487534718259562717383137)
    ·
      refine ⟨1865651038694672038037353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2487534718259562717383137 1865651038694672038037353)
      ·
        refine ⟨1399238279021004028528015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1865651038694672038037353 1399238279021004028528015)
        ·
          refine ⟨2098857418531506042792023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1399238279021004028528015 2098857418531506042792023)
          ·
            refine ⟨3148286127797259064188035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2098857418531506042792023 3148286127797259064188035)
            ·
              refine ⟨4722429191695888596282053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3148286127797259064188035 4722429191695888596282053)
              ·
                refine ⟨885455473442979111802885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4722429191695888596282053 885455473442979111802885)
                ·
                  refine ⟨166022901270558583463041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 885455473442979111802885 166022901270558583463041)
                  ·
                    rfl

theorem cell22_1454978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_1454978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1454978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1454978 prefixEnd_1454978 := by exact prefixLift 1454978
  have htrace : WordTrace (prefixWord ++ tailWord_1454978) baseStart_1454978 baseEnd_1454978 := by
    simpa [prefixWord, tailWord_1454978, baseEnd_1454978] using wordTrace_append hprefix tailTrace_1454978
  have hstable : (prefixWord ++ tailWord_1454978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454978).length < 2 ^ (prefixWord ++ tailWord_1454978).sum := by decide
  have hdescent : baseEnd_1454978 < baseStart_1454978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454985 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 2, 6]
def baseStart_1454985 : Nat := 118140960795 + 1454985 * 2 ^ 59
def prefixEnd_1454985 : Nat := 4983230072969 + 3 ^ 40 * 1454985 * 2
def baseEnd_1454985 : Nat := 498071100054730065464101

theorem tailTrace_1454985 : CollatzResearch.WordTrace tailWord_1454985 prefixEnd_1454985 498071100054730065464101 := by
  unfold tailWord_1454985
  simp only [CollatzResearch.WordTrace]
  refine ⟨53067662633845311499678409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35378441755896874333118939 53067662633845311499678409)
  ·
    refine ⟨39800746975383983624758807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53067662633845311499678409 39800746975383983624758807)
    ·
      refine ⟨59701120463075975437138211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39800746975383983624758807 59701120463075975437138211)
      ·
        refine ⟨89551680694613963155707317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59701120463075975437138211 89551680694613963155707317)
        ·
          refine ⟨8395470065120059045847561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89551680694613963155707317 8395470065120059045847561)
          ·
            refine ⟨6296602548840044284385671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8395470065120059045847561 6296602548840044284385671)
            ·
              refine ⟨9444903823260066426578507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6296602548840044284385671 9444903823260066426578507)
              ·
                refine ⟨14167355734890099639867761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9444903823260066426578507 14167355734890099639867761)
                ·
                  refine ⟨10625516801167574729900821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14167355734890099639867761 10625516801167574729900821)
                  ·
                    refine ⟨498071100054730065464101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10625516801167574729900821 498071100054730065464101)
                    ·
                      rfl

theorem cell22_1454985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 6].length) (baseStart_1454985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1454985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1454985 prefixEnd_1454985 := by exact prefixLift 1454985
  have htrace : WordTrace (prefixWord ++ tailWord_1454985) baseStart_1454985 baseEnd_1454985 := by
    simpa [prefixWord, tailWord_1454985, baseEnd_1454985] using wordTrace_append hprefix tailTrace_1454985
  have hstable : (prefixWord ++ tailWord_1454985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454985).length < 2 ^ (prefixWord ++ tailWord_1454985).sum := by decide
  have hdescent : baseEnd_1454985 < baseStart_1454985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455064 : List Nat := [2, 1, 2, 2, 2, 4, 2, 2, 1, 4]
def baseStart_1455064 : Nat := 118140960795 + 1455064 * 2 ^ 59
def prefixEnd_1455064 : Nat := 4983230072969 + 3 ^ 40 * 1455064 * 2
def baseEnd_1455064 : Nat := 498098143369200192738859

theorem tailTrace_1455064 : CollatzResearch.WordTrace tailWord_1455064 prefixEnd_1455064 498098143369200192738859 := by
  unfold tailWord_1455064
  simp only [CollatzResearch.WordTrace]
  refine ⟨26535272000279553995902123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35380362667039405327869497 26535272000279553995902123)
  ·
    refine ⟨39802908000419330993853185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26535272000279553995902123 39802908000419330993853185)
    ·
      refine ⟨29852181000314498245389889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39802908000419330993853185 29852181000314498245389889)
      ·
        refine ⟨22389135750235873684042417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29852181000314498245389889 22389135750235873684042417)
        ·
          refine ⟨16791851812676905263031813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22389135750235873684042417 16791851812676905263031813)
          ·
            refine ⟨3148472214876919736818465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16791851812676905263031813 3148472214876919736818465)
            ·
              refine ⟨2361354161157689802613849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3148472214876919736818465 2361354161157689802613849)
              ·
                refine ⟨1771015620868267351960387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2361354161157689802613849 1771015620868267351960387)
                ·
                  refine ⟨2656523431302401027940581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1771015620868267351960387 2656523431302401027940581)
                  ·
                    refine ⟨498098143369200192738859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2656523431302401027940581 498098143369200192738859)
                    ·
                      rfl

theorem cell22_1455064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_1455064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1455064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1455064 prefixEnd_1455064 := by exact prefixLift 1455064
  have htrace : WordTrace (prefixWord ++ tailWord_1455064) baseStart_1455064 baseEnd_1455064 := by
    simpa [prefixWord, tailWord_1455064, baseEnd_1455064] using wordTrace_append hprefix tailTrace_1455064
  have hstable : (prefixWord ++ tailWord_1455064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455064).length < 2 ^ (prefixWord ++ tailWord_1455064).sum := by decide
  have hdescent : baseEnd_1455064 < baseStart_1455064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455199 : List Nat := [1, 1, 2, 3, 1, 1, 5, 3, 1, 4]
def baseStart_1455199 : Nat := 118140960795 + 1455199 * 2 ^ 59
def prefixEnd_1455199 : Nat := 4983230072969 + 3 ^ 40 * 1455199 * 2
def baseEnd_1455199 : Nat := 498144356628104840613445

theorem tailTrace_1455199 : CollatzResearch.WordTrace tailWord_1455199 prefixEnd_1455199 498144356628104840613445 := by
  unfold tailWord_1455199
  simp only [CollatzResearch.WordTrace]
  refine ⟨53075467855070026047968651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35383645236713350698645767 53075467855070026047968651)
  ·
    refine ⟨79613201782605039071952977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53075467855070026047968651 79613201782605039071952977)
    ·
      refine ⟨59709901336953779303964733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79613201782605039071952977 59709901336953779303964733)
      ·
        refine ⟨22391213001357667238986775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59709901336953779303964733 22391213001357667238986775)
        ·
          refine ⟨33586819502036500858480163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22391213001357667238986775 33586819502036500858480163)
          ·
            refine ⟨50380229253054751287720245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33586819502036500858480163 50380229253054751287720245)
            ·
              refine ⟨4723146492473882933223773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50380229253054751287720245 4723146492473882933223773)
              ·
                refine ⟨1771179934677706099958915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4723146492473882933223773 1771179934677706099958915)
                ·
                  refine ⟨2656769902016559149938373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1771179934677706099958915 2656769902016559149938373)
                  ·
                    refine ⟨498144356628104840613445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2656769902016559149938373 498144356628104840613445)
                    ·
                      rfl

theorem cell22_1455199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 4].length) (baseStart_1455199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1455199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1455199 prefixEnd_1455199 := by exact prefixLift 1455199
  have htrace : WordTrace (prefixWord ++ tailWord_1455199) baseStart_1455199 baseEnd_1455199 := by
    simpa [prefixWord, tailWord_1455199, baseEnd_1455199] using wordTrace_append hprefix tailTrace_1455199
  have hstable : (prefixWord ++ tailWord_1455199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455199).length < 2 ^ (prefixWord ++ tailWord_1455199).sum := by decide
  have hdescent : baseEnd_1455199 < baseStart_1455199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455214 : List Nat := [4, 1, 2, 2, 1, 2, 1, 3, 6]
def baseStart_1455214 : Nat := 118140960795 + 1455214 * 2 ^ 59
def prefixEnd_1455214 : Nat := 4983230072969 + 3 ^ 40 * 1455214 * 2
def baseEnd_1455214 : Nat := 166049830478216600496133

theorem tailTrace_1455214 : CollatzResearch.WordTrace tailWord_1455214 prefixEnd_1455214 166049830478216600496133 := by
  unfold tailWord_1455214
  simp only [CollatzResearch.WordTrace]
  refine ⟨6634501868751960451220587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35384009966677122406509797 6634501868751960451220587)
  ·
    refine ⟨9951752803127940676830881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6634501868751960451220587 9951752803127940676830881)
    ·
      refine ⟨7463814602345955507623161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9951752803127940676830881 7463814602345955507623161)
      ·
        refine ⟨5597860951759466630717371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7463814602345955507623161 5597860951759466630717371)
        ·
          refine ⟨8396791427639199946076057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5597860951759466630717371 8396791427639199946076057)
          ·
            refine ⟨6297593570729399959557043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8396791427639199946076057 6297593570729399959557043)
            ·
              refine ⟨9446390356094099939335565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6297593570729399959557043 9446390356094099939335565)
              ·
                refine ⟨3542396383535287477250837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9446390356094099939335565 3542396383535287477250837)
                ·
                  refine ⟨166049830478216600496133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3542396383535287477250837 166049830478216600496133)
                  ·
                    rfl

theorem cell22_1455214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_1455214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1455214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1455214 prefixEnd_1455214 := by exact prefixLift 1455214
  have htrace : WordTrace (prefixWord ++ tailWord_1455214) baseStart_1455214 baseEnd_1455214 := by
    simpa [prefixWord, tailWord_1455214, baseEnd_1455214] using wordTrace_append hprefix tailTrace_1455214
  have hstable : (prefixWord ++ tailWord_1455214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455214).length < 2 ^ (prefixWord ++ tailWord_1455214).sum := by decide
  have hdescent : baseEnd_1455214 < baseStart_1455214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455246 : List Nat := [4, 1, 1, 3, 2, 1, 1, 2, 4, 3]
def baseStart_1455246 : Nat := 118140960795 + 1455246 * 2 ^ 59
def prefixEnd_1455246 : Nat := 4983230072969 + 3 ^ 40 * 1455246 * 2
def baseEnd_1455246 : Nat := 498160445688612384688301

theorem tailTrace_1455246 : CollatzResearch.WordTrace tailWord_1455246 prefixEnd_1455246 498160445688612384688301 := by
  unfold tailWord_1455246
  simp only [CollatzResearch.WordTrace]
  refine ⟨6634647760737469134366199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35384788057266502049953061 6634647760737469134366199)
  ·
    refine ⟨9951971641106203701549299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6634647760737469134366199 9951971641106203701549299)
    ·
      refine ⟨14927957461659305552323949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9951971641106203701549299 14927957461659305552323949)
      ·
        refine ⟨5597984048122239582121481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14927957461659305552323949 5597984048122239582121481)
        ·
          refine ⟨4198488036091679686591111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5597984048122239582121481 4198488036091679686591111)
          ·
            refine ⟨6297732054137519529886667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4198488036091679686591111 6297732054137519529886667)
            ·
              refine ⟨9446598081206279294830001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6297732054137519529886667 9446598081206279294830001)
              ·
                refine ⟨7084948560904709471122501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9446598081206279294830001 7084948560904709471122501)
                ·
                  refine ⟨1328427855169633025835469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7084948560904709471122501 1328427855169633025835469)
                  ·
                    refine ⟨498160445688612384688301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1328427855169633025835469 498160445688612384688301)
                    ·
                      rfl

theorem cell22_1455246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_1455246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1455246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1455246 prefixEnd_1455246 := by exact prefixLift 1455246
  have htrace : WordTrace (prefixWord ++ tailWord_1455246) baseStart_1455246 baseEnd_1455246 := by
    simpa [prefixWord, tailWord_1455246, baseEnd_1455246] using wordTrace_append hprefix tailTrace_1455246
  have hstable : (prefixWord ++ tailWord_1455246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455246).length < 2 ^ (prefixWord ++ tailWord_1455246).sum := by decide
  have hdescent : baseEnd_1455246 < baseStart_1455246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455368 : List Nat := [2, 1, 3, 2, 4, 1, 1, 3, 1, 4]
def baseStart_1455368 : Nat := 118140960795 + 1455368 * 2 ^ 59
def prefixEnd_1455368 : Nat := 4983230072969 + 3 ^ 40 * 1455368 * 2
def baseEnd_1455368 : Nat := 498202208781844733137927

theorem tailTrace_1455368 : CollatzResearch.WordTrace tailWord_1455368 prefixEnd_1455368 498202208781844733137927 := by
  unfold tailWord_1455368
  simp only [CollatzResearch.WordTrace]
  refine ⟨26540815895728883955435379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35387754527638511940580505 26540815895728883955435379)
  ·
    refine ⟨39811223843593325933153069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26540815895728883955435379 39811223843593325933153069)
    ·
      refine ⟨14929208941347497224932401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39811223843593325933153069 14929208941347497224932401)
      ·
        refine ⟨11196906706010622918699301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14929208941347497224932401 11196906706010622918699301)
        ·
          refine ⟨2099420007376991797256119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11196906706010622918699301 2099420007376991797256119)
          ·
            refine ⟨3149130011065487695884179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2099420007376991797256119 3149130011065487695884179)
            ·
              refine ⟨4723695016598231543826269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3149130011065487695884179 4723695016598231543826269)
              ·
                refine ⟨1771385631224336828934851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4723695016598231543826269 1771385631224336828934851)
                ·
                  refine ⟨2657078446836505243402277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1771385631224336828934851 2657078446836505243402277)
                  ·
                    refine ⟨498202208781844733137927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2657078446836505243402277 498202208781844733137927)
                    ·
                      rfl

theorem cell22_1455368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_1455368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1455368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1455368 prefixEnd_1455368 := by exact prefixLift 1455368
  have htrace : WordTrace (prefixWord ++ tailWord_1455368) baseStart_1455368 baseEnd_1455368 := by
    simpa [prefixWord, tailWord_1455368, baseEnd_1455368] using wordTrace_append hprefix tailTrace_1455368
  have hstable : (prefixWord ++ tailWord_1455368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455368).length < 2 ^ (prefixWord ++ tailWord_1455368).sum := by decide
  have hdescent : baseEnd_1455368 < baseStart_1455368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455411 : List Nat := [1, 1, 1, 2, 5, 2, 4, 6]
def baseStart_1455411 : Nat := 118140960795 + 1455411 * 2 ^ 59
def prefixEnd_1455411 : Nat := 4983230072969 + 3 ^ 40 * 1455411 * 2
def baseEnd_1455411 : Nat := 55357436506734106034755

theorem tailTrace_1455411 : CollatzResearch.WordTrace tailWord_1455411 prefixEnd_1455411 55357436506734106034755 := by
  unfold tailWord_1455411
  simp only [CollatzResearch.WordTrace]
  refine ⟨53083200130301986254686087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35388800086867990836457391 53083200130301986254686087)
  ·
    refine ⟨79624800195452979382029131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53083200130301986254686087 79624800195452979382029131)
    ·
      refine ⟨119437200293179469073043697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79624800195452979382029131 119437200293179469073043697)
      ·
        refine ⟨89577900219884601804782773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119437200293179469073043697 89577900219884601804782773)
        ·
          refine ⟨8397928145614181419198385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89577900219884601804782773 8397928145614181419198385)
          ·
            refine ⟨6298446109210636064398789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8397928145614181419198385 6298446109210636064398789)
            ·
              refine ⟨1180958645476994262074773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6298446109210636064398789 1180958645476994262074773)
              ·
                refine ⟨55357436506734106034755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1180958645476994262074773 55357436506734106034755)
                ·
                  rfl

theorem cell22_1455411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 6].length) (baseStart_1455411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1455411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1455411 prefixEnd_1455411 := by exact prefixLift 1455411
  have htrace : WordTrace (prefixWord ++ tailWord_1455411) baseStart_1455411 baseEnd_1455411 := by
    simpa [prefixWord, tailWord_1455411, baseEnd_1455411] using wordTrace_append hprefix tailTrace_1455411
  have hstable : (prefixWord ++ tailWord_1455411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455411).length < 2 ^ (prefixWord ++ tailWord_1455411).sum := by decide
  have hdescent : baseEnd_1455411 < baseStart_1455411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455417 : List Nat := [1, 2, 1, 6, 3, 1, 1, 3, 4]
def baseStart_1455417 : Nat := 118140960795 + 1455417 * 2 ^ 59
def prefixEnd_1455417 : Nat := 4983230072969 + 3 ^ 40 * 1455417 * 2
def baseEnd_1455417 : Nat := 166072994161074979554259

theorem tailTrace_1455417 : CollatzResearch.WordTrace tailWord_1455417 prefixEnd_1455417 166072994161074979554259 := by
  unfold tailWord_1455417
  simp only [CollatzResearch.WordTrace]
  refine ⟨53083418968280249279404505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35388945978853499519603003 53083418968280249279404505)
  ·
    refine ⟨39812564226210186959553379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53083418968280249279404505 39812564226210186959553379)
    ·
      refine ⟨59718846339315280439330069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39812564226210186959553379 59718846339315280439330069)
      ·
        refine ⟨2799320922155403770593597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59718846339315280439330069 2799320922155403770593597)
        ·
          refine ⟨1049745345808276413972599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2799320922155403770593597 1049745345808276413972599)
          ·
            refine ⟨1574618018712414620958899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1049745345808276413972599 1574618018712414620958899)
            ·
              refine ⟨2361927028068621931438349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1574618018712414620958899 2361927028068621931438349)
              ·
                refine ⟨885722635525733224289381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2361927028068621931438349 885722635525733224289381)
                ·
                  refine ⟨166072994161074979554259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 885722635525733224289381 166072994161074979554259)
                  ·
                    rfl

theorem cell22_1455417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3, 4].length) (baseStart_1455417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1455417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1455417 prefixEnd_1455417 := by exact prefixLift 1455417
  have htrace : WordTrace (prefixWord ++ tailWord_1455417) baseStart_1455417 baseEnd_1455417 := by
    simpa [prefixWord, tailWord_1455417, baseEnd_1455417] using wordTrace_append hprefix tailTrace_1455417
  have hstable : (prefixWord ++ tailWord_1455417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455417).length < 2 ^ (prefixWord ++ tailWord_1455417).sum := by decide
  have hdescent : baseEnd_1455417 < baseStart_1455417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455428 : List Nat := [2, 3, 4, 1, 1, 3, 8]
def baseStart_1455428 : Nat := 118140960795 + 1455428 * 2 ^ 59
def prefixEnd_1455428 : Nat := 4983230072969 + 3 ^ 40 * 1455428 * 2
def baseEnd_1455428 : Nat := 18452694370667576912509

theorem tailTrace_1455428 : CollatzResearch.WordTrace tailWord_1455428 prefixEnd_1455428 18452694370667576912509 := by
  unfold tailWord_1455428
  simp only [CollatzResearch.WordTrace]
  refine ⟨26541910085620199079027469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35389213447493598772036625 26541910085620199079027469)
  ·
    refine ⟨9953216282107574654635301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26541910085620199079027469 9953216282107574654635301)
    ·
      refine ⟨1866228052895170247744119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9953216282107574654635301 1866228052895170247744119)
      ·
        refine ⟨2799342079342755371616179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1866228052895170247744119 2799342079342755371616179)
        ·
          refine ⟨4199013119014133057424269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2799342079342755371616179 4199013119014133057424269)
          ·
            refine ⟨1574629919630299896534101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4199013119014133057424269 1574629919630299896534101)
            ·
              refine ⟨18452694370667576912509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1574629919630299896534101 18452694370667576912509)
              ·
                rfl

theorem cell22_1455428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 8].length) (baseStart_1455428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1455428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1455428 prefixEnd_1455428 := by exact prefixLift 1455428
  have htrace : WordTrace (prefixWord ++ tailWord_1455428) baseStart_1455428 baseEnd_1455428 := by
    simpa [prefixWord, tailWord_1455428, baseEnd_1455428] using wordTrace_append hprefix tailTrace_1455428
  have hstable : (prefixWord ++ tailWord_1455428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455428).length < 2 ^ (prefixWord ++ tailWord_1455428).sum := by decide
  have hdescent : baseEnd_1455428 < baseStart_1455428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455490 : List Nat := [3, 4, 2, 1, 1, 1, 1, 4, 5]
def baseStart_1455490 : Nat := 118140960795 + 1455490 * 2 ^ 59
def prefixEnd_1455490 : Nat := 4983230072969 + 3 ^ 40 * 1455490 * 2
def baseEnd_1455490 : Nat := 166081323958359027195851

theorem tailTrace_1455490 : CollatzResearch.WordTrace tailWord_1455490 prefixEnd_1455490 166081323958359027195851 := by
  unfold tailWord_1455490
  simp only [CollatzResearch.WordTrace]
  refine ⟨13271520374253945686702981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35390720998010521831207949 13271520374253945686702981)
  ·
    refine ⟨2488410070172614816256809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13271520374253945686702981 2488410070172614816256809)
    ·
      refine ⟨1866307552629461112192607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2488410070172614816256809 1866307552629461112192607)
      ·
        refine ⟨2799461328944191668288911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1866307552629461112192607 2799461328944191668288911)
        ·
          refine ⟨4199191993416287502433367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2799461328944191668288911 4199191993416287502433367)
          ·
            refine ⟨6298787990124431253650051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4199191993416287502433367 6298787990124431253650051)
            ·
              refine ⟨9448181985186646880475077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6298787990124431253650051 9448181985186646880475077)
              ·
                refine ⟨1771534122222496290089077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9448181985186646880475077 1771534122222496290089077)
                ·
                  refine ⟨166081323958359027195851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1771534122222496290089077 166081323958359027195851)
                  ·
                    rfl

theorem cell22_1455490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_1455490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1455490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1455490 prefixEnd_1455490 := by exact prefixLift 1455490
  have htrace : WordTrace (prefixWord ++ tailWord_1455490) baseStart_1455490 baseEnd_1455490 := by
    simpa [prefixWord, tailWord_1455490, baseEnd_1455490] using wordTrace_append hprefix tailTrace_1455490
  have hstable : (prefixWord ++ tailWord_1455490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455490).length < 2 ^ (prefixWord ++ tailWord_1455490).sum := by decide
  have hdescent : baseEnd_1455490 < baseStart_1455490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455576 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 2, 6]
def baseStart_1455576 : Nat := 118140960795 + 1455576 * 2 ^ 59
def prefixEnd_1455576 : Nat := 4983230072969 + 3 ^ 40 * 1455576 * 2
def baseEnd_1455576 : Nat := 498273411432601523937289

theorem tailTrace_1455576 : CollatzResearch.WordTrace tailWord_1455576 prefixEnd_1455576 498273411432601523937289 := by
  unfold tailWord_1455576
  simp only [CollatzResearch.WordTrace]
  refine ⟨26544609087352109717221291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35392812116469479622961721 26544609087352109717221291)
  ·
    refine ⟨39816913631028164575831937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26544609087352109717221291 39816913631028164575831937)
    ·
      refine ⟨29862685223271123431873953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39816913631028164575831937 29862685223271123431873953)
      ·
        refine ⟨22397013917453342573905465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29862685223271123431873953 22397013917453342573905465)
        ·
          refine ⟨16797760438090006930429099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22397013917453342573905465 16797760438090006930429099)
          ·
            refine ⟨25196640657135010395643649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16797760438090006930429099 25196640657135010395643649)
            ·
              refine ⟨18897480492851257796732737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25196640657135010395643649 18897480492851257796732737)
              ·
                refine ⟨14173110369638443347549553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18897480492851257796732737 14173110369638443347549553)
                ·
                  refine ⟨10629832777228832510662165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14173110369638443347549553 10629832777228832510662165)
                  ·
                    refine ⟨498273411432601523937289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10629832777228832510662165 498273411432601523937289)
                    ·
                      rfl

theorem cell22_1455576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_1455576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1455576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1455576 prefixEnd_1455576 := by exact prefixLift 1455576
  have htrace : WordTrace (prefixWord ++ tailWord_1455576) baseStart_1455576 baseEnd_1455576 := by
    simpa [prefixWord, tailWord_1455576, baseEnd_1455576] using wordTrace_append hprefix tailTrace_1455576
  have hstable : (prefixWord ++ tailWord_1455576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455576).length < 2 ^ (prefixWord ++ tailWord_1455576).sum := by decide
  have hdescent : baseEnd_1455576 < baseStart_1455576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455595 : List Nat := [1, 1, 1, 1, 2, 3, 2, 7, 1, 3]
def baseStart_1455595 : Nat := 118140960795 + 1455595 * 2 ^ 59
def prefixEnd_1455595 : Nat := 4983230072969 + 3 ^ 40 * 1455595 * 2
def baseEnd_1455595 : Nat := 498279915520891807712231

theorem tailTrace_1455595 : CollatzResearch.WordTrace tailWord_1455595 prefixEnd_1455595 498279915520891807712231 := by
  unfold tailWord_1455595
  simp only [CollatzResearch.WordTrace]
  refine ⟨53089911161635385679384239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35393274107756923786256159 53089911161635385679384239)
  ·
    refine ⟨79634866742453078519076359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53089911161635385679384239 79634866742453078519076359)
    ·
      refine ⟨119452300113679617778614539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79634866742453078519076359 119452300113679617778614539)
      ·
        refine ⟨179178450170519426667921809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119452300113679617778614539 179178450170519426667921809)
        ·
          refine ⟨134383837627889570000941357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179178450170519426667921809 134383837627889570000941357)
          ·
            refine ⟨50393939110458588750353009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134383837627889570000941357 50393939110458588750353009)
            ·
              refine ⟨37795454332843941562764757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50393939110458588750353009 37795454332843941562764757)
              ·
                refine ⟨885830960926029880377299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 37795454332843941562764757 885830960926029880377299)
                ·
                  refine ⟨1328746441389044820565949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 885830960926029880377299 1328746441389044820565949)
                  ·
                    refine ⟨498279915520891807712231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1328746441389044820565949 498279915520891807712231)
                    ·
                      rfl

theorem cell22_1455595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7, 1, 3].length) (baseStart_1455595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1455595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1455595 prefixEnd_1455595 := by exact prefixLift 1455595
  have htrace : WordTrace (prefixWord ++ tailWord_1455595) baseStart_1455595 baseEnd_1455595 := by
    simpa [prefixWord, tailWord_1455595, baseEnd_1455595] using wordTrace_append hprefix tailTrace_1455595
  have hstable : (prefixWord ++ tailWord_1455595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455595).length < 2 ^ (prefixWord ++ tailWord_1455595).sum := by decide
  have hdescent : baseEnd_1455595 < baseStart_1455595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455621 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 2, 8]
def baseStart_1455621 : Nat := 118140960795 + 1455621 * 2 ^ 59
def prefixEnd_1455621 : Nat := 4983230072969 + 3 ^ 40 * 1455621 * 2
def baseEnd_1455621 : Nat := 498288815852236406562151

theorem tailTrace_1455621 : CollatzResearch.WordTrace tailWord_1455621 prefixEnd_1455621 498288815852236406562151 := by
  unfold tailWord_1455621
  simp only [CollatzResearch.WordTrace]
  refine ⟨53090859459541192119830717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35393906306360794746553811 53090859459541192119830717)
  ·
    refine ⟨19909072297327947044936519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53090859459541192119830717 19909072297327947044936519)
    ·
      refine ⟨29863608445991920567404779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19909072297327947044936519 29863608445991920567404779)
      ·
        refine ⟨44795412668987880851107169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29863608445991920567404779 44795412668987880851107169)
        ·
          refine ⟨33596559501740910638330377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44795412668987880851107169 33596559501740910638330377)
          ·
            refine ⟨25197419626305682978747783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33596559501740910638330377 25197419626305682978747783)
            ·
              refine ⟨37796129439458524468121675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25197419626305682978747783 37796129439458524468121675)
              ·
                refine ⟨56694194159187786702182513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37796129439458524468121675 56694194159187786702182513)
                ·
                  refine ⟨42520645619390840026636885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56694194159187786702182513 42520645619390840026636885)
                  ·
                    refine ⟨498288815852236406562151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42520645619390840026636885 498288815852236406562151)
                    ·
                      rfl

theorem cell22_1455621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_1455621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1455621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1455621 prefixEnd_1455621 := by exact prefixLift 1455621
  have htrace : WordTrace (prefixWord ++ tailWord_1455621) baseStart_1455621 baseEnd_1455621 := by
    simpa [prefixWord, tailWord_1455621, baseEnd_1455621] using wordTrace_append hprefix tailTrace_1455621
  have hstable : (prefixWord ++ tailWord_1455621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455621).length < 2 ^ (prefixWord ++ tailWord_1455621).sum := by decide
  have hdescent : baseEnd_1455621 < baseStart_1455621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455685 : List Nat := [1, 3, 1, 1, 1, 4, 1, 5, 2, 3]
def baseStart_1455685 : Nat := 118140960795 + 1455685 * 2 ^ 59
def prefixEnd_1455685 : Nat := 4983230072969 + 3 ^ 40 * 1455685 * 2
def baseEnd_1455685 : Nat := 498310724360161572961955

theorem tailTrace_1455685 : CollatzResearch.WordTrace tailWord_1455685 prefixEnd_1455685 498310724360161572961955 := by
  unfold tailWord_1455685
  simp only [CollatzResearch.WordTrace]
  refine ⟨53093193731309331050160509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35395462487539554033440339 53093193731309331050160509)
  ·
    refine ⟨19909947649240999143810191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53093193731309331050160509 19909947649240999143810191)
    ·
      refine ⟨29864921473861498715715287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19909947649240999143810191 29864921473861498715715287)
      ·
        refine ⟨44797382210792248073572931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29864921473861498715715287 44797382210792248073572931)
        ·
          refine ⟨67196073316188372110359397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44797382210792248073572931 67196073316188372110359397)
          ·
            refine ⟨12599263746785319770692387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67196073316188372110359397 12599263746785319770692387)
            ·
              refine ⟨18898895620177979656038581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12599263746785319770692387 18898895620177979656038581)
              ·
                refine ⟨1771771464391685592753617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18898895620177979656038581 1771771464391685592753617)
                ·
                  refine ⟨1328828598293764194565213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1771771464391685592753617 1328828598293764194565213)
                  ·
                    refine ⟨498310724360161572961955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1328828598293764194565213 498310724360161572961955)
                    ·
                      rfl

theorem cell22_1455685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2, 3].length) (baseStart_1455685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1455685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1455685 prefixEnd_1455685 := by exact prefixLift 1455685
  have htrace : WordTrace (prefixWord ++ tailWord_1455685) baseStart_1455685 baseEnd_1455685 := by
    simpa [prefixWord, tailWord_1455685, baseEnd_1455685] using wordTrace_append hprefix tailTrace_1455685
  have hstable : (prefixWord ++ tailWord_1455685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455685).length < 2 ^ (prefixWord ++ tailWord_1455685).sum := by decide
  have hdescent : baseEnd_1455685 < baseStart_1455685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455803 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 5, 5]
def baseStart_1455803 : Nat := 118140960795 + 1455803 * 2 ^ 59
def prefixEnd_1455803 : Nat := 4983230072969 + 3 ^ 40 * 1455803 * 2
def baseEnd_1455803 : Nat := 498351118171648598511593

theorem tailTrace_1455803 : CollatzResearch.WordTrace tailWord_1455803 prefixEnd_1455803 498351118171648598511593 := by
  unfold tailWord_1455803
  simp only [CollatzResearch.WordTrace]
  refine ⟨53097497544881837202956063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35398331696587891468637375 53097497544881837202956063)
  ·
    refine ⟨79646246317322755804434095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53097497544881837202956063 79646246317322755804434095)
    ·
      refine ⟨119469369475984133706651143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79646246317322755804434095 119469369475984133706651143)
      ·
        refine ⟨179204054213976200559976715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119469369475984133706651143 179204054213976200559976715)
        ·
          refine ⟨268806081320964300839965073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179204054213976200559976715 268806081320964300839965073)
          ·
            refine ⟨201604560990723225629973805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268806081320964300839965073 201604560990723225629973805)
            ·
              refine ⟨75601710371521209611240177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201604560990723225629973805 75601710371521209611240177)
              ·
                refine ⟨56701282778640907208430133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75601710371521209611240177 56701282778640907208430133)
                ·
                  refine ⟨5315745260497585050790325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56701282778640907208430133 5315745260497585050790325)
                  ·
                    refine ⟨498351118171648598511593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5315745260497585050790325 498351118171648598511593)
                    ·
                      rfl

theorem cell22_1455803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 5].length) (baseStart_1455803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1455803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1455803 prefixEnd_1455803 := by exact prefixLift 1455803
  have htrace : WordTrace (prefixWord ++ tailWord_1455803) baseStart_1455803 baseEnd_1455803 := by
    simpa [prefixWord, tailWord_1455803, baseEnd_1455803] using wordTrace_append hprefix tailTrace_1455803
  have hstable : (prefixWord ++ tailWord_1455803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455803).length < 2 ^ (prefixWord ++ tailWord_1455803).sum := by decide
  have hdescent : baseEnd_1455803 < baseStart_1455803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455822 : List Nat := [4, 1, 1, 1, 3, 1, 2, 5, 4]
def baseStart_1455822 : Nat := 118140960795 + 1455822 * 2 ^ 59
def prefixEnd_1455822 : Nat := 4983230072969 + 3 ^ 40 * 1455822 * 2
def baseEnd_1455822 : Nat := 166119207419979627428845

theorem tailTrace_1455822 : CollatzResearch.WordTrace tailWord_1455822 prefixEnd_1455822 166119207419979627428845 := by
  unfold tailWord_1455822
  simp only [CollatzResearch.WordTrace]
  refine ⟨6637273816476625430987215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35398793687875335631931813 6637273816476625430987215)
  ·
    refine ⟨9955910724714938146480823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6637273816476625430987215 9955910724714938146480823)
    ·
      refine ⟨14933866087072407219721235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9955910724714938146480823 14933866087072407219721235)
      ·
        refine ⟨22400799130608610829581853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14933866087072407219721235 22400799130608610829581853)
        ·
          refine ⟨8400299673978229061093195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22400799130608610829581853 8400299673978229061093195)
          ·
            refine ⟨12600449510967343591639793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8400299673978229061093195 12600449510967343591639793)
            ·
              refine ⟨9450337133225507693729845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12600449510967343591639793 9450337133225507693729845)
              ·
                refine ⟨885969106239891346287173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9450337133225507693729845 885969106239891346287173)
                ·
                  refine ⟨166119207419979627428845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 885969106239891346287173 166119207419979627428845)
                  ·
                    rfl

theorem cell22_1455822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_1455822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1455822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1455822 prefixEnd_1455822 := by exact prefixLift 1455822
  have htrace : WordTrace (prefixWord ++ tailWord_1455822) baseStart_1455822 baseEnd_1455822 := by
    simpa [prefixWord, tailWord_1455822, baseEnd_1455822] using wordTrace_append hprefix tailTrace_1455822
  have hstable : (prefixWord ++ tailWord_1455822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455822).length < 2 ^ (prefixWord ++ tailWord_1455822).sum := by decide
  have hdescent : baseEnd_1455822 < baseStart_1455822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455833 : List Nat := [1, 2, 1, 2, 3, 13]
def baseStart_1455833 : Nat := 118140960795 + 1455833 * 2 ^ 59
def prefixEnd_1455833 : Nat := 4983230072969 + 3 ^ 40 * 1455833 * 2
def baseEnd_1455833 : Nat := 6152609725737512595821

theorem tailTrace_1455833 : CollatzResearch.WordTrace tailWord_1455833 prefixEnd_1455833 6152609725737512595821 := by
  unfold tailWord_1455833
  simp only [CollatzResearch.WordTrace]
  refine ⟨53098591734773152326548153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35399061156515434884365435 53098591734773152326548153)
  ·
    refine ⟨39823943801079864244911115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53098591734773152326548153 39823943801079864244911115)
    ·
      refine ⟨59735915701619796367366673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39823943801079864244911115 59735915701619796367366673)
      ·
        refine ⟨44801936776214847275525005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59735915701619796367366673 44801936776214847275525005)
        ·
          refine ⟨16800726291080567728321877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44801936776214847275525005 16800726291080567728321877)
          ·
            refine ⟨6152609725737512595821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 16800726291080567728321877 6152609725737512595821)
            ·
              rfl

theorem cell22_1455833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 13].length) (baseStart_1455833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1455833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1455833 prefixEnd_1455833 := by exact prefixLift 1455833
  have htrace : WordTrace (prefixWord ++ tailWord_1455833) baseStart_1455833 baseEnd_1455833 := by
    simpa [prefixWord, tailWord_1455833, baseEnd_1455833] using wordTrace_append hprefix tailTrace_1455833
  have hstable : (prefixWord ++ tailWord_1455833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455833).length < 2 ^ (prefixWord ++ tailWord_1455833).sum := by decide
  have hdescent : baseEnd_1455833 < baseStart_1455833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455850 : List Nat := [3, 1, 3, 1, 1, 1, 5, 7]
def baseStart_1455850 : Nat := 118140960795 + 1455850 * 2 ^ 59
def prefixEnd_1455850 : Nat := 4983230072969 + 3 ^ 40 * 1455850 * 2
def baseEnd_1455850 : Nat := 55374134136906238065161

theorem tailTrace_1455850 : CollatzResearch.WordTrace tailWord_1455850 prefixEnd_1455850 55374134136906238065161 := by
  unfold tailWord_1455850
  simp only [CollatzResearch.WordTrace]
  refine ⟨13274802943927891057479251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35399474517141042819944669 13274802943927891057479251)
  ·
    refine ⟨19912204415891836586218877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13274802943927891057479251 19912204415891836586218877)
    ·
      refine ⟨7467076655959438719832079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19912204415891836586218877 7467076655959438719832079)
      ·
        refine ⟨11200614983939158079748119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7467076655959438719832079 11200614983939158079748119)
        ·
          refine ⟨16800922475908737119622179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11200614983939158079748119 16800922475908737119622179)
          ·
            refine ⟨25201383713863105679433269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16800922475908737119622179 25201383713863105679433269)
            ·
              refine ⟨2362629723174666157446869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25201383713863105679433269 2362629723174666157446869)
              ·
                refine ⟨55374134136906238065161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2362629723174666157446869 55374134136906238065161)
                ·
                  rfl

theorem cell22_1455850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 7].length) (baseStart_1455850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1455850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1455850 prefixEnd_1455850 := by exact prefixLift 1455850
  have htrace : WordTrace (prefixWord ++ tailWord_1455850) baseStart_1455850 baseEnd_1455850 := by
    simpa [prefixWord, tailWord_1455850, baseEnd_1455850] using wordTrace_append hprefix tailTrace_1455850
  have hstable : (prefixWord ++ tailWord_1455850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455850).length < 2 ^ (prefixWord ++ tailWord_1455850).sum := by decide
  have hdescent : baseEnd_1455850 < baseStart_1455850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455933 : List Nat := [1, 4, 1, 4, 1, 3, 1, 3, 1, 3]
def baseStart_1455933 : Nat := 118140960795 + 1455933 * 2 ^ 59
def prefixEnd_1455933 : Nat := 4983230072969 + 3 ^ 40 * 1455933 * 2
def baseEnd_1455933 : Nat := 498395619828371592761195

theorem tailTrace_1455933 : CollatzResearch.WordTrace tailWord_1455933 prefixEnd_1455933 498395619828371592761195 := by
  unfold tailWord_1455933
  simp only [CollatzResearch.WordTrace]
  refine ⟨53102239034410869405188453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35401492689607246270125635 53102239034410869405188453)
  ·
    refine ⟨9956669818952038013472835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53102239034410869405188453 9956669818952038013472835)
    ·
      refine ⟨14935004728428057020209253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9956669818952038013472835 14935004728428057020209253)
      ·
        refine ⟨2800313386580260691289235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14935004728428057020209253 2800313386580260691289235)
        ·
          refine ⟨4200470079870391036933853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2800313386580260691289235 4200470079870391036933853)
          ·
            refine ⟨1575176279951396638850195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4200470079870391036933853 1575176279951396638850195)
            ·
              refine ⟨2362764419927094958275293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1575176279951396638850195 2362764419927094958275293)
              ·
                refine ⟨886036657472660609353235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2362764419927094958275293 886036657472660609353235)
                ·
                  refine ⟨1329054986208990914029853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 886036657472660609353235 1329054986208990914029853)
                  ·
                    refine ⟨498395619828371592761195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1329054986208990914029853 498395619828371592761195)
                    ·
                      rfl

theorem cell22_1455933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_1455933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1455933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1455933 prefixEnd_1455933 := by exact prefixLift 1455933
  have htrace : WordTrace (prefixWord ++ tailWord_1455933) baseStart_1455933 baseEnd_1455933 := by
    simpa [prefixWord, tailWord_1455933, baseEnd_1455933] using wordTrace_append hprefix tailTrace_1455933
  have hstable : (prefixWord ++ tailWord_1455933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455933).length < 2 ^ (prefixWord ++ tailWord_1455933).sum := by decide
  have hdescent : baseEnd_1455933 < baseStart_1455933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455957 : List Nat := [1, 3, 2, 2, 2, 2, 3, 1, 6]
def baseStart_1455957 : Nat := 118140960795 + 1455957 * 2 ^ 59
def prefixEnd_1455957 : Nat := 4983230072969 + 3 ^ 40 * 1455957 * 2
def baseEnd_1455957 : Nat := 166134611839614510053707

theorem tailTrace_1455957 : CollatzResearch.WordTrace tailWord_1455957 prefixEnd_1455957 166134611839614510053707 := by
  unfold tailWord_1455957
  simp only [CollatzResearch.WordTrace]
  refine ⟨53103114386323921504062125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35402076257549281002708083 53103114386323921504062125)
  ·
    refine ⟨19913667894871470564023297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53103114386323921504062125 19913667894871470564023297)
    ·
      refine ⟨14935250921153602923017473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19913667894871470564023297 14935250921153602923017473)
      ·
        refine ⟨11201438190865202192263105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14935250921153602923017473 11201438190865202192263105)
        ·
          refine ⟨8401078643148901644197329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11201438190865202192263105 8401078643148901644197329)
          ·
            refine ⟨6300808982361676233147997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8401078643148901644197329 6300808982361676233147997)
            ·
              refine ⟨2362803368385628587430499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6300808982361676233147997 2362803368385628587430499)
              ·
                refine ⟨3544205052578442881145749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2362803368385628587430499 3544205052578442881145749)
                ·
                  refine ⟨166134611839614510053707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3544205052578442881145749 166134611839614510053707)
                  ·
                    rfl

theorem cell22_1455957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 6].length) (baseStart_1455957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1455957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1455957 prefixEnd_1455957 := by exact prefixLift 1455957
  have htrace : WordTrace (prefixWord ++ tailWord_1455957) baseStart_1455957 baseEnd_1455957 := by
    simpa [prefixWord, tailWord_1455957, baseEnd_1455957] using wordTrace_append hprefix tailTrace_1455957
  have hstable : (prefixWord ++ tailWord_1455957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455957).length < 2 ^ (prefixWord ++ tailWord_1455957).sum := by decide
  have hdescent : baseEnd_1455957 < baseStart_1455957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455985 : List Nat := [1, 2, 2, 2, 1, 3, 1, 10]
def baseStart_1455985 : Nat := 118140960795 + 1455985 * 2 ^ 59
def prefixEnd_1455985 : Nat := 4983230072969 + 3 ^ 40 * 1455985 * 2
def baseEnd_1455985 : Nat := 55379268943451198940115

theorem tailTrace_1455985 : CollatzResearch.WordTrace tailWord_1455985 prefixEnd_1455985 55379268943451198940115 := by
  unfold tailWord_1455985
  simp only [CollatzResearch.WordTrace]
  refine ⟨53104135630222482286081409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35402757086814988190720939 53104135630222482286081409)
  ·
    refine ⟨39828101722666861714561057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53104135630222482286081409 39828101722666861714561057)
    ·
      refine ⟨29871076292000146285920793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39828101722666861714561057 29871076292000146285920793)
      ·
        refine ⟨22403307219000109714440595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29871076292000146285920793 22403307219000109714440595)
        ·
          refine ⟨33604960828500164571660893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22403307219000109714440595 33604960828500164571660893)
          ·
            refine ⟨12601860310687561714372835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33604960828500164571660893 12601860310687561714372835)
            ·
              refine ⟨18902790466031342571559253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12601860310687561714372835 18902790466031342571559253)
              ·
                refine ⟨55379268943451198940115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18902790466031342571559253 55379268943451198940115)
                ·
                  rfl

theorem cell22_1455985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 10].length) (baseStart_1455985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1455985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1455985 prefixEnd_1455985 := by exact prefixLift 1455985
  have htrace : WordTrace (prefixWord ++ tailWord_1455985) baseStart_1455985 baseEnd_1455985 := by
    simpa [prefixWord, tailWord_1455985, baseEnd_1455985] using wordTrace_append hprefix tailTrace_1455985
  have hstable : (prefixWord ++ tailWord_1455985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455985).length < 2 ^ (prefixWord ++ tailWord_1455985).sum := by decide
  have hdescent : baseEnd_1455985 < baseStart_1455985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456002 : List Nat := [3, 4, 2, 13]
def baseStart_1456002 : Nat := 118140960795 + 1456002 * 2 ^ 59
def prefixEnd_1456002 : Nat := 4983230072969 + 3 ^ 40 * 1456002 * 2
def baseEnd_1456002 : Nat := 683702661095306464727

theorem tailTrace_1456002 : CollatzResearch.WordTrace tailWord_1456002 prefixEnd_1456002 683702661095306464727 := by
  unfold tailWord_1456002
  simp only [CollatzResearch.WordTrace]
  refine ⟨13276188917790223547362565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35403170447440596126300173 13276188917790223547362565)
  ·
    refine ⟨2489285422085666915130481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13276188917790223547362565 2489285422085666915130481)
    ·
      refine ⟨1866964066564250186347861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2489285422085666915130481 1866964066564250186347861)
      ·
        refine ⟨683702661095306464727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 1866964066564250186347861 683702661095306464727)
        ·
          rfl

theorem cell22_1456002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 13].length) (baseStart_1456002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1456002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1456002 prefixEnd_1456002 := by exact prefixLift 1456002
  have htrace : WordTrace (prefixWord ++ tailWord_1456002) baseStart_1456002 baseEnd_1456002 := by
    simpa [prefixWord, tailWord_1456002, baseEnd_1456002] using wordTrace_append hprefix tailTrace_1456002
  have hstable : (prefixWord ++ tailWord_1456002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456002).length < 2 ^ (prefixWord ++ tailWord_1456002).sum := by decide
  have hdescent : baseEnd_1456002 < baseStart_1456002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456008 : List Nat := [2, 1, 3, 3, 3, 2, 2, 2, 4]
def baseStart_1456008 : Nat := 118140960795 + 1456008 * 2 ^ 59
def prefixEnd_1456008 : Nat := 4983230072969 + 3 ^ 40 * 1456008 * 2
def baseEnd_1456008 : Nat := 166140431287032132378655

theorem tailTrace_1456008 : CollatzResearch.WordTrace tailWord_1456008 prefixEnd_1456008 166140431287032132378655 := by
  unfold tailWord_1456008
  simp only [CollatzResearch.WordTrace]
  refine ⟨26552487254569578607084339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35403316339426104809445785 26552487254569578607084339)
  ·
    refine ⟨39828730881854367910626509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26552487254569578607084339 39828730881854367910626509)
    ·
      refine ⟨14935774080695387966484941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39828730881854367910626509 14935774080695387966484941)
      ·
        refine ⟨5600915280260770487431853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14935774080695387966484941 5600915280260770487431853)
        ·
          refine ⟨2100343230097788932786945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5600915280260770487431853 2100343230097788932786945)
          ·
            refine ⟨1575257422573341699590209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2100343230097788932786945 1575257422573341699590209)
            ·
              refine ⟨1181443066930006274692657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1575257422573341699590209 1181443066930006274692657)
              ·
                refine ⟨886082300197504706019493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1181443066930006274692657 886082300197504706019493)
                ·
                  refine ⟨166140431287032132378655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 886082300197504706019493 166140431287032132378655)
                  ·
                    rfl

theorem cell22_1456008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2, 4].length) (baseStart_1456008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1456008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1456008 prefixEnd_1456008 := by exact prefixLift 1456008
  have htrace : WordTrace (prefixWord ++ tailWord_1456008) baseStart_1456008 baseEnd_1456008 := by
    simpa [prefixWord, tailWord_1456008, baseEnd_1456008] using wordTrace_append hprefix tailTrace_1456008
  have hstable : (prefixWord ++ tailWord_1456008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456008).length < 2 ^ (prefixWord ++ tailWord_1456008).sum := by decide
  have hdescent : baseEnd_1456008 < baseStart_1456008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456051 : List Nat := [1, 1, 1, 2, 3, 1, 6, 3, 1, 3]
def baseStart_1456051 : Nat := 118140960795 + 1456051 * 2 ^ 59
def prefixEnd_1456051 : Nat := 4983230072969 + 3 ^ 40 * 1456051 * 2
def baseEnd_1456051 : Nat := 498436013639858618310833

theorem tailTrace_1456051 : CollatzResearch.WordTrace tailWord_1456051 prefixEnd_1456051 498436013639858618310833 := by
  unfold tailWord_1456051
  simp only [CollatzResearch.WordTrace]
  refine ⟨53106542847983375557984007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35404361898655583705322671 53106542847983375557984007)
  ·
    refine ⟨79659814271975063336976011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53106542847983375557984007 79659814271975063336976011)
    ·
      refine ⟨119489721407962595005464017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79659814271975063336976011 119489721407962595005464017)
      ·
        refine ⟨89617291055971946254098013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119489721407962595005464017 89617291055971946254098013)
        ·
          refine ⟨33606484145989479845286755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89617291055971946254098013 33606484145989479845286755)
          ·
            refine ⟨50409726218984219767930133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33606484145989479845286755 50409726218984219767930133)
            ·
              refine ⟨2362955916514885301621725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50409726218984219767930133 2362955916514885301621725)
              ·
                refine ⟨886108468693081988108147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2362955916514885301621725 886108468693081988108147)
                ·
                  refine ⟨1329162703039622982162221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 886108468693081988108147 1329162703039622982162221)
                  ·
                    refine ⟨498436013639858618310833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1329162703039622982162221 498436013639858618310833)
                    ·
                      rfl

theorem cell22_1456051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3, 1, 3].length) (baseStart_1456051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1456051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1456051 prefixEnd_1456051 := by exact prefixLift 1456051
  have htrace : WordTrace (prefixWord ++ tailWord_1456051) baseStart_1456051 baseEnd_1456051 := by
    simpa [prefixWord, tailWord_1456051, baseEnd_1456051] using wordTrace_append hprefix tailTrace_1456051
  have hstable : (prefixWord ++ tailWord_1456051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456051).length < 2 ^ (prefixWord ++ tailWord_1456051).sum := by decide
  have hdescent : baseEnd_1456051 < baseStart_1456051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456107 : List Nat := [1, 1, 1, 1, 2, 3, 1, 6, 1, 5]
def baseStart_1456107 : Nat := 118140960795 + 1456107 * 2 ^ 59
def prefixEnd_1456107 : Nat := 4983230072969 + 3 ^ 40 * 1456107 * 2
def baseEnd_1456107 : Nat := 498455183584293138910661

theorem tailTrace_1456107 : CollatzResearch.WordTrace tailWord_1456107 prefixEnd_1456107 498455183584293138910661 := by
  unfold tailWord_1456107
  simp only [CollatzResearch.WordTrace]
  refine ⟨53108585335780497122022575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35405723557186998081348383 53108585335780497122022575)
  ·
    refine ⟨79662878003670745683033863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53108585335780497122022575 79662878003670745683033863)
    ·
      refine ⟨119494317005506118524550795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79662878003670745683033863 119494317005506118524550795)
      ·
        refine ⟨179241475508259177786826193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119494317005506118524550795 179241475508259177786826193)
        ·
          refine ⟨134431106631194383340119645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179241475508259177786826193 134431106631194383340119645)
          ·
            refine ⟨50411664986697893752544867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134431106631194383340119645 50411664986697893752544867)
            ·
              refine ⟨75617497480046840628817301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50411664986697893752544867 75617497480046840628817301)
              ·
                refine ⟨3544570194377195654475811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75617497480046840628817301 3544570194377195654475811)
                ·
                  refine ⟨5316855291565793481713717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3544570194377195654475811 5316855291565793481713717)
                  ·
                    refine ⟨498455183584293138910661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5316855291565793481713717 498455183584293138910661)
                    ·
                      rfl

theorem cell22_1456107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 5].length) (baseStart_1456107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1456107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1456107 prefixEnd_1456107 := by exact prefixLift 1456107
  have htrace : WordTrace (prefixWord ++ tailWord_1456107) baseStart_1456107 baseEnd_1456107 := by
    simpa [prefixWord, tailWord_1456107, baseEnd_1456107] using wordTrace_append hprefix tailTrace_1456107
  have hstable : (prefixWord ++ tailWord_1456107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456107).length < 2 ^ (prefixWord ++ tailWord_1456107).sum := by decide
  have hdescent : baseEnd_1456107 < baseStart_1456107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456124 : List Nat := [2, 2, 2, 1, 2, 2, 1, 3, 4, 3]
def baseStart_1456124 : Nat := 118140960795 + 1456124 * 2 ^ 59
def prefixEnd_1456124 : Nat := 4983230072969 + 3 ^ 40 * 1456124 * 2
def baseEnd_1456124 : Nat := 498461003031710761235609

theorem tailTrace_1456124 : CollatzResearch.WordTrace tailWord_1456124 prefixEnd_1456124 498461003031710761235609 := by
  unfold tailWord_1456124
  simp only [CollatzResearch.WordTrace]
  refine ⟨26554602688359454512695713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35406136917812606016927617 26554602688359454512695713)
  ·
    refine ⟨19915952016269590884521785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26554602688359454512695713 19915952016269590884521785)
    ·
      refine ⟨14936964012202193163391339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19915952016269590884521785 14936964012202193163391339)
      ·
        refine ⟨22405446018303289745087009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14936964012202193163391339 22405446018303289745087009)
        ·
          refine ⟨16804084513727467308815257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22405446018303289745087009 16804084513727467308815257)
          ·
            refine ⟨12603063385295600481611443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16804084513727467308815257 12603063385295600481611443)
            ·
              refine ⟨18904595077943400722417165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12603063385295600481611443 18904595077943400722417165)
              ·
                refine ⟨7089223154228775270906437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18904595077943400722417165 7089223154228775270906437)
                ·
                  refine ⟨1329229341417895363294957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7089223154228775270906437 1329229341417895363294957)
                  ·
                    refine ⟨498461003031710761235609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1329229341417895363294957 498461003031710761235609)
                    ·
                      rfl

theorem cell22_1456124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_1456124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1456124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1456124 prefixEnd_1456124 := by exact prefixLift 1456124
  have htrace : WordTrace (prefixWord ++ tailWord_1456124) baseStart_1456124 baseEnd_1456124 := by
    simpa [prefixWord, tailWord_1456124, baseEnd_1456124] using wordTrace_append hprefix tailTrace_1456124
  have hstable : (prefixWord ++ tailWord_1456124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456124).length < 2 ^ (prefixWord ++ tailWord_1456124).sum := by decide
  have hdescent : baseEnd_1456124 < baseStart_1456124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456126 : List Nat := [4, 2, 2, 2, 1, 1, 3, 1, 6]
def baseStart_1456126 : Nat := 118140960795 + 1456126 * 2 ^ 59
def prefixEnd_1456126 : Nat := 4983230072969 + 3 ^ 40 * 1456126 * 2
def baseEnd_1456126 : Nat := 166153895890861140895201

theorem tailTrace_1456126 : CollatzResearch.WordTrace tailWord_1456126 prefixEnd_1456126 166153895890861140895201 := by
  unfold tailWord_1456126
  simp only [CollatzResearch.WordTrace]
  refine ⟨6638659790338957920870529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35406185548474442244642821 6638659790338957920870529)
  ·
    refine ⟨4978994842754218440652897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6638659790338957920870529 4978994842754218440652897)
    ·
      refine ⟨3734246132065663830489673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4978994842754218440652897 3734246132065663830489673)
      ·
        refine ⟨2800684599049247872867255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3734246132065663830489673 2800684599049247872867255)
        ·
          refine ⟨4201026898573871809300883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2800684599049247872867255 4201026898573871809300883)
          ·
            refine ⟨6301540347860807713951325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4201026898573871809300883 6301540347860807713951325)
            ·
              refine ⟨2363077630447802892731747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6301540347860807713951325 2363077630447802892731747)
              ·
                refine ⟨3544616445671704339097621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2363077630447802892731747 3544616445671704339097621)
                ·
                  refine ⟨166153895890861140895201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3544616445671704339097621 166153895890861140895201)
                  ·
                    rfl

theorem cell22_1456126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_1456126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1456126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1456126 prefixEnd_1456126 := by exact prefixLift 1456126
  have htrace : WordTrace (prefixWord ++ tailWord_1456126) baseStart_1456126 baseEnd_1456126 := by
    simpa [prefixWord, tailWord_1456126, baseEnd_1456126] using wordTrace_append hprefix tailTrace_1456126
  have hstable : (prefixWord ++ tailWord_1456126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456126).length < 2 ^ (prefixWord ++ tailWord_1456126).sum := by decide
  have hdescent : baseEnd_1456126 < baseStart_1456126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456156 : List Nat := [2, 2, 3, 1, 3, 2, 2, 1, 2, 4]
def baseStart_1456156 : Nat := 118140960795 + 1456156 * 2 ^ 59
def prefixEnd_1456156 : Nat := 4983230072969 + 3 ^ 40 * 1456156 * 2
def baseEnd_1456156 : Nat := 498471957285673344435511

theorem tailTrace_1456156 : CollatzResearch.WordTrace tailWord_1456156 prefixEnd_1456156 498471957285673344435511 := by
  unfold tailWord_1456156
  simp only [CollatzResearch.WordTrace]
  refine ⟨26555186256301489245278161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35406915008401985660370881 26555186256301489245278161)
  ·
    refine ⟨19916389692226116933958621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26555186256301489245278161 19916389692226116933958621)
    ·
      refine ⟨7468646134584793850234483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19916389692226116933958621 7468646134584793850234483)
      ·
        refine ⟨11202969201877190775351725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7468646134584793850234483 11202969201877190775351725)
        ·
          refine ⟨4201113450703946540756897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11202969201877190775351725 4201113450703946540756897)
          ·
            refine ⟨3150835088027959905567673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4201113450703946540756897 3150835088027959905567673)
            ·
              refine ⟨2363126316020969929175755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3150835088027959905567673 2363126316020969929175755)
              ·
                refine ⟨3544689474031454893763633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2363126316020969929175755 3544689474031454893763633)
                ·
                  refine ⟨2658517105523591170322725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3544689474031454893763633 2658517105523591170322725)
                  ·
                    refine ⟨498471957285673344435511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2658517105523591170322725 498471957285673344435511)
                    ·
                      rfl

theorem cell22_1456156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_1456156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1456156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1456156 prefixEnd_1456156 := by exact prefixLift 1456156
  have htrace : WordTrace (prefixWord ++ tailWord_1456156) baseStart_1456156 baseEnd_1456156 := by
    simpa [prefixWord, tailWord_1456156, baseEnd_1456156] using wordTrace_append hprefix tailTrace_1456156
  have hstable : (prefixWord ++ tailWord_1456156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456156).length < 2 ^ (prefixWord ++ tailWord_1456156).sum := by decide
  have hdescent : baseEnd_1456156 < baseStart_1456156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456199 : List Nat := [1, 1, 4, 1, 3, 1, 1, 5, 5]
def baseStart_1456199 : Nat := 118140960795 + 1456199 * 2 ^ 59
def prefixEnd_1456199 : Nat := 4983230072969 + 3 ^ 40 * 1456199 * 2
def baseEnd_1456199 : Nat := 166162225688145188536793

theorem tailTrace_1456199 : CollatzResearch.WordTrace tailWord_1456199 prefixEnd_1456199 166162225688145188536793 := by
  unfold tailWord_1456199
  simp only [CollatzResearch.WordTrace]
  refine ⟨53111940851447196834371651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35407960567631464556247767 53111940851447196834371651)
  ·
    refine ⟨79667911277170795251557477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53111940851447196834371651 79667911277170795251557477)
    ·
      refine ⟨14937733364469524109667027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79667911277170795251557477 14937733364469524109667027)
      ·
        refine ⟨22406600046704286164500541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14937733364469524109667027 22406600046704286164500541)
        ·
          refine ⟨8402475017514107311687703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22406600046704286164500541 8402475017514107311687703)
          ·
            refine ⟨12603712526271160967531555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8402475017514107311687703 12603712526271160967531555)
            ·
              refine ⟨18905568789406741451297333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12603712526271160967531555 18905568789406741451297333)
              ·
                refine ⟨1772397074006882011059125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18905568789406741451297333 1772397074006882011059125)
                ·
                  refine ⟨166162225688145188536793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1772397074006882011059125 166162225688145188536793)
                  ·
                    rfl

theorem cell22_1456199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 5].length) (baseStart_1456199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1456199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1456199 prefixEnd_1456199 := by exact prefixLift 1456199
  have htrace : WordTrace (prefixWord ++ tailWord_1456199) baseStart_1456199 baseEnd_1456199 := by
    simpa [prefixWord, tailWord_1456199, baseEnd_1456199] using wordTrace_append hprefix tailTrace_1456199
  have hstable : (prefixWord ++ tailWord_1456199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456199).length < 2 ^ (prefixWord ++ tailWord_1456199).sum := by decide
  have hdescent : baseEnd_1456199 < baseStart_1456199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456220 : List Nat := [2, 2, 4, 1, 1, 3, 2, 3, 1, 3]
def baseStart_1456220 : Nat := 118140960795 + 1456220 * 2 ^ 59
def prefixEnd_1456220 : Nat := 4983230072969 + 3 ^ 40 * 1456220 * 2
def baseEnd_1456220 : Nat := 498493865793598510835315

theorem tailTrace_1456220 : CollatzResearch.WordTrace tailWord_1456220 prefixEnd_1456220 498493865793598510835315 := by
  unfold tailWord_1456220
  simp only [CollatzResearch.WordTrace]
  refine ⟨26556353392185558710443057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35408471189580744947257409 26556353392185558710443057)
  ·
    refine ⟨19917265044139169032832293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26556353392185558710443057 19917265044139169032832293)
    ·
      refine ⟨3734487195776094193656055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19917265044139169032832293 3734487195776094193656055)
      ·
        refine ⟨5601730793664141290484083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3734487195776094193656055 5601730793664141290484083)
        ·
          refine ⟨8402596190496211935726125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5601730793664141290484083 8402596190496211935726125)
          ·
            refine ⟨3150973571436079475897297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8402596190496211935726125 3150973571436079475897297)
            ·
              refine ⟨2363230178577059606922973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3150973571436079475897297 2363230178577059606922973)
              ·
                refine ⟨886211316966397352596115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2363230178577059606922973 886211316966397352596115)
                ·
                  refine ⟨1329316975449596028894173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 886211316966397352596115 1329316975449596028894173)
                  ·
                    refine ⟨498493865793598510835315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1329316975449596028894173 498493865793598510835315)
                    ·
                      rfl

theorem cell22_1456220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_1456220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1456220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1456220 prefixEnd_1456220 := by exact prefixLift 1456220
  have htrace : WordTrace (prefixWord ++ tailWord_1456220) baseStart_1456220 baseEnd_1456220 := by
    simpa [prefixWord, tailWord_1456220, baseEnd_1456220] using wordTrace_append hprefix tailTrace_1456220
  have hstable : (prefixWord ++ tailWord_1456220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456220).length < 2 ^ (prefixWord ++ tailWord_1456220).sum := by decide
  have hdescent : baseEnd_1456220 < baseStart_1456220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456289 : List Nat := [1, 2, 3, 3, 1, 2, 10]
def baseStart_1456289 : Nat := 118140960795 + 1456289 * 2 ^ 59
def prefixEnd_1456289 : Nat := 4983230072969 + 3 ^ 40 * 1456289 * 2
def baseEnd_1456289 : Nat := 18463610589026123365189

theorem tailTrace_1456289 : CollatzResearch.WordTrace tailWord_1456289 prefixEnd_1456289 18463610589026123365189 := by
  unfold tailWord_1456289
  simp only [CollatzResearch.WordTrace]
  refine ⟨53115223421121142205147921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35410148947414094803431947 53115223421121142205147921)
  ·
    refine ⟨39836417565840856653860941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53115223421121142205147921 39836417565840856653860941)
    ·
      refine ⟨14938656587190321245197853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39836417565840856653860941 14938656587190321245197853)
      ·
        refine ⟨5601996220196370466949195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14938656587190321245197853 5601996220196370466949195)
        ·
          refine ⟨8402994330294555700423793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5601996220196370466949195 8402994330294555700423793)
          ·
            refine ⟨6302245747720916775317845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8402994330294555700423793 6302245747720916775317845)
            ·
              refine ⟨18463610589026123365189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6302245747720916775317845 18463610589026123365189)
              ·
                rfl

theorem cell22_1456289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 10].length) (baseStart_1456289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1456289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1456289 prefixEnd_1456289 := by exact prefixLift 1456289
  have htrace : WordTrace (prefixWord ++ tailWord_1456289) baseStart_1456289 baseEnd_1456289 := by
    simpa [prefixWord, tailWord_1456289, baseEnd_1456289] using wordTrace_append hprefix tailTrace_1456289
  have hstable : (prefixWord ++ tailWord_1456289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456289).length < 2 ^ (prefixWord ++ tailWord_1456289).sum := by decide
  have hdescent : baseEnd_1456289 < baseStart_1456289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456295 : List Nat := [1, 1, 6, 2, 3, 1, 1, 1, 6]
def baseStart_1456295 : Nat := 118140960795 + 1456295 * 2 ^ 59
def prefixEnd_1456295 : Nat := 4983230072969 + 3 ^ 40 * 1456295 * 2
def baseEnd_1456295 : Nat := 166173179942107771736695

theorem tailTrace_1456295 : CollatzResearch.WordTrace tailWord_1456295 prefixEnd_1456295 166173179942107771736695 := by
  unfold tailWord_1456295
  simp only [CollatzResearch.WordTrace]
  refine ⟨53115442259099405229866339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35410294839399603486577559 53115442259099405229866339)
  ·
    refine ⟨79673163388649107844799509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53115442259099405229866339 79673163388649107844799509)
    ·
      refine ⟨3734679533842926930224977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 79673163388649107844799509 3734679533842926930224977)
      ·
        refine ⟨2801009650382195197668733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3734679533842926930224977 2801009650382195197668733)
        ·
          refine ⟨1050378618893323199125775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2801009650382195197668733 1050378618893323199125775)
          ·
            refine ⟨1575567928339984798688663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1050378618893323199125775 1575567928339984798688663)
            ·
              refine ⟨2363351892509977198032995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1575567928339984798688663 2363351892509977198032995)
              ·
                refine ⟨3545027838764965797049493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2363351892509977198032995 3545027838764965797049493)
                ·
                  refine ⟨166173179942107771736695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3545027838764965797049493 166173179942107771736695)
                  ·
                    rfl

theorem cell22_1456295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 6].length) (baseStart_1456295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1456295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1456295 prefixEnd_1456295 := by exact prefixLift 1456295
  have htrace : WordTrace (prefixWord ++ tailWord_1456295) baseStart_1456295 baseEnd_1456295 := by
    simpa [prefixWord, tailWord_1456295, baseEnd_1456295] using wordTrace_append hprefix tailTrace_1456295
  have hstable : (prefixWord ++ tailWord_1456295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456295).length < 2 ^ (prefixWord ++ tailWord_1456295).sum := by decide
  have hdescent : baseEnd_1456295 < baseStart_1456295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456398 : List Nat := [4, 1, 1, 2, 1, 2, 3, 3, 1, 4]
def baseStart_1456398 : Nat := 118140960795 + 1456398 * 2 ^ 59
def prefixEnd_1456398 : Nat := 4983230072969 + 3 ^ 40 * 1456398 * 2
def baseEnd_1456398 : Nat := 498554798831265379884769

theorem tailTrace_1456398 : CollatzResearch.WordTrace tailWord_1456398 prefixEnd_1456398 498554798831265379884769 := by
  unfold tailWord_1456398
  simp only [CollatzResearch.WordTrace]
  refine ⟨6639899872215781727608231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35412799318484169213910565 6639899872215781727608231)
  ·
    refine ⟨9959849808323672591412347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6639899872215781727608231 9959849808323672591412347)
    ·
      refine ⟨14939774712485508887118521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9959849808323672591412347 14939774712485508887118521)
      ·
        refine ⟨11204831034364131665338891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14939774712485508887118521 11204831034364131665338891)
        ·
          refine ⟨16807246551546197498008337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11204831034364131665338891 16807246551546197498008337)
          ·
            refine ⟨12605434913659648123506253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16807246551546197498008337 12605434913659648123506253)
            ·
              refine ⟨4727038092622368046314845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12605434913659648123506253 4727038092622368046314845)
              ·
                refine ⟨1772639284733388017368067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4727038092622368046314845 1772639284733388017368067)
                ·
                  refine ⟨2658958927100082026052101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1772639284733388017368067 2658958927100082026052101)
                  ·
                    refine ⟨498554798831265379884769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2658958927100082026052101 498554798831265379884769)
                    ·
                      rfl

theorem cell22_1456398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_1456398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1456398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1456398 prefixEnd_1456398 := by exact prefixLift 1456398
  have htrace : WordTrace (prefixWord ++ tailWord_1456398) baseStart_1456398 baseEnd_1456398 := by
    simpa [prefixWord, tailWord_1456398, baseEnd_1456398] using wordTrace_append hprefix tailTrace_1456398
  have hstable : (prefixWord ++ tailWord_1456398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456398).length < 2 ^ (prefixWord ++ tailWord_1456398).sum := by decide
  have hdescent : baseEnd_1456398 < baseStart_1456398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
