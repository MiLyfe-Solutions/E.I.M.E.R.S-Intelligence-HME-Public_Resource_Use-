import V185TrunkScan23Chunk0460

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2727542 : List Nat := [5, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2]
def baseStart_2727542 : Nat := 118140960795 + 2727542 * 2 ^ 59
def prefixEnd_2727542 : Nat := 4983230072969 + 3 ^ 40 * 2727542 * 2
def baseEnd_2727542 : Nat := 1400540051325672713081269

theorem tailTrace_2727542 : CollatzResearch.WordTrace tailWord_2727542 prefixEnd_2727542 1400540051325672713081269 := by
  unfold tailWord_2727542
  simp only [CollatzResearch.WordTrace]
  refine ⟨6217601842786789745770055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66321086323059090621547253 6217601842786789745770055)
  ·
    refine ⟨9326402764180184618655083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6217601842786789745770055 9326402764180184618655083)
    ·
      refine ⟨13989604146270276927982625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9326402764180184618655083 13989604146270276927982625)
      ·
        refine ⟨10492203109702707695986969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13989604146270276927982625 10492203109702707695986969)
        ·
          refine ⟨7869152332277030771990227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10492203109702707695986969 7869152332277030771990227)
          ·
            refine ⟨11803728498415546157985341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7869152332277030771990227 11803728498415546157985341)
            ·
              refine ⟨4426398186905829809244503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11803728498415546157985341 4426398186905829809244503)
              ·
                refine ⟨6639597280358744713866755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4426398186905829809244503 6639597280358744713866755)
                ·
                  refine ⟨9959395920538117070800133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6639597280358744713866755 9959395920538117070800133)
                  ·
                    refine ⟨1867386735100896950775025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9959395920538117070800133 1867386735100896950775025)
                    ·
                      refine ⟨1400540051325672713081269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1867386735100896950775025 1400540051325672713081269)
                      ·
                        rfl

theorem cell23_2727542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_2727542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727542 prefixEnd_2727542 := by exact prefixLift 2727542
  have htrace : WordTrace (prefixWord ++ tailWord_2727542) baseStart_2727542 baseEnd_2727542 := by
    simpa [prefixWord, tailWord_2727542, baseEnd_2727542] using wordTrace_append hprefix tailTrace_2727542
  have hstable : (prefixWord ++ tailWord_2727542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727542).length < 2 ^ (prefixWord ++ tailWord_2727542).sum := by decide
  have hdescent : baseEnd_2727542 < baseStart_2727542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727561 : List Nat := [1, 2, 1, 1, 4, 1, 4, 1, 1, 7]
def baseStart_2727561 : Nat := 118140960795 + 2727561 * 2 ^ 59
def prefixEnd_2727561 : Nat := 4983230072969 + 3 ^ 40 * 2727561 * 2
def baseEnd_2727561 : Nat := 466849935819369379581227

theorem tailTrace_2727561 : CollatzResearch.WordTrace tailWord_2727561 prefixEnd_2727561 466849935819369379581227 := by
  unfold tailWord_2727561
  simp only [CollatzResearch.WordTrace]
  refine ⟨99482322471519802177262537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66321548314346534784841691 99482322471519802177262537)
  ·
    refine ⟨74611741853639851632946903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99482322471519802177262537 74611741853639851632946903)
    ·
      refine ⟨111917612780459777449420355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74611741853639851632946903 111917612780459777449420355)
      ·
        refine ⟨167876419170689666174130533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111917612780459777449420355 167876419170689666174130533)
        ·
          refine ⟨31476828594504312407649475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167876419170689666174130533 31476828594504312407649475)
          ·
            refine ⟨47215242891756468611474213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31476828594504312407649475 47215242891756468611474213)
            ·
              refine ⟨8852858042204337864651415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47215242891756468611474213 8852858042204337864651415)
              ·
                refine ⟨13279287063306506796977123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8852858042204337864651415 13279287063306506796977123)
                ·
                  refine ⟨19918930594959760195465685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13279287063306506796977123 19918930594959760195465685)
                  ·
                    refine ⟨466849935819369379581227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19918930594959760195465685 466849935819369379581227)
                    ·
                      rfl

theorem cell23_2727561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 7].length) (baseStart_2727561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727561 prefixEnd_2727561 := by exact prefixLift 2727561
  have htrace : WordTrace (prefixWord ++ tailWord_2727561) baseStart_2727561 baseEnd_2727561 := by
    simpa [prefixWord, tailWord_2727561, baseEnd_2727561] using wordTrace_append hprefix tailTrace_2727561
  have hstable : (prefixWord ++ tailWord_2727561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727561).length < 2 ^ (prefixWord ++ tailWord_2727561).sum := by decide
  have hdescent : baseEnd_2727561 < baseStart_2727561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727588 : List Nat := [2, 3, 1, 2, 2, 3, 1, 1, 1, 2, 5]
def baseStart_2727588 : Nat := 118140960795 + 2727588 * 2 ^ 59
def prefixEnd_2727588 : Nat := 4983230072969 + 3 ^ 40 * 2727588 * 2
def baseEnd_2727588 : Nat := 1400563671435779533106057

theorem tailTrace_2727588 : CollatzResearch.WordTrace tailWord_2727588 prefixEnd_2727588 1400563671435779533106057 := by
  unfold tailWord_2727588
  simp only [CollatzResearch.WordTrace]
  refine ⟨49741653621210992894247709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66322204828281323858996945 49741653621210992894247709)
  ·
    refine ⟨18653120107954122335342891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49741653621210992894247709 18653120107954122335342891)
    ·
      refine ⟨27979680161931183503014337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18653120107954122335342891 27979680161931183503014337)
      ·
        refine ⟨20984760121448387627260753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27979680161931183503014337 20984760121448387627260753)
        ·
          refine ⟨15738570091086290720445565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20984760121448387627260753 15738570091086290720445565)
          ·
            refine ⟨5901963784157359020167087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15738570091086290720445565 5901963784157359020167087)
            ·
              refine ⟨8852945676236038530250631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5901963784157359020167087 8852945676236038530250631)
              ·
                refine ⟨13279418514354057795375947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8852945676236038530250631 13279418514354057795375947)
                ·
                  refine ⟨19919127771531086693063921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13279418514354057795375947 19919127771531086693063921)
                  ·
                    refine ⟨14939345828648315019797941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19919127771531086693063921 14939345828648315019797941)
                    ·
                      refine ⟨1400563671435779533106057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14939345828648315019797941 1400563671435779533106057)
                      ·
                        rfl

theorem cell23_2727588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_2727588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727588 prefixEnd_2727588 := by exact prefixLift 2727588
  have htrace : WordTrace (prefixWord ++ tailWord_2727588) baseStart_2727588 baseEnd_2727588 := by
    simpa [prefixWord, tailWord_2727588, baseEnd_2727588] using wordTrace_append hprefix tailTrace_2727588
  have hstable : (prefixWord ++ tailWord_2727588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727588).length < 2 ^ (prefixWord ++ tailWord_2727588).sum := by decide
  have hdescent : baseEnd_2727588 < baseStart_2727588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727608 : List Nat := [2, 1, 2, 1, 2, 1, 1, 6, 3, 4]
def baseStart_2727608 : Nat := 118140960795 + 2727608 * 2 ^ 59
def prefixEnd_2727608 : Nat := 4983230072969 + 3 ^ 40 * 2727608 * 2
def baseEnd_2727608 : Nat := 466857980349623151618655

theorem tailTrace_2727608 : CollatzResearch.WordTrace tailWord_2727608 prefixEnd_2727608 466857980349623151618655 := by
  unfold tailWord_2727608
  simp only [CollatzResearch.WordTrace]
  refine ⟨49742018351174764602111739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66322691134899686136148985 49742018351174764602111739)
  ·
    refine ⟨74613027526762146903167609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49742018351174764602111739 74613027526762146903167609)
    ·
      refine ⟨55959770645071610177375707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74613027526762146903167609 55959770645071610177375707)
      ·
        refine ⟨83939655967607415266063561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55959770645071610177375707 83939655967607415266063561)
        ·
          refine ⟨62954741975705561449547671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83939655967607415266063561 62954741975705561449547671)
          ·
            refine ⟨94432112963558342174321507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62954741975705561449547671 94432112963558342174321507)
            ·
              refine ⟨141648169445337513261482261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94432112963558342174321507 141648169445337513261482261)
              ·
                refine ⟨6639757942750195934131981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 141648169445337513261482261 6639757942750195934131981)
                ·
                  refine ⟨2489909228531323475299493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6639757942750195934131981 2489909228531323475299493)
                  ·
                    refine ⟨466857980349623151618655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2489909228531323475299493 466857980349623151618655)
                    ·
                      rfl

theorem cell23_2727608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 3, 4].length) (baseStart_2727608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727608 prefixEnd_2727608 := by exact prefixLift 2727608
  have htrace : WordTrace (prefixWord ++ tailWord_2727608) baseStart_2727608 baseEnd_2727608 := by
    simpa [prefixWord, tailWord_2727608, baseEnd_2727608] using wordTrace_append hprefix tailTrace_2727608
  have hstable : (prefixWord ++ tailWord_2727608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727608).length < 2 ^ (prefixWord ++ tailWord_2727608).sum := by decide
  have hdescent : baseEnd_2727608 < baseStart_2727608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727611 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 4]
def baseStart_2727611 : Nat := 118140960795 + 2727611 * 2 ^ 59
def prefixEnd_2727611 : Nat := 4983230072969 + 3 ^ 40 * 2727611 * 2
def baseEnd_2727611 : Nat := 1400575481490832943118451

theorem tailTrace_2727611 : CollatzResearch.WordTrace tailWord_2727611 prefixEnd_2727611 1400575481490832943118451 := by
  unfold tailWord_2727611
  simp only [CollatzResearch.WordTrace]
  refine ⟨99484146121338660716582687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66322764080892440477721791 99484146121338660716582687)
  ·
    refine ⟨149226219182007991074874031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99484146121338660716582687 149226219182007991074874031)
    ·
      refine ⟨223839328773011986612311047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149226219182007991074874031 223839328773011986612311047)
      ·
        refine ⟨335758993159517979918466571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223839328773011986612311047 335758993159517979918466571)
        ·
          refine ⟨503638489739276969877699857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335758993159517979918466571 503638489739276969877699857)
          ·
            refine ⟨377728867304457727408274893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 503638489739276969877699857 377728867304457727408274893)
            ·
              refine ⟨141648325239171647778103085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 377728867304457727408274893 141648325239171647778103085)
              ·
                refine ⟨53118121964689367916788657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141648325239171647778103085 53118121964689367916788657)
                ·
                  refine ⟨39838591473517025937591493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53118121964689367916788657 39838591473517025937591493)
                  ·
                    refine ⟨7469735901284442363298405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39838591473517025937591493 7469735901284442363298405)
                    ·
                      refine ⟨1400575481490832943118451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7469735901284442363298405 1400575481490832943118451)
                      ·
                        rfl

theorem cell23_2727611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 4].length) (baseStart_2727611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727611 prefixEnd_2727611 := by exact prefixLift 2727611
  have htrace : WordTrace (prefixWord ++ tailWord_2727611) baseStart_2727611 baseEnd_2727611 := by
    simpa [prefixWord, tailWord_2727611, baseEnd_2727611] using wordTrace_append hprefix tailTrace_2727611
  have hstable : (prefixWord ++ tailWord_2727611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727611).length < 2 ^ (prefixWord ++ tailWord_2727611).sum := by decide
  have hdescent : baseEnd_2727611 < baseStart_2727611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727622 : List Nat := [6, 1, 2, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_2727622 : Nat := 118140960795 + 2727622 * 2 ^ 59
def prefixEnd_2727622 : Nat := 4983230072969 + 3 ^ 40 * 2727622 * 2
def baseEnd_2727622 : Nat := 1400581129778032400080901

theorem tailTrace_2727622 : CollatzResearch.WordTrace tailWord_2727622 prefixEnd_2727622 1400581129778032400080901 := by
  unfold tailWord_2727622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3108892103884337799851035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 66323031549532539730155413 3108892103884337799851035)
  ·
    refine ⟨4663338155826506699776553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3108892103884337799851035 4663338155826506699776553)
    ·
      refine ⟨3497503616869880024832415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4663338155826506699776553 3497503616869880024832415)
      ·
        refine ⟨5246255425304820037248623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3497503616869880024832415 5246255425304820037248623)
        ·
          refine ⟨7869383137957230055872935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5246255425304820037248623 7869383137957230055872935)
          ·
            refine ⟨11804074706935845083809403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7869383137957230055872935 11804074706935845083809403)
            ·
              refine ⟨17706112060403767625714105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11804074706935845083809403 17706112060403767625714105)
              ·
                refine ⟨13279584045302825719285579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17706112060403767625714105 13279584045302825719285579)
                ·
                  refine ⟨19919376067954238578928369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13279584045302825719285579 19919376067954238578928369)
                  ·
                    refine ⟨14939532050965678934196277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19919376067954238578928369 14939532050965678934196277)
                    ·
                      refine ⟨1400581129778032400080901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14939532050965678934196277 1400581129778032400080901)
                      ·
                        rfl

theorem cell23_2727622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_2727622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727622 prefixEnd_2727622 := by exact prefixLift 2727622
  have htrace : WordTrace (prefixWord ++ tailWord_2727622) baseStart_2727622 baseEnd_2727622 := by
    simpa [prefixWord, tailWord_2727622, baseEnd_2727622] using wordTrace_append hprefix tailTrace_2727622
  have hstable : (prefixWord ++ tailWord_2727622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727622).length < 2 ^ (prefixWord ++ tailWord_2727622).sum := by decide
  have hdescent : baseEnd_2727622 < baseStart_2727622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727642 : List Nat := [3, 1, 1, 2, 2, 4, 1, 4, 1, 4]
def baseStart_2727642 : Nat := 118140960795 + 2727642 * 2 ^ 59
def prefixEnd_2727642 : Nat := 4983230072969 + 3 ^ 40 * 2727642 * 2
def baseEnd_2727642 : Nat := 466863799797040773943603

theorem tailTrace_2727642 : CollatzResearch.WordTrace tailWord_2727642 prefixEnd_2727642 466863799797040773943603 := by
  unfold tailWord_2727642
  simp only [CollatzResearch.WordTrace]
  refine ⟨24871319196056588252740295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66323517856150902007307453 24871319196056588252740295)
  ·
    refine ⟨37306978794084882379110443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24871319196056588252740295 37306978794084882379110443)
    ·
      refine ⟨55960468191127323568665665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37306978794084882379110443 55960468191127323568665665)
      ·
        refine ⟨41970351143345492676499249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55960468191127323568665665 41970351143345492676499249)
        ·
          refine ⟨31477763357509119507374437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41970351143345492676499249 31477763357509119507374437)
          ·
            refine ⟨5902080629532959907632707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31477763357509119507374437 5902080629532959907632707)
            ·
              refine ⟨8853120944299439861449061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5902080629532959907632707 8853120944299439861449061)
              ·
                refine ⟨1659960177056144974021699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8853120944299439861449061 1659960177056144974021699)
                ·
                  refine ⟨2489940265584217461032549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1659960177056144974021699 2489940265584217461032549)
                  ·
                    refine ⟨466863799797040773943603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2489940265584217461032549 466863799797040773943603)
                    ·
                      rfl

theorem cell23_2727642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4, 1, 4].length) (baseStart_2727642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727642 prefixEnd_2727642 := by exact prefixLift 2727642
  have htrace : WordTrace (prefixWord ++ tailWord_2727642) baseStart_2727642 baseEnd_2727642 := by
    simpa [prefixWord, tailWord_2727642, baseEnd_2727642] using wordTrace_append hprefix tailTrace_2727642
  have hstable : (prefixWord ++ tailWord_2727642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727642).length < 2 ^ (prefixWord ++ tailWord_2727642).sum := by decide
  have hdescent : baseEnd_2727642 < baseStart_2727642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727665 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 5, 1, 3]
def baseStart_2727665 : Nat := 118140960795 + 2727665 * 2 ^ 59
def prefixEnd_2727665 : Nat := 4983230072969 + 3 ^ 40 * 2727665 * 2
def baseEnd_2727665 : Nat := 1400603209446175731843203

theorem tailTrace_2727665 : CollatzResearch.WordTrace tailWord_2727665 prefixEnd_2727665 1400603209446175731843203 := by
  unfold tailWord_2727665
  simp only [CollatzResearch.WordTrace]
  refine ⟨99486115663143027939048449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66324077108762018626032299 99486115663143027939048449)
  ·
    refine ⟨74614586747357270954286337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99486115663143027939048449 74614586747357270954286337)
    ·
      refine ⟨55960940060517953215714753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74614586747357270954286337 55960940060517953215714753)
      ·
        refine ⟨41970705045388464911786065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55960940060517953215714753 41970705045388464911786065)
        ·
          refine ⟨31478028784041348683839549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41970705045388464911786065 31478028784041348683839549)
          ·
            refine ⟨11804260794015505756439831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31478028784041348683839549 11804260794015505756439831)
            ·
              refine ⟨17706391191023258634659747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11804260794015505756439831 17706391191023258634659747)
              ·
                refine ⟨26559586786534887951989621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17706391191023258634659747 26559586786534887951989621)
                ·
                  refine ⟨2489961261237645745499027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26559586786534887951989621 2489961261237645745499027)
                  ·
                    refine ⟨3734941891856468618248541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2489961261237645745499027 3734941891856468618248541)
                    ·
                      refine ⟨1400603209446175731843203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3734941891856468618248541 1400603209446175731843203)
                      ·
                        rfl

theorem cell23_2727665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_2727665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727665 prefixEnd_2727665 := by exact prefixLift 2727665
  have htrace : WordTrace (prefixWord ++ tailWord_2727665) baseStart_2727665 baseEnd_2727665 := by
    simpa [prefixWord, tailWord_2727665, baseEnd_2727665] using wordTrace_append hprefix tailTrace_2727665
  have hstable : (prefixWord ++ tailWord_2727665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727665).length < 2 ^ (prefixWord ++ tailWord_2727665).sum := by decide
  have hdescent : baseEnd_2727665 < baseStart_2727665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727675 : List Nat := [1, 1, 1, 1, 1, 3, 1, 7, 2, 3, 2]
def baseStart_2727675 : Nat := 118140960795 + 2727675 * 2 ^ 59
def prefixEnd_2727675 : Nat := 4983230072969 + 3 ^ 40 * 2727675 * 2
def baseEnd_2727675 : Nat := 1400608344252720692718157

theorem tailTrace_2727675 : CollatzResearch.WordTrace tailWord_2727675 prefixEnd_2727675 1400608344252720692718157 := by
  unfold tailWord_2727675
  simp only [CollatzResearch.WordTrace]
  refine ⟨99486480393106799646912479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66324320262071199764608319 99486480393106799646912479)
  ·
    refine ⟨149229720589660199470368719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99486480393106799646912479 149229720589660199470368719)
    ·
      refine ⟨223844580884490299205553079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149229720589660199470368719 223844580884490299205553079)
      ·
        refine ⟨335766871326735448808329619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223844580884490299205553079 335766871326735448808329619)
        ·
          refine ⟨503650306990103173212494429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335766871326735448808329619 503650306990103173212494429)
          ·
            refine ⟨188868865121288689954685411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 503650306990103173212494429 188868865121288689954685411)
            ·
              refine ⟨283303297681933034932028117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188868865121288689954685411 283303297681933034932028117)
              ·
                refine ⟨6639921039420305506219409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 283303297681933034932028117 6639921039420305506219409)
                ·
                  refine ⟨4979940779565229129664557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6639921039420305506219409 4979940779565229129664557)
                  ·
                    refine ⟨1867477792336960923624209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4979940779565229129664557 1867477792336960923624209)
                    ·
                      refine ⟨1400608344252720692718157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1867477792336960923624209 1400608344252720692718157)
                      ·
                        rfl

theorem cell23_2727675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 3, 2].length) (baseStart_2727675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727675 prefixEnd_2727675 := by exact prefixLift 2727675
  have htrace : WordTrace (prefixWord ++ tailWord_2727675) baseStart_2727675 baseEnd_2727675 := by
    simpa [prefixWord, tailWord_2727675, baseEnd_2727675] using wordTrace_append hprefix tailTrace_2727675
  have hstable : (prefixWord ++ tailWord_2727675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727675).length < 2 ^ (prefixWord ++ tailWord_2727675).sum := by decide
  have hdescent : baseEnd_2727675 < baseStart_2727675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727682 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 5, 1, 3]
def baseStart_2727682 : Nat := 118140960795 + 2727682 * 2 ^ 59
def prefixEnd_2727682 : Nat := 4983230072969 + 3 ^ 40 * 2727682 * 2
def baseEnd_2727682 : Nat := 1400611938617302165330625

theorem tailTrace_2727682 : CollatzResearch.WordTrace tailWord_2727682 prefixEnd_2727682 1400611938617302165330625 := by
  unfold tailWord_2727682
  simp only [CollatzResearch.WordTrace]
  refine ⟨24871683926020359960604325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66324490469387626561611533 24871683926020359960604325)
  ·
    refine ⟨4663440736128817492613311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24871683926020359960604325 4663440736128817492613311)
    ·
      refine ⟨6995161104193226238919967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4663440736128817492613311 6995161104193226238919967)
      ·
        refine ⟨10492741656289839358379951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6995161104193226238919967 10492741656289839358379951)
        ·
          refine ⟨15739112484434759037569927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10492741656289839358379951 15739112484434759037569927)
          ·
            refine ⟨23608668726652138556354891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15739112484434759037569927 23608668726652138556354891)
            ·
              refine ⟨35413003089978207834532337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23608668726652138556354891 35413003089978207834532337)
              ·
                refine ⟨26559752317483655875899253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35413003089978207834532337 26559752317483655875899253)
                ·
                  refine ⟨2489976779764092738365555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26559752317483655875899253 2489976779764092738365555)
                  ·
                    refine ⟨3734965169646139107548333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2489976779764092738365555 3734965169646139107548333)
                    ·
                      refine ⟨1400611938617302165330625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3734965169646139107548333 1400611938617302165330625)
                      ·
                        rfl

theorem cell23_2727682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_2727682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727682 prefixEnd_2727682 := by exact prefixLift 2727682
  have htrace : WordTrace (prefixWord ++ tailWord_2727682) baseStart_2727682 baseEnd_2727682 := by
    simpa [prefixWord, tailWord_2727682, baseEnd_2727682] using wordTrace_append hprefix tailTrace_2727682
  have hstable : (prefixWord ++ tailWord_2727682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727682).length < 2 ^ (prefixWord ++ tailWord_2727682).sum := by decide
  have hdescent : baseEnd_2727682 < baseStart_2727682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727693 : List Nat := [1, 7, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_2727693 : Nat := 118140960795 + 2727693 * 2 ^ 59
def prefixEnd_2727693 : Nat := 4983230072969 + 3 ^ 40 * 2727693 * 2
def baseEnd_2727693 : Nat := 466872528968167207431025

theorem tailTrace_2727693 : CollatzResearch.WordTrace tailWord_2727693 prefixEnd_2727693 466872528968167207431025 := by
  unfold tailWord_2727693
  simp only [CollatzResearch.WordTrace]
  refine ⟨99487136907041588721067733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66324757938027725814045155 99487136907041588721067733)
  ·
    refine ⟨2331729771258787235650025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 99487136907041588721067733 2331729771258787235650025)
    ·
      refine ⟨1748797328444090426737519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2331729771258787235650025 1748797328444090426737519)
      ·
        refine ⟨2623195992666135640106279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1748797328444090426737519 2623195992666135640106279)
        ·
          refine ⟨3934793988999203460159419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2623195992666135640106279 3934793988999203460159419)
          ·
            refine ⟨5902190983498805190239129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3934793988999203460159419 5902190983498805190239129)
            ·
              refine ⟨4426643237624103892679347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5902190983498805190239129 4426643237624103892679347)
              ·
                refine ⟨6639964856436155839019021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4426643237624103892679347 6639964856436155839019021)
                ·
                  refine ⟨2489986821163558439632133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6639964856436155839019021 2489986821163558439632133)
                  ·
                    refine ⟨466872528968167207431025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2489986821163558439632133 466872528968167207431025)
                    ·
                      rfl

theorem cell23_2727693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_2727693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727693 prefixEnd_2727693 := by exact prefixLift 2727693
  have htrace : WordTrace (prefixWord ++ tailWord_2727693) baseStart_2727693 baseEnd_2727693 := by
    simpa [prefixWord, tailWord_2727693, baseEnd_2727693] using wordTrace_append hprefix tailTrace_2727693
  have hstable : (prefixWord ++ tailWord_2727693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727693).length < 2 ^ (prefixWord ++ tailWord_2727693).sum := by decide
  have hdescent : baseEnd_2727693 < baseStart_2727693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727715 : List Nat := [1, 1, 1, 4, 2, 1, 2, 5, 2, 4]
def baseStart_2727715 : Nat := 118140960795 + 2727715 * 2 ^ 59
def prefixEnd_2727715 : Nat := 4983230072969 + 3 ^ 40 * 2727715 * 2
def baseEnd_2727715 : Nat := 466876294492966845405991

theorem tailTrace_2727715 : CollatzResearch.WordTrace tailWord_2727715 prefixEnd_2727715 466876294492966845405991 := by
  unfold tailWord_2727715
  simp only [CollatzResearch.WordTrace]
  refine ⟨99487939312961886478368599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66325292875307924318912399 99487939312961886478368599)
  ·
    refine ⟨149231908969442829717552899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99487939312961886478368599 149231908969442829717552899)
    ·
      refine ⟨223847863454164244576329349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149231908969442829717552899 223847863454164244576329349)
      ·
        refine ⟨41971474397655795858061753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 223847863454164244576329349 41971474397655795858061753)
        ·
          refine ⟨31478605798241846893546315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41971474397655795858061753 31478605798241846893546315)
          ·
            refine ⟨47217908697362770340319473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31478605798241846893546315 47217908697362770340319473)
            ·
              refine ⟨35413431523022077755239605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47217908697362770340319473 35413431523022077755239605)
              ·
                refine ⟨3320009205283319789553713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35413431523022077755239605 3320009205283319789553713)
                ·
                  refine ⟨2490006903962489842165285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3320009205283319789553713 2490006903962489842165285)
                  ·
                    refine ⟨466876294492966845405991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2490006903962489842165285 466876294492966845405991)
                    ·
                      rfl

theorem cell23_2727715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2, 4].length) (baseStart_2727715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727715 prefixEnd_2727715 := by exact prefixLift 2727715
  have htrace : WordTrace (prefixWord ++ tailWord_2727715) baseStart_2727715 baseEnd_2727715 := by
    simpa [prefixWord, tailWord_2727715, baseEnd_2727715] using wordTrace_append hprefix tailTrace_2727715
  have hstable : (prefixWord ++ tailWord_2727715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727715).length < 2 ^ (prefixWord ++ tailWord_2727715).sum := by decide
  have hdescent : baseEnd_2727715 < baseStart_2727715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727732 : List Nat := [2, 5, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_2727732 : Nat := 118140960795 + 2727732 * 2 ^ 59
def prefixEnd_2727732 : Nat := 4983230072969 + 3 ^ 40 * 2727732 * 2
def baseEnd_2727732 : Nat := 466879204216675656568465

theorem tailTrace_2727732 : CollatzResearch.WordTrace tailWord_2727732 prefixEnd_2727732 466879204216675656568465 := by
  unfold tailWord_2727732
  simp only [CollatzResearch.WordTrace]
  refine ⟨49744279676950149190868725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66325706235933532254491633 49744279676950149190868725)
  ·
    refine ⟨4663526219714076486643943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49744279676950149190868725 4663526219714076486643943)
    ·
      refine ⟨6995289329571114729965915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4663526219714076486643943 6995289329571114729965915)
      ·
        refine ⟨10492933994356672094948873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6995289329571114729965915 10492933994356672094948873)
        ·
          refine ⟨7869700495767504071211655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10492933994356672094948873 7869700495767504071211655)
          ·
            refine ⟨11804550743651256106817483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7869700495767504071211655 11804550743651256106817483)
            ·
              refine ⟨17706826115476884160226225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11804550743651256106817483 17706826115476884160226225)
              ·
                refine ⟨13280119586607663120169669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17706826115476884160226225 13280119586607663120169669)
                ·
                  refine ⟨2490022422488936835031813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13280119586607663120169669 2490022422488936835031813)
                  ·
                    refine ⟨466879204216675656568465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2490022422488936835031813 466879204216675656568465)
                    ·
                      rfl

theorem cell23_2727732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_2727732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727732 prefixEnd_2727732 := by exact prefixLift 2727732
  have htrace : WordTrace (prefixWord ++ tailWord_2727732) baseStart_2727732 baseEnd_2727732 := by
    simpa [prefixWord, tailWord_2727732, baseEnd_2727732] using wordTrace_append hprefix tailTrace_2727732
  have hstable : (prefixWord ++ tailWord_2727732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727732).length < 2 ^ (prefixWord ++ tailWord_2727732).sum := by decide
  have hdescent : baseEnd_2727732 < baseStart_2727732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727733 : List Nat := [1, 3, 3, 1, 5, 1, 1, 3, 1, 1, 3]
def baseStart_2727733 : Nat := 118140960795 + 2727733 * 2 ^ 59
def prefixEnd_2727733 : Nat := 4983230072969 + 3 ^ 40 * 2727733 * 2
def baseEnd_2727733 : Nat := 1400638126130681465792891

theorem tailTrace_2727733 : CollatzResearch.WordTrace tailWord_2727733 prefixEnd_2727733 1400638126130681465792891 := by
  unfold tailWord_2727733
  simp only [CollatzResearch.WordTrace]
  refine ⟨99488595826896675552523853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66325730551264450368349235 99488595826896675552523853)
  ·
    refine ⟨37308223435086253332196445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99488595826896675552523853 37308223435086253332196445)
    ·
      refine ⟨13990583788157344999573667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37308223435086253332196445 13990583788157344999573667)
      ·
        refine ⟨20985875682236017499360501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13990583788157344999573667 20985875682236017499360501)
        ·
          refine ⟨1967425845209626640565047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20985875682236017499360501 1967425845209626640565047)
          ·
            refine ⟨2951138767814439960847571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1967425845209626640565047 2951138767814439960847571)
            ·
              refine ⟨4426708151721659941271357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2951138767814439960847571 4426708151721659941271357)
              ·
                refine ⟨1660015556895622477976759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4426708151721659941271357 1660015556895622477976759)
                ·
                  refine ⟨2490023335343433716965139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1660015556895622477976759 2490023335343433716965139)
                  ·
                    refine ⟨3735035003015150575447709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2490023335343433716965139 3735035003015150575447709)
                    ·
                      refine ⟨1400638126130681465792891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3735035003015150575447709 1400638126130681465792891)
                      ·
                        rfl

theorem cell23_2727733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_2727733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727733 prefixEnd_2727733 := by exact prefixLift 2727733
  have htrace : WordTrace (prefixWord ++ tailWord_2727733) baseStart_2727733 baseEnd_2727733 := by
    simpa [prefixWord, tailWord_2727733, baseEnd_2727733] using wordTrace_append hprefix tailTrace_2727733
  have hstable : (prefixWord ++ tailWord_2727733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727733).length < 2 ^ (prefixWord ++ tailWord_2727733).sum := by decide
  have hdescent : baseEnd_2727733 < baseStart_2727733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727742 : List Nat := [4, 2, 1, 2, 2, 2, 2, 1, 1, 1, 5]
def baseStart_2727742 : Nat := 118140960795 + 2727742 * 2 ^ 59
def prefixEnd_2727742 : Nat := 4983230072969 + 3 ^ 40 * 2727742 * 2
def baseEnd_2727742 : Nat := 1400642747456571930580349

theorem tailTrace_2727742 : CollatzResearch.WordTrace tailWord_2727742 prefixEnd_2727742 1400642747456571930580349 := by
  unfold tailWord_2727742
  simp only [CollatzResearch.WordTrace]
  refine ⟨12436115510483008761200185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66325949389242713393067653 12436115510483008761200185)
  ·
    refine ⟨9327086632862256570900139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12436115510483008761200185 9327086632862256570900139)
    ·
      refine ⟨13990629949293384856350209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9327086632862256570900139 13990629949293384856350209)
      ·
        refine ⟨10492972461970038642262657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13990629949293384856350209 10492972461970038642262657)
        ·
          refine ⟨7869729346477528981696993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10492972461970038642262657 7869729346477528981696993)
          ·
            refine ⟨5902297009858146736272745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7869729346477528981696993 5902297009858146736272745)
            ·
              refine ⟨4426722757393610052204559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5902297009858146736272745 4426722757393610052204559)
              ·
                refine ⟨6640084136090415078306839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4426722757393610052204559 6640084136090415078306839)
                ·
                  refine ⟨9960126204135622617460259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6640084136090415078306839 9960126204135622617460259)
                  ·
                    refine ⟨14940189306203433926190389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9960126204135622617460259 14940189306203433926190389)
                    ·
                      refine ⟨1400642747456571930580349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14940189306203433926190389 1400642747456571930580349)
                      ·
                        rfl

theorem cell23_2727742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_2727742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727742 prefixEnd_2727742 := by exact prefixLift 2727742
  have htrace : WordTrace (prefixWord ++ tailWord_2727742) baseStart_2727742 baseEnd_2727742 := by
    simpa [prefixWord, tailWord_2727742, baseEnd_2727742] using wordTrace_append hprefix tailTrace_2727742
  have hstable : (prefixWord ++ tailWord_2727742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727742).length < 2 ^ (prefixWord ++ tailWord_2727742).sum := by decide
  have hdescent : baseEnd_2727742 < baseStart_2727742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727750 : List Nat := [6, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3]
def baseStart_2727750 : Nat := 118140960795 + 2727750 * 2 ^ 59
def prefixEnd_2727750 : Nat := 4983230072969 + 3 ^ 40 * 2727750 * 2
def baseEnd_2727750 : Nat := 1400646855301807899280313

theorem tailTrace_2727750 : CollatzResearch.WordTrace tailWord_2727750 prefixEnd_2727750 1400646855301807899280313 := by
  unfold tailWord_2727750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3109037995869846482996647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 66326143911890058303928469 3109037995869846482996647)
  ·
    refine ⟨4663556993804769724494971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3109037995869846482996647 4663556993804769724494971)
    ·
      refine ⟨6995335490707154586742457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4663556993804769724494971 6995335490707154586742457)
      ·
        refine ⟨5246501618030365940056843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6995335490707154586742457 5246501618030365940056843)
        ·
          refine ⟨7869752427045548910085265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5246501618030365940056843 7869752427045548910085265)
          ·
            refine ⟨5902314320284161682563949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7869752427045548910085265 5902314320284161682563949)
            ·
              refine ⟨2213367870106560630961481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5902314320284161682563949 2213367870106560630961481)
              ·
                refine ⟨1660025902579920473221111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2213367870106560630961481 1660025902579920473221111)
                ·
                  refine ⟨2490038853869880709831667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1660025902579920473221111 2490038853869880709831667)
                  ·
                    refine ⟨3735058280804821064747501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2490038853869880709831667 3735058280804821064747501)
                    ·
                      refine ⟨1400646855301807899280313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3735058280804821064747501 1400646855301807899280313)
                      ·
                        rfl

theorem cell23_2727750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_2727750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727750 prefixEnd_2727750 := by exact prefixLift 2727750
  have htrace : WordTrace (prefixWord ++ tailWord_2727750) baseStart_2727750 baseEnd_2727750 := by
    simpa [prefixWord, tailWord_2727750, baseEnd_2727750] using wordTrace_append hprefix tailTrace_2727750
  have hstable : (prefixWord ++ tailWord_2727750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727750).length < 2 ^ (prefixWord ++ tailWord_2727750).sum := by decide
  have hdescent : baseEnd_2727750 < baseStart_2727750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727756 : List Nat := [2, 2, 1, 3, 4, 2, 1, 1, 3, 2, 2]
def baseStart_2727756 : Nat := 118140960795 + 2727756 * 2 ^ 59
def prefixEnd_2727756 : Nat := 4983230072969 + 3 ^ 40 * 2727756 * 2
def baseEnd_2727756 : Nat := 1400649936185734875805285

theorem tailTrace_2727756 : CollatzResearch.WordTrace tailWord_2727756 prefixEnd_2727756 1400649936185734875805285 := by
  unfold tailWord_2727756
  simp only [CollatzResearch.WordTrace]
  refine ⟨49744717352906675240305561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66326289803875566987074081 49744717352906675240305561)
  ·
    refine ⟨37308538014680006430229171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49744717352906675240305561 37308538014680006430229171)
    ·
      refine ⟨55962807022020009645343757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37308538014680006430229171 55962807022020009645343757)
      ·
        refine ⟨20986052633257503617003909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55962807022020009645343757 20986052633257503617003909)
        ·
          refine ⟨3934884868735781928188233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20986052633257503617003909 3934884868735781928188233)
          ·
            refine ⟨2951163651551836446141175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3934884868735781928188233 2951163651551836446141175)
            ·
              refine ⟨4426745477327754669211763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2951163651551836446141175 4426745477327754669211763)
              ·
                refine ⟨6640118215991632003817645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4426745477327754669211763 6640118215991632003817645)
                ·
                  refine ⟨2490044330996862001431617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6640118215991632003817645 2490044330996862001431617)
                  ·
                    refine ⟨1867533248247646501073713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2490044330996862001431617 1867533248247646501073713)
                    ·
                      refine ⟨1400649936185734875805285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1867533248247646501073713 1400649936185734875805285)
                      ·
                        rfl

theorem cell23_2727756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_2727756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727756 prefixEnd_2727756 := by exact prefixLift 2727756
  have htrace : WordTrace (prefixWord ++ tailWord_2727756) baseStart_2727756 baseEnd_2727756 := by
    simpa [prefixWord, tailWord_2727756, baseEnd_2727756] using wordTrace_append hprefix tailTrace_2727756
  have hstable : (prefixWord ++ tailWord_2727756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727756).length < 2 ^ (prefixWord ++ tailWord_2727756).sum := by decide
  have hdescent : baseEnd_2727756 < baseStart_2727756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727806 : List Nat := [4, 2, 3, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_2727806 : Nat := 118140960795 + 2727806 * 2 ^ 59
def prefixEnd_2727806 : Nat := 4983230072969 + 3 ^ 40 * 2727806 * 2
def baseEnd_2727806 : Nat := 1400675610218459680180055

theorem tailTrace_2727806 : CollatzResearch.WordTrace tailWord_2727806 prefixEnd_2727806 1400675610218459680180055 := by
  unfold tailWord_2727806
  simp only [CollatzResearch.WordTrace]
  refine ⟨12436407294454026127491409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66327505570421472679954181 12436407294454026127491409)
  ·
    refine ⟨9327305470840519595618557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12436407294454026127491409 9327305470840519595618557)
    ·
      refine ⟨3497739551565194848356959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9327305470840519595618557 3497739551565194848356959)
      ·
        refine ⟨5246609327347792272535439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3497739551565194848356959 5246609327347792272535439)
        ·
          refine ⟨7869913991021688408803159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5246609327347792272535439 7869913991021688408803159)
          ·
            refine ⟨11804870986532532613204739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7869913991021688408803159 11804870986532532613204739)
            ·
              refine ⟨17707306479798798919807109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11804870986532532613204739 17707306479798798919807109)
              ·
                refine ⟨3320119964962274797463833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17707306479798798919807109 3320119964962274797463833)
                ·
                  refine ⟨2490089973721706098097875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3320119964962274797463833 2490089973721706098097875)
                  ·
                    refine ⟨3735134960582559147146813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2490089973721706098097875 3735134960582559147146813)
                    ·
                      refine ⟨1400675610218459680180055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3735134960582559147146813 1400675610218459680180055)
                      ·
                        rfl

theorem cell23_2727806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_2727806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727806 prefixEnd_2727806 := by exact prefixLift 2727806
  have htrace : WordTrace (prefixWord ++ tailWord_2727806) baseStart_2727806 baseEnd_2727806 := by
    simpa [prefixWord, tailWord_2727806, baseEnd_2727806] using wordTrace_append hprefix tailTrace_2727806
  have hstable : (prefixWord ++ tailWord_2727806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727806).length < 2 ^ (prefixWord ++ tailWord_2727806).sum := by decide
  have hdescent : baseEnd_2727806 < baseStart_2727806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727829 : List Nat := [1, 3, 2, 1, 1, 3, 1, 5, 2, 2, 2]
def baseStart_2727829 : Nat := 118140960795 + 2727829 * 2 ^ 59
def prefixEnd_2727829 : Nat := 4983230072969 + 3 ^ 40 * 2727829 * 2
def baseEnd_2727829 : Nat := 1400687420273513090192449

theorem tailTrace_2727829 : CollatzResearch.WordTrace tailWord_2727829 prefixEnd_2727829 1400687420273513090192449 := by
  unfold tailWord_2727829
  simp only [CollatzResearch.WordTrace]
  refine ⟨99492097234548883948018541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66328064823032589298679027 99492097234548883948018541)
  ·
    refine ⟨37309536462955831480506953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99492097234548883948018541 37309536462955831480506953)
    ·
      refine ⟨27982152347216873610380215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37309536462955831480506953 27982152347216873610380215)
      ·
        refine ⟨41973228520825310415570323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27982152347216873610380215 41973228520825310415570323)
        ·
          refine ⟨62959842781237965623355485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41973228520825310415570323 62959842781237965623355485)
          ·
            refine ⟨23609941042964237108758307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62959842781237965623355485 23609941042964237108758307)
            ·
              refine ⟨35414911564446355663137461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23609941042964237108758307 35414911564446355663137461)
              ·
                refine ⟨3320147959166845843419137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35414911564446355663137461 3320147959166845843419137)
                ·
                  refine ⟨2490110969375134382564353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3320147959166845843419137 2490110969375134382564353)
                  ·
                    refine ⟨1867583227031350786923265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2490110969375134382564353 1867583227031350786923265)
                    ·
                      refine ⟨1400687420273513090192449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1867583227031350786923265 1400687420273513090192449)
                      ·
                        rfl

theorem cell23_2727829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2, 2, 2].length) (baseStart_2727829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727829 prefixEnd_2727829 := by exact prefixLift 2727829
  have htrace : WordTrace (prefixWord ++ tailWord_2727829) baseStart_2727829 baseEnd_2727829 := by
    simpa [prefixWord, tailWord_2727829, baseEnd_2727829] using wordTrace_append hprefix tailTrace_2727829
  have hstable : (prefixWord ++ tailWord_2727829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727829).length < 2 ^ (prefixWord ++ tailWord_2727829).sum := by decide
  have hdescent : baseEnd_2727829 < baseStart_2727829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727865 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 4, 5]
def baseStart_2727865 : Nat := 118140960795 + 2727865 * 2 ^ 59
def prefixEnd_2727865 : Nat := 4983230072969 + 3 ^ 40 * 2727865 * 2
def baseEnd_2727865 : Nat := 466901968525691649780761

theorem tailTrace_2727865 : CollatzResearch.WordTrace tailWord_2727865 prefixEnd_2727865 466901968525691649780761 := by
  unfold tailWord_2727865
  simp only [CollatzResearch.WordTrace]
  refine ⟨99493410262418462096329049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66328940174945641397552699 99493410262418462096329049)
  ·
    refine ⟨74620057696813846572246787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99493410262418462096329049 74620057696813846572246787)
    ·
      refine ⟨111930086545220769858370181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74620057696813846572246787 111930086545220769858370181)
      ·
        refine ⟨20986891227228894348444409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111930086545220769858370181 20986891227228894348444409)
        ·
          refine ⟨15740168420421670761333307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20986891227228894348444409 15740168420421670761333307)
          ·
            refine ⟨23610252630632506141999961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15740168420421670761333307 23610252630632506141999961)
            ·
              refine ⟨17707689472974379606499971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23610252630632506141999961 17707689472974379606499971)
              ·
                refine ⟨26561534209461569409749957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17707689472974379606499971 26561534209461569409749957)
                ·
                  refine ⟨4980287664274044264328117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26561534209461569409749957 4980287664274044264328117)
                  ·
                    refine ⟨466901968525691649780761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4980287664274044264328117 466901968525691649780761)
                    ·
                      rfl

theorem cell23_2727865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 5].length) (baseStart_2727865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727865 prefixEnd_2727865 := by exact prefixLift 2727865
  have htrace : WordTrace (prefixWord ++ tailWord_2727865) baseStart_2727865 baseEnd_2727865 := by
    simpa [prefixWord, tailWord_2727865, baseEnd_2727865] using wordTrace_append hprefix tailTrace_2727865
  have hstable : (prefixWord ++ tailWord_2727865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727865).length < 2 ^ (prefixWord ++ tailWord_2727865).sum := by decide
  have hdescent : baseEnd_2727865 < baseStart_2727865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727929 : List Nat := [1, 2, 1, 3, 1, 6, 1, 1, 3, 4]
def baseStart_2727929 : Nat := 118140960795 + 2727929 * 2 ^ 59
def prefixEnd_2727929 : Nat := 4983230072969 + 3 ^ 40 * 2727929 * 2
def baseEnd_2727929 : Nat := 466912922779654232980663

theorem tailTrace_2727929 : CollatzResearch.WordTrace tailWord_2727929 prefixEnd_2727929 466912922779654232980663 := by
  unfold tailWord_2727929
  simp only [CollatzResearch.WordTrace]
  refine ⟨99495744534186601026658841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66330496356124400684439227 99495744534186601026658841)
  ·
    refine ⟨74621808400639950769994131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99495744534186601026658841 74621808400639950769994131)
    ·
      refine ⟨111932712600959926154991197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74621808400639950769994131 111932712600959926154991197)
      ·
        refine ⟨41974767225359972308121699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111932712600959926154991197 41974767225359972308121699)
        ·
          refine ⟨62962150838039958462182549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41974767225359972308121699 62962150838039958462182549)
          ·
            refine ⟨2951350820533123052914807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62962150838039958462182549 2951350820533123052914807)
            ·
              refine ⟨4427026230799684579372211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2951350820533123052914807 4427026230799684579372211)
              ·
                refine ⟨6640539346199526869058317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4427026230799684579372211 6640539346199526869058317)
                ·
                  refine ⟨2490202254824822575896869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6640539346199526869058317 2490202254824822575896869)
                  ·
                    refine ⟨466912922779654232980663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2490202254824822575896869 466912922779654232980663)
                    ·
                      rfl

theorem cell23_2727929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3, 4].length) (baseStart_2727929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727929 prefixEnd_2727929 := by exact prefixLift 2727929
  have htrace : WordTrace (prefixWord ++ tailWord_2727929) baseStart_2727929 baseEnd_2727929 := by
    simpa [prefixWord, tailWord_2727929, baseEnd_2727929] using wordTrace_append hprefix tailTrace_2727929
  have hstable : (prefixWord ++ tailWord_2727929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727929).length < 2 ^ (prefixWord ++ tailWord_2727929).sum := by decide
  have hdescent : baseEnd_2727929 < baseStart_2727929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727976 : List Nat := [2, 1, 5, 3, 1, 1, 2, 2, 6]
def baseStart_2727976 : Nat := 118140960795 + 2727976 * 2 ^ 59
def prefixEnd_2727976 : Nat := 4983230072969 + 3 ^ 40 * 2727976 * 2
def baseEnd_2727976 : Nat := 155640322436636001672697

theorem tailTrace_2727976 : CollatzResearch.WordTrace tailWord_2727976 prefixEnd_2727976 155640322436636001672697 := by
  unfold tailWord_2727976
  simp only [CollatzResearch.WordTrace]
  refine ⟨49748729382508164026809891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66331639176677552035746521 49748729382508164026809891)
  ·
    refine ⟨74623094073762246040214837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49748729382508164026809891 74623094073762246040214837)
    ·
      refine ⟨6995915069415210566270141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74623094073762246040214837 6995915069415210566270141)
      ·
        refine ⟨2623468151030703962351303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6995915069415210566270141 2623468151030703962351303)
        ·
          refine ⟨3935202226546055943526955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2623468151030703962351303 3935202226546055943526955)
          ·
            refine ⟨5902803339819083915290433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3935202226546055943526955 5902803339819083915290433)
            ·
              refine ⟨4427102504864312936467825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5902803339819083915290433 4427102504864312936467825)
              ·
                refine ⟨3320326878648234702350869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4427102504864312936467825 3320326878648234702350869)
                ·
                  refine ⟨155640322436636001672697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3320326878648234702350869 155640322436636001672697)
                  ·
                    rfl

theorem cell23_2727976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 6].length) (baseStart_2727976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727976 prefixEnd_2727976 := by exact prefixLift 2727976
  have htrace : WordTrace (prefixWord ++ tailWord_2727976) baseStart_2727976 baseEnd_2727976 := by
    simpa [prefixWord, tailWord_2727976, baseEnd_2727976] using wordTrace_append hprefix tailTrace_2727976
  have hstable : (prefixWord ++ tailWord_2727976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727976).length < 2 ^ (prefixWord ++ tailWord_2727976).sum := by decide
  have hdescent : baseEnd_2727976 < baseStart_2727976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728006 : List Nat := [6, 1, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_2728006 : Nat := 118140960795 + 2728006 * 2 ^ 59
def prefixEnd_2728006 : Nat := 4983230072969 + 3 ^ 40 * 2728006 * 2
def baseEnd_2728006 : Nat := 466926102116452965893045

theorem tailTrace_2728006 : CollatzResearch.WordTrace tailWord_2728006 prefixEnd_2728006 466926102116452965893045 := by
  unfold tailWord_2728006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3109329779840863849287871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 66332368636605095451474581 3109329779840863849287871)
  ·
    refine ⟨4663994669761295773931807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3109329779840863849287871 4663994669761295773931807)
    ·
      refine ⟨6995992004641943660897711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4663994669761295773931807 6995992004641943660897711)
      ·
        refine ⟨10493988006962915491346567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6995992004641943660897711 10493988006962915491346567)
        ·
          refine ⟨15740982010444373237019851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10493988006962915491346567 15740982010444373237019851)
          ·
            refine ⟨23611473015666559855529777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15740982010444373237019851 23611473015666559855529777)
            ·
              refine ⟨17708604761749919891647333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23611473015666559855529777 17708604761749919891647333)
              ·
                refine ⟨3320363392828109979683875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17708604761749919891647333 3320363392828109979683875)
                ·
                  refine ⟨4980545089242164969525813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3320363392828109979683875 4980545089242164969525813)
                  ·
                    refine ⟨466926102116452965893045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4980545089242164969525813 466926102116452965893045)
                    ·
                      rfl

theorem cell23_2728006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_2728006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728006 prefixEnd_2728006 := by exact prefixLift 2728006
  have htrace : WordTrace (prefixWord ++ tailWord_2728006) baseStart_2728006 baseEnd_2728006 := by
    simpa [prefixWord, tailWord_2728006, baseEnd_2728006] using wordTrace_append hprefix tailTrace_2728006
  have hstable : (prefixWord ++ tailWord_2728006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728006).length < 2 ^ (prefixWord ++ tailWord_2728006).sum := by decide
  have hdescent : baseEnd_2728006 < baseStart_2728006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728094 : List Nat := [4, 3, 1, 1, 3, 1, 3, 2, 1, 2, 2]
def baseStart_2728094 : Nat := 118140960795 + 2728094 * 2 ^ 59
def prefixEnd_2728094 : Nat := 4983230072969 + 3 ^ 40 * 2728094 * 2
def baseEnd_2728094 : Nat := 1400823492646954553378731

theorem tailTrace_2728094 : CollatzResearch.WordTrace tailWord_2728094 prefixEnd_2728094 1400823492646954553378731 := by
  unfold tailWord_2728094
  simp only [CollatzResearch.WordTrace]
  refine ⟨12437720322323604275801917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66334508385725889470943557 12437720322323604275801917)
  ·
    refine ⟨4664145120871351603425719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12437720322323604275801917 4664145120871351603425719)
    ·
      refine ⟨6996217681307027405138579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4664145120871351603425719 6996217681307027405138579)
      ·
        refine ⟨10494326521960541107707869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6996217681307027405138579 10494326521960541107707869)
        ·
          refine ⟨3935372445735202915390451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10494326521960541107707869 3935372445735202915390451)
          ·
            refine ⟨5903058668602804373085677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3935372445735202915390451 5903058668602804373085677)
            ·
              refine ⟨2213647000726051639907129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5903058668602804373085677 2213647000726051639907129)
              ·
                refine ⟨1660235250544538729930347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2213647000726051639907129 1660235250544538729930347)
                ·
                  refine ⟨2490352875816808094895521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1660235250544538729930347 2490352875816808094895521)
                  ·
                    refine ⟨1867764656862606071171641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2490352875816808094895521 1867764656862606071171641)
                    ·
                      refine ⟨1400823492646954553378731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1867764656862606071171641 1400823492646954553378731)
                      ·
                        rfl

theorem cell23_2728094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_2728094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728094 prefixEnd_2728094 := by exact prefixLift 2728094
  have htrace : WordTrace (prefixWord ++ tailWord_2728094) baseStart_2728094 baseEnd_2728094 := by
    simpa [prefixWord, tailWord_2728094, baseEnd_2728094] using wordTrace_append hprefix tailTrace_2728094
  have hstable : (prefixWord ++ tailWord_2728094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728094).length < 2 ^ (prefixWord ++ tailWord_2728094).sum := by decide
  have hdescent : baseEnd_2728094 < baseStart_2728094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728122 : List Nat := [3, 1, 1, 1, 2, 2, 2, 4, 7]
def baseStart_2728122 : Nat := 118140960795 + 2728122 * 2 ^ 59
def prefixEnd_2728122 : Nat := 4983230072969 + 3 ^ 40 * 2728122 * 2
def baseEnd_2728122 : Nat := 155648652233920049314289

theorem tailTrace_2728122 : CollatzResearch.WordTrace tailWord_2728122 prefixEnd_2728122 155648652233920049314289 := by
  unfold tailWord_2728122
  simp only [CollatzResearch.WordTrace]
  refine ⟨24875695955621848747108655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66335189214991596658956413 24875695955621848747108655)
  ·
    refine ⟨37313543933432773120662983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24875695955621848747108655 37313543933432773120662983)
    ·
      refine ⟨55970315900149159680994475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37313543933432773120662983 55970315900149159680994475)
      ·
        refine ⟨83955473850223739521491713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55970315900149159680994475 83955473850223739521491713)
        ·
          refine ⟨62966605387667804641118785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83955473850223739521491713 62966605387667804641118785)
          ·
            refine ⟨47224954040750853480839089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62966605387667804641118785 47224954040750853480839089)
            ·
              refine ⟨35418715530563140110629317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47224954040750853480839089 35418715530563140110629317)
              ·
                refine ⟨6641009161980588770742997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35418715530563140110629317 6641009161980588770742997)
                ·
                  refine ⟨155648652233920049314289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6641009161980588770742997 155648652233920049314289)
                  ·
                    rfl

theorem cell23_2728122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 7].length) (baseStart_2728122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728122 prefixEnd_2728122 := by exact prefixLift 2728122
  have htrace : WordTrace (prefixWord ++ tailWord_2728122) baseStart_2728122 baseEnd_2728122 := by
    simpa [prefixWord, tailWord_2728122, baseEnd_2728122] using wordTrace_append hprefix tailTrace_2728122
  have hstable : (prefixWord ++ tailWord_2728122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728122).length < 2 ^ (prefixWord ++ tailWord_2728122).sum := by decide
  have hdescent : baseEnd_2728122 < baseStart_2728122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728139 : List Nat := [1, 1, 1, 1, 3, 2, 4, 5, 5]
def baseStart_2728139 : Nat := 118140960795 + 2728139 * 2 ^ 59
def prefixEnd_2728139 : Nat := 4983230072969 + 3 ^ 40 * 2728139 * 2
def baseEnd_2728139 : Nat := 155649622141822986368447

theorem tailTrace_2728139 : CollatzResearch.WordTrace tailWord_2728139 prefixEnd_2728139 155649622141822986368447 := by
  unfold tailWord_2728139
  simp only [CollatzResearch.WordTrace]
  refine ⟨99503403863425806891803471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66335602575617204594535647 99503403863425806891803471)
  ·
    refine ⟨149255105795138710337705207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99503403863425806891803471 149255105795138710337705207)
    ·
      refine ⟨223882658692708065506557811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149255105795138710337705207 223882658692708065506557811)
      ·
        refine ⟨335823988039062098259836717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223882658692708065506557811 335823988039062098259836717)
        ·
          refine ⟨125933995514648286847438769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 335823988039062098259836717 125933995514648286847438769)
          ·
            refine ⟨94450496635986215135579077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125933995514648286847438769 94450496635986215135579077)
            ·
              refine ⟨17709468119247415337921077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94450496635986215135579077 17709468119247415337921077)
              ·
                refine ⟨1660262636179445187930101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17709468119247415337921077 1660262636179445187930101)
                ·
                  refine ⟨155649622141822986368447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1660262636179445187930101 155649622141822986368447)
                  ·
                    rfl

theorem cell23_2728139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5, 5].length) (baseStart_2728139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728139 prefixEnd_2728139 := by exact prefixLift 2728139
  have htrace : WordTrace (prefixWord ++ tailWord_2728139) baseStart_2728139 baseEnd_2728139 := by
    simpa [prefixWord, tailWord_2728139, baseEnd_2728139] using wordTrace_append hprefix tailTrace_2728139
  have hstable : (prefixWord ++ tailWord_2728139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728139).length < 2 ^ (prefixWord ++ tailWord_2728139).sum := by decide
  have hdescent : baseEnd_2728139 < baseStart_2728139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728186 : List Nat := [3, 1, 1, 1, 1, 7, 1, 1, 2, 5]
def baseStart_2728186 : Nat := 118140960795 + 2728186 * 2 ^ 59
def prefixEnd_2728186 : Nat := 4983230072969 + 3 ^ 40 * 2728186 * 2
def baseEnd_2728186 : Nat := 466956910955722731142769

theorem tailTrace_2728186 : CollatzResearch.WordTrace tailWord_2728186 prefixEnd_2728186 466956910955722731142769 := by
  unfold tailWord_2728186
  simp only [CollatzResearch.WordTrace]
  refine ⟨24876279523563883479691103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66336745396170355945842941 24876279523563883479691103)
  ·
    refine ⟨37314419285345825219536655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24876279523563883479691103 37314419285345825219536655)
    ·
      refine ⟨55971628928018737829304983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37314419285345825219536655 55971628928018737829304983)
      ·
        refine ⟨83957443392028106743957475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55971628928018737829304983 83957443392028106743957475)
        ·
          refine ⟨125936165088042160115936213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83957443392028106743957475 125936165088042160115936213)
          ·
            refine ⟨2951628869250988127717255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 125936165088042160115936213 2951628869250988127717255)
            ·
              refine ⟨4427443303876482191575883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2951628869250988127717255 4427443303876482191575883)
              ·
                refine ⟨6641164955814723287363825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4427443303876482191575883 6641164955814723287363825)
                ·
                  refine ⟨4980873716861042465522869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6641164955814723287363825 4980873716861042465522869)
                  ·
                    refine ⟨466956910955722731142769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4980873716861042465522869 466956910955722731142769)
                    ·
                      rfl

theorem cell23_2728186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 2, 5].length) (baseStart_2728186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728186 prefixEnd_2728186 := by exact prefixLift 2728186
  have htrace : WordTrace (prefixWord ++ tailWord_2728186) baseStart_2728186 baseEnd_2728186 := by
    simpa [prefixWord, tailWord_2728186, baseEnd_2728186] using wordTrace_append hprefix tailTrace_2728186
  have hstable : (prefixWord ++ tailWord_2728186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728186).length < 2 ^ (prefixWord ++ tailWord_2728186).sum := by decide
  have hdescent : baseEnd_2728186 < baseStart_2728186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728206 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2]
def baseStart_2728206 : Nat := 118140960795 + 2728206 * 2 ^ 59
def prefixEnd_2728206 : Nat := 4983230072969 + 3 ^ 40 * 2728206 * 2
def baseEnd_2728206 : Nat := 1400881002480258115178215

theorem tailTrace_2728206 : CollatzResearch.WordTrace tailWord_2728206 prefixEnd_2728206 1400881002480258115178215 := by
  unfold tailWord_2728206
  simp only [CollatzResearch.WordTrace]
  refine ⟨12438230944272884666811559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66337231702788718222994981 12438230944272884666811559)
  ·
    refine ⟨18657346416409327000217339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12438230944272884666811559 18657346416409327000217339)
    ·
      refine ⟨27986019624613990500326009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18657346416409327000217339 27986019624613990500326009)
      ·
        refine ⟨20989514718460492875244507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27986019624613990500326009 20989514718460492875244507)
        ·
          refine ⟨31484272077690739312866761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20989514718460492875244507 31484272077690739312866761)
          ·
            refine ⟨23613204058268054484650071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31484272077690739312866761 23613204058268054484650071)
            ·
              refine ⟨35419806087402081726975107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23613204058268054484650071 35419806087402081726975107)
              ·
                refine ⟨53129709131103122590462661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35419806087402081726975107 53129709131103122590462661)
                ·
                  refine ⟨9961820462081835485711749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53129709131103122590462661 9961820462081835485711749)
                  ·
                    refine ⟨1867841336640344153570953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9961820462081835485711749 1867841336640344153570953)
                    ·
                      refine ⟨1400881002480258115178215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1867841336640344153570953 1400881002480258115178215)
                      ·
                        rfl

theorem cell23_2728206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_2728206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728206 prefixEnd_2728206 := by exact prefixLift 2728206
  have htrace : WordTrace (prefixWord ++ tailWord_2728206) baseStart_2728206 baseEnd_2728206 := by
    simpa [prefixWord, tailWord_2728206, baseEnd_2728206] using wordTrace_append hprefix tailTrace_2728206
  have hstable : (prefixWord ++ tailWord_2728206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728206).length < 2 ^ (prefixWord ++ tailWord_2728206).sum := by decide
  have hdescent : baseEnd_2728206 < baseStart_2728206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728216 : List Nat := [2, 1, 2, 3, 1, 2, 4, 1, 3, 4]
def baseStart_2728216 : Nat := 118140960795 + 2728216 * 2 ^ 59
def prefixEnd_2728216 : Nat := 4983230072969 + 3 ^ 40 * 2728216 * 2
def baseEnd_2728216 : Nat := 466962045762267692017723

theorem tailTrace_2728216 : CollatzResearch.WordTrace tailWord_2728216 prefixEnd_2728216 466962045762267692017723 := by
  unfold tailWord_2728216
  simp only [CollatzResearch.WordTrace]
  refine ⟨49753106142073424521178251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66337474856097899361571001 49753106142073424521178251)
  ·
    refine ⟨74629659213110136781767377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49753106142073424521178251 74629659213110136781767377)
    ·
      refine ⟨55972244409832602586325533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74629659213110136781767377 55972244409832602586325533)
      ·
        refine ⟨20989591653687225969872075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55972244409832602586325533 20989591653687225969872075)
        ·
          refine ⟨31484387480530838954808113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20989591653687225969872075 31484387480530838954808113)
          ·
            refine ⟨23613290610398129216106085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31484387480530838954808113 23613290610398129216106085)
            ·
              refine ⟨4427491989449649228019891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23613290610398129216106085 4427491989449649228019891)
              ·
                refine ⟨6641237984174473842029837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4427491989449649228019891 6641237984174473842029837)
                ·
                  refine ⟨2490464244065427690761189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6641237984174473842029837 2490464244065427690761189)
                  ·
                    refine ⟨466962045762267692017723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2490464244065427690761189 466962045762267692017723)
                    ·
                      rfl

theorem cell23_2728216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 3, 4].length) (baseStart_2728216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728216 prefixEnd_2728216 := by exact prefixLift 2728216
  have htrace : WordTrace (prefixWord ++ tailWord_2728216) baseStart_2728216 baseEnd_2728216 := by
    simpa [prefixWord, tailWord_2728216, baseEnd_2728216] using wordTrace_append hprefix tailTrace_2728216
  have hstable : (prefixWord ++ tailWord_2728216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728216).length < 2 ^ (prefixWord ++ tailWord_2728216).sum := by decide
  have hdescent : baseEnd_2728216 < baseStart_2728216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728226 : List Nat := [3, 3, 1, 1, 3, 1, 1, 2, 1, 4, 3]
def baseStart_2728226 : Nat := 118140960795 + 2728226 * 2 ^ 59
def prefixEnd_2728226 : Nat := 4983230072969 + 3 ^ 40 * 2728226 * 2
def baseEnd_2728226 : Nat := 1400891272093348036928123

theorem tailTrace_2728226 : CollatzResearch.WordTrace tailWord_2728226 prefixEnd_2728226 1400891272093348036928123 := by
  unfold tailWord_2728226
  simp only [CollatzResearch.WordTrace]
  refine ⟨24876644253527655187555133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66337718009407080500147021 24876644253527655187555133)
  ·
    refine ⟨9328741595072870695333175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24876644253527655187555133 9328741595072870695333175)
    ·
      refine ⟨13993112392609306042999763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9328741595072870695333175 13993112392609306042999763)
      ·
        refine ⟨20989668588913959064499645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13993112392609306042999763 20989668588913959064499645)
        ·
          refine ⟨7871125720842734649187367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20989668588913959064499645 7871125720842734649187367)
          ·
            refine ⟨11806688581264101973781051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7871125720842734649187367 11806688581264101973781051)
            ·
              refine ⟨17710032871896152960671577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11806688581264101973781051 17710032871896152960671577)
              ·
                refine ⟨13282524653922114720503683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17710032871896152960671577 13282524653922114720503683)
                ·
                  refine ⟨19923786980883172080755525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13282524653922114720503683 19923786980883172080755525)
                  ·
                    refine ⟨3735710058915594765141661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19923786980883172080755525 3735710058915594765141661)
                    ·
                      refine ⟨1400891272093348036928123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3735710058915594765141661 1400891272093348036928123)
                      ·
                        rfl

theorem cell23_2728226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_2728226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728226 prefixEnd_2728226 := by exact prefixLift 2728226
  have htrace : WordTrace (prefixWord ++ tailWord_2728226) baseStart_2728226 baseEnd_2728226 := by
    simpa [prefixWord, tailWord_2728226, baseEnd_2728226] using wordTrace_append hprefix tailTrace_2728226
  have hstable : (prefixWord ++ tailWord_2728226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728226).length < 2 ^ (prefixWord ++ tailWord_2728226).sum := by decide
  have hdescent : baseEnd_2728226 < baseStart_2728226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728250 : List Nat := [3, 1, 1, 1, 4, 4, 1, 3, 1, 4]
def baseStart_2728250 : Nat := 118140960795 + 2728250 * 2 ^ 59
def prefixEnd_2728250 : Nat := 4983230072969 + 3 ^ 40 * 2728250 * 2
def baseEnd_2728250 : Nat := 466967865209685314342671

theorem tailTrace_2728250 : CollatzResearch.WordTrace tailWord_2728250 prefixEnd_2728250 466967865209685314342671 := by
  unfold tailWord_2728250
  simp only [CollatzResearch.WordTrace]
  refine ⟨24876863091505918212273551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66338301577349115232729469 24876863091505918212273551)
  ·
    refine ⟨37315294637258877318410327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24876863091505918212273551 37315294637258877318410327)
    ·
      refine ⟨55972941955888315977615491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37315294637258877318410327 55972941955888315977615491)
      ·
        refine ⟨83959412933832473966423237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55972941955888315977615491 83959412933832473966423237)
        ·
          refine ⟨15742389925093588868704357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83959412933832473966423237 15742389925093588868704357)
          ·
            refine ⟨2951698110955047912882067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15742389925093588868704357 2951698110955047912882067)
            ·
              refine ⟨4427547166432571869323101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2951698110955047912882067 4427547166432571869323101)
              ·
                refine ⟨1660330187412214450996163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4427547166432571869323101 1660330187412214450996163)
                ·
                  refine ⟨2490495281118321676494245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1660330187412214450996163 2490495281118321676494245)
                  ·
                    refine ⟨466967865209685314342671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2490495281118321676494245 466967865209685314342671)
                    ·
                      rfl

theorem cell23_2728250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3, 1, 4].length) (baseStart_2728250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728250 prefixEnd_2728250 := by exact prefixLift 2728250
  have htrace : WordTrace (prefixWord ++ tailWord_2728250) baseStart_2728250 baseEnd_2728250 := by
    simpa [prefixWord, tailWord_2728250, baseEnd_2728250] using wordTrace_append hprefix tailTrace_2728250
  have hstable : (prefixWord ++ tailWord_2728250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728250).length < 2 ^ (prefixWord ++ tailWord_2728250).sum := by decide
  have hdescent : baseEnd_2728250 < baseStart_2728250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728260 : List Nat := [2, 3, 4, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_2728260 : Nat := 118140960795 + 2728260 * 2 ^ 59
def prefixEnd_2728260 : Nat := 4983230072969 + 3 ^ 40 * 2728260 * 2
def baseEnd_2728260 : Nat := 1400908730435600903902967

theorem tailTrace_2728260 : CollatzResearch.WordTrace tailWord_2728260 prefixEnd_2728260 1400908730435600903902967 := by
  unfold tailWord_2728260
  simp only [CollatzResearch.WordTrace]
  refine ⟨49753908547993722278479117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66338544730658296371305489 49753908547993722278479117)
  ·
    refine ⟨18657715705497645854429669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49753908547993722278479117 18657715705497645854429669)
    ·
      refine ⟨3498321694780808597705563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18657715705497645854429669 3498321694780808597705563)
      ·
        refine ⟨5247482542171212896558345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3498321694780808597705563 5247482542171212896558345)
        ·
          refine ⟨3935611906628409672418759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5247482542171212896558345 3935611906628409672418759)
          ·
            refine ⟨5903417859942614508628139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3935611906628409672418759 5903417859942614508628139)
            ·
              refine ⟨8855126789913921762942209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5903417859942614508628139 8855126789913921762942209)
              ·
                refine ⟨6641345092435441322206657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8855126789913921762942209 6641345092435441322206657)
                ·
                  refine ⟨4981008819326580991654993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6641345092435441322206657 4981008819326580991654993)
                  ·
                    refine ⟨3735756614494935743741245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4981008819326580991654993 3735756614494935743741245)
                    ·
                      refine ⟨1400908730435600903902967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3735756614494935743741245 1400908730435600903902967)
                      ·
                        rfl

theorem cell23_2728260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_2728260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728260 prefixEnd_2728260 := by exact prefixLift 2728260
  have htrace : WordTrace (prefixWord ++ tailWord_2728260) baseStart_2728260 baseEnd_2728260 := by
    simpa [prefixWord, tailWord_2728260, baseEnd_2728260] using wordTrace_append hprefix tailTrace_2728260
  have hstable : (prefixWord ++ tailWord_2728260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728260).length < 2 ^ (prefixWord ++ tailWord_2728260).sum := by decide
  have hdescent : baseEnd_2728260 < baseStart_2728260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728273 : List Nat := [1, 2, 2, 1, 4, 2, 3, 1, 3, 1, 3]
def baseStart_2728273 : Nat := 118140960795 + 2728273 * 2 ^ 59
def prefixEnd_2728273 : Nat := 4983230072969 + 3 ^ 40 * 2728273 * 2
def baseEnd_2728273 : Nat := 1400915405684109353040407

theorem tailTrace_2728273 : CollatzResearch.WordTrace tailWord_2728273 prefixEnd_2728273 1400915405684109353040407 := by
  unfold tailWord_2728273
  simp only [CollatzResearch.WordTrace]
  refine ⟨99508291244940347777181473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66338860829960231851454315 99508291244940347777181473)
  ·
    refine ⟨74631218433705260832886105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99508291244940347777181473 74631218433705260832886105)
    ·
      refine ⟨55973413825278945624664579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74631218433705260832886105 55973413825278945624664579)
      ·
        refine ⟨83960120737918418436996869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55973413825278945624664579 83960120737918418436996869)
        ·
          refine ⟨15742522638359703456936913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83960120737918418436996869 15742522638359703456936913)
          ·
            refine ⟨11806891978769777592702685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15742522638359703456936913 11806891978769777592702685)
            ·
              refine ⟨4427584492038666597263507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11806891978769777592702685 4427584492038666597263507)
              ·
                refine ⟨6641376738057999895895261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4427584492038666597263507 6641376738057999895895261)
                ·
                  refine ⟨2490516276771749960960723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6641376738057999895895261 2490516276771749960960723)
                  ·
                    refine ⟨3735774415157624941441085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2490516276771749960960723 3735774415157624941441085)
                    ·
                      refine ⟨1400915405684109353040407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3735774415157624941441085 1400915405684109353040407)
                      ·
                        rfl

theorem cell23_2728273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3, 1, 3].length) (baseStart_2728273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728273 prefixEnd_2728273 := by exact prefixLift 2728273
  have htrace : WordTrace (prefixWord ++ tailWord_2728273) baseStart_2728273 baseEnd_2728273 := by
    simpa [prefixWord, tailWord_2728273, baseEnd_2728273] using wordTrace_append hprefix tailTrace_2728273
  have hstable : (prefixWord ++ tailWord_2728273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728273).length < 2 ^ (prefixWord ++ tailWord_2728273).sum := by decide
  have hdescent : baseEnd_2728273 < baseStart_2728273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728293 : List Nat := [1, 3, 1, 3, 1, 5, 1, 2, 1, 5]
def baseStart_2728293 : Nat := 118140960795 + 2728293 * 2 ^ 59
def prefixEnd_2728293 : Nat := 4983230072969 + 3 ^ 40 * 2728293 * 2
def baseEnd_2728293 : Nat := 466975225099066424930105

theorem tailTrace_2728293 : CollatzResearch.WordTrace tailWord_2728293 prefixEnd_2728293 466975225099066424930105 := by
  unfold tailWord_2728293
  simp only [CollatzResearch.WordTrace]
  refine ⟨99509020704867891192909533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66339347136578594128606355 99509020704867891192909533)
  ·
    refine ⟨37315882764325459197341075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99509020704867891192909533 37315882764325459197341075)
    ·
      refine ⟨55973824146488188796011613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37315882764325459197341075 55973824146488188796011613)
      ·
        refine ⟨20990184054933070798504355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55973824146488188796011613 20990184054933070798504355)
        ·
          refine ⟨31485276082399606197756533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20990184054933070798504355 31485276082399606197756533)
          ·
            refine ⟨2951744632724963081039675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31485276082399606197756533 2951744632724963081039675)
            ·
              refine ⟨4427616949087444621559513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2951744632724963081039675 4427616949087444621559513)
              ·
                refine ⟨3320712711815583466169635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4427616949087444621559513 3320712711815583466169635)
                ·
                  refine ⟨4981069067723375199254453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3320712711815583466169635 4981069067723375199254453)
                  ·
                    refine ⟨466975225099066424930105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4981069067723375199254453 466975225099066424930105)
                    ·
                      rfl

theorem cell23_2728293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 5].length) (baseStart_2728293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728293 prefixEnd_2728293 := by exact prefixLift 2728293
  have htrace : WordTrace (prefixWord ++ tailWord_2728293) baseStart_2728293 baseEnd_2728293 := by
    simpa [prefixWord, tailWord_2728293, baseEnd_2728293] using wordTrace_append hprefix tailTrace_2728293
  have hstable : (prefixWord ++ tailWord_2728293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728293).length < 2 ^ (prefixWord ++ tailWord_2728293).sum := by decide
  have hdescent : baseEnd_2728293 < baseStart_2728293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728299 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 2, 6, 3]
def baseStart_2728299 : Nat := 118140960795 + 2728299 * 2 ^ 59
def prefixEnd_2728299 : Nat := 4983230072969 + 3 ^ 40 * 2728299 * 2
def baseEnd_2728299 : Nat := 1400928756181126251315287

theorem tailTrace_2728299 : CollatzResearch.WordTrace tailWord_2728299 prefixEnd_2728299 1400928756181126251315287 := by
  unfold tailWord_2728299
  simp only [CollatzResearch.WordTrace]
  refine ⟨99509239542846154217627951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66339493028564102811751967 99509239542846154217627951)
  ·
    refine ⟨149263859314269231326441927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99509239542846154217627951 149263859314269231326441927)
    ·
      refine ⟨223895788971403846989662891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149263859314269231326441927 223895788971403846989662891)
      ·
        refine ⟨335843683457105770484494337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223895788971403846989662891 335843683457105770484494337)
        ·
          refine ⟨251882762592829327863370753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335843683457105770484494337 251882762592829327863370753)
          ·
            refine ⟨188912071944621995897528065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251882762592829327863370753 188912071944621995897528065)
            ·
              refine ⟨141684053958466496923146049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188912071944621995897528065 141684053958466496923146049)
              ·
                refine ⟨106263040468849872692359537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141684053958466496923146049 106263040468849872692359537)
                ·
                  refine ⟨79697280351637404519269653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106263040468849872692359537 79697280351637404519269653)
                  ·
                    refine ⟨3735810016483003336840765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79697280351637404519269653 3735810016483003336840765)
                    ·
                      refine ⟨1400928756181126251315287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3735810016483003336840765 1400928756181126251315287)
                      ·
                        rfl

theorem cell23_2728299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6, 3].length) (baseStart_2728299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728299 prefixEnd_2728299 := by exact prefixLift 2728299
  have htrace : WordTrace (prefixWord ++ tailWord_2728299) baseStart_2728299 baseEnd_2728299 := by
    simpa [prefixWord, tailWord_2728299, baseEnd_2728299] using wordTrace_append hprefix tailTrace_2728299
  have hstable : (prefixWord ++ tailWord_2728299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728299).length < 2 ^ (prefixWord ++ tailWord_2728299).sum := by decide
  have hdescent : baseEnd_2728299 < baseStart_2728299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728300 : List Nat := [2, 2, 1, 1, 6, 1, 2, 1, 2, 3, 2]
def baseStart_2728300 : Nat := 118140960795 + 2728300 * 2 ^ 59
def prefixEnd_2728300 : Nat := 4983230072969 + 3 ^ 40 * 2728300 * 2
def baseEnd_2728300 : Nat := 1400929269661780747402783

theorem tailTrace_2728300 : CollatzResearch.WordTrace tailWord_2728300 prefixEnd_2728300 1400929269661780747402783 := by
  unfold tailWord_2728300
  simp only [CollatzResearch.WordTrace]
  refine ⟨49754638007921265694207177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66339517343895020925609569 49754638007921265694207177)
  ·
    refine ⟨37315978505940949270655383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49754638007921265694207177 37315978505940949270655383)
    ·
      refine ⟨55973967758911423905983075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37315978505940949270655383 55973967758911423905983075)
      ·
        refine ⟨83960951638367135858974613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55973967758911423905983075 83960951638367135858974613)
        ·
          refine ⟨3935669608048459493389435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 83960951638367135858974613 3935669608048459493389435)
          ·
            refine ⟨5903504412072689240084153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3935669608048459493389435 5903504412072689240084153)
            ·
              refine ⟨4427628309054516930063115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5903504412072689240084153 4427628309054516930063115)
              ·
                refine ⟨6641442463581775395094673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4427628309054516930063115 6641442463581775395094673)
                ·
                  refine ⟨4981081847686331546321005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6641442463581775395094673 4981081847686331546321005)
                  ·
                    refine ⟨1867905692882374329870377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4981081847686331546321005 1867905692882374329870377)
                    ·
                      refine ⟨1400929269661780747402783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1867905692882374329870377 1400929269661780747402783)
                      ·
                        rfl

theorem cell23_2728300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 3, 2].length) (baseStart_2728300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728300 prefixEnd_2728300 := by exact prefixLift 2728300
  have htrace : WordTrace (prefixWord ++ tailWord_2728300) baseStart_2728300 baseEnd_2728300 := by
    simpa [prefixWord, tailWord_2728300, baseEnd_2728300] using wordTrace_append hprefix tailTrace_2728300
  have hstable : (prefixWord ++ tailWord_2728300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728300).length < 2 ^ (prefixWord ++ tailWord_2728300).sum := by decide
  have hdescent : baseEnd_2728300 < baseStart_2728300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728306 : List Nat := [3, 2, 1, 2, 1, 4, 1, 2, 1, 6]
def baseStart_2728306 : Nat := 118140960795 + 2728306 * 2 ^ 59
def prefixEnd_2728306 : Nat := 4983230072969 + 3 ^ 40 * 2728306 * 2
def baseEnd_2728306 : Nat := 466977450181902574642585

theorem tailTrace_2728306 : CollatzResearch.WordTrace tailWord_2728306 prefixEnd_2728306 466977450181902574642585 := by
  unfold tailWord_2728306
  simp only [CollatzResearch.WordTrace]
  refine ⟨24877373713455198603283193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66339663235880529608755181 24877373713455198603283193)
  ·
    refine ⟨18658030285091398952462395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24877373713455198603283193 18658030285091398952462395)
    ·
      refine ⟨27987045427637098428693593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18658030285091398952462395 27987045427637098428693593)
      ·
        refine ⟨20990284070727823821520195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27987045427637098428693593 20990284070727823821520195)
        ·
          refine ⟨31485426106091735732280293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20990284070727823821520195 31485426106091735732280293)
          ·
            refine ⟨5903517394892200449802555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31485426106091735732280293 5903517394892200449802555)
            ·
              refine ⟨8855276092338300674703833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5903517394892200449802555 8855276092338300674703833)
              ·
                refine ⟨6641457069253725506027875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8855276092338300674703833 6641457069253725506027875)
                ·
                  refine ⟨9962185603880588259041813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6641457069253725506027875 9962185603880588259041813)
                  ·
                    refine ⟨466977450181902574642585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9962185603880588259041813 466977450181902574642585)
                    ·
                      rfl

theorem cell23_2728306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_2728306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728306 prefixEnd_2728306 := by exact prefixLift 2728306
  have htrace : WordTrace (prefixWord ++ tailWord_2728306) baseStart_2728306 baseEnd_2728306 := by
    simpa [prefixWord, tailWord_2728306, baseEnd_2728306] using wordTrace_append hprefix tailTrace_2728306
  have hstable : (prefixWord ++ tailWord_2728306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728306).length < 2 ^ (prefixWord ++ tailWord_2728306).sum := by decide
  have hdescent : baseEnd_2728306 < baseStart_2728306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728350 : List Nat := [4, 3, 1, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_2728350 : Nat := 118140960795 + 2728350 * 2 ^ 59
def prefixEnd_2728350 : Nat := 4983230072969 + 3 ^ 40 * 2728350 * 2
def baseEnd_2728350 : Nat := 1400954943694505551777553

theorem tailTrace_2728350 : CollatzResearch.WordTrace tailWord_2728350 prefixEnd_2728350 1400954943694505551777553 := by
  unfold tailWord_2728350
  simp only [CollatzResearch.WordTrace]
  refine ⟨12438887458207673740966813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66340733110440926618489669 12438887458207673740966813)
  ·
    refine ⟨4664582796827877652862555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12438887458207673740966813 4664582796827877652862555)
    ·
      refine ⟨6996874195241816479293833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4664582796827877652862555 6996874195241816479293833)
      ·
        refine ⟨5247655646431362359470375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6996874195241816479293833 5247655646431362359470375)
        ·
          refine ⟨7871483469647043539205563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5247655646431362359470375 7871483469647043539205563)
          ·
            refine ⟨11807225204470565308808345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7871483469647043539205563 11807225204470565308808345)
            ·
              refine ⟨8855418903352923981606259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11807225204470565308808345 8855418903352923981606259)
              ·
                refine ⟨13283128355029385972409389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8855418903352923981606259 13283128355029385972409389)
                ·
                  refine ⟨4981173133136019739653521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13283128355029385972409389 4981173133136019739653521)
                  ·
                    refine ⟨3735879849852014804740141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4981173133136019739653521 3735879849852014804740141)
                    ·
                      refine ⟨1400954943694505551777553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3735879849852014804740141 1400954943694505551777553)
                      ·
                        rfl

theorem cell23_2728350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_2728350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728350 prefixEnd_2728350 := by exact prefixLift 2728350
  have htrace : WordTrace (prefixWord ++ tailWord_2728350) baseStart_2728350 baseEnd_2728350 := by
    simpa [prefixWord, tailWord_2728350, baseEnd_2728350] using wordTrace_append hprefix tailTrace_2728350
  have hstable : (prefixWord ++ tailWord_2728350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728350).length < 2 ^ (prefixWord ++ tailWord_2728350).sum := by decide
  have hdescent : baseEnd_2728350 < baseStart_2728350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728380 : List Nat := [2, 2, 2, 4, 1, 2, 1, 1, 4, 1, 3]
def baseStart_2728380 : Nat := 118140960795 + 2728380 * 2 ^ 59
def prefixEnd_2728380 : Nat := 4983230072969 + 3 ^ 40 * 2728380 * 2
def baseEnd_2728380 : Nat := 1400970348114140434402415

theorem tailTrace_2728380 : CollatzResearch.WordTrace tailWord_2728380 prefixEnd_2728380 1400970348114140434402415 := by
  unfold tailWord_2728380
  simp only [CollatzResearch.WordTrace]
  refine ⟨49756096927776352525663297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66341462570368470034217729 49756096927776352525663297)
  ·
    refine ⟨37317072695832264394247473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49756096927776352525663297 37317072695832264394247473)
    ·
      refine ⟨27987804521874198295685605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37317072695832264394247473 27987804521874198295685605)
      ·
        refine ⟨5247713347851412180441051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27987804521874198295685605 5247713347851412180441051)
        ·
          refine ⟨7871570021777118270661577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5247713347851412180441051 7871570021777118270661577)
          ·
            refine ⟨5903677516332838702996183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7871570021777118270661577 5903677516332838702996183)
            ·
              refine ⟨8855516274499258054494275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5903677516332838702996183 8855516274499258054494275)
              ·
                refine ⟨13283274411748887081741413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8855516274499258054494275 13283274411748887081741413)
                ·
                  refine ⟨2490613952202916327826515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13283274411748887081741413 2490613952202916327826515)
                  ·
                    refine ⟨3735920928304374491739773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2490613952202916327826515 3735920928304374491739773)
                    ·
                      refine ⟨1400970348114140434402415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3735920928304374491739773 1400970348114140434402415)
                      ·
                        rfl

theorem cell23_2728380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_2728380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728380 prefixEnd_2728380 := by exact prefixLift 2728380
  have htrace : WordTrace (prefixWord ++ tailWord_2728380) baseStart_2728380 baseEnd_2728380 := by
    simpa [prefixWord, tailWord_2728380, baseEnd_2728380] using wordTrace_append hprefix tailTrace_2728380
  have hstable : (prefixWord ++ tailWord_2728380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728380).length < 2 ^ (prefixWord ++ tailWord_2728380).sum := by decide
  have hdescent : baseEnd_2728380 < baseStart_2728380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728456 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 6, 5]
def baseStart_2728456 : Nat := 118140960795 + 2728456 * 2 ^ 59
def prefixEnd_2728456 : Nat := 4983230072969 + 3 ^ 40 * 2728456 * 2
def baseEnd_2728456 : Nat := 467003124214627379017355

theorem tailTrace_2728456 : CollatzResearch.WordTrace tailWord_2728456 prefixEnd_2728456 467003124214627379017355 := by
  unfold tailWord_2728456
  simp only [CollatzResearch.WordTrace]
  refine ⟨49757482901638685015546611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66343310535518246687395481 49757482901638685015546611)
  ·
    refine ⟨74636224352458027523319917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49757482901638685015546611 74636224352458027523319917)
    ·
      refine ⟨27988584132171760321244969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74636224352458027523319917 27988584132171760321244969)
      ·
        refine ⟨20991438099128820240933727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27988584132171760321244969 20991438099128820240933727)
        ·
          refine ⟨31487157148693230361400591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20991438099128820240933727 31487157148693230361400591)
          ·
            refine ⟨47230735723039845542100887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31487157148693230361400591 47230735723039845542100887)
            ·
              refine ⟨70846103584559768313151331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47230735723039845542100887 70846103584559768313151331)
              ·
                refine ⟨106269155376839652469726997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70846103584559768313151331 106269155376839652469726997)
                ·
                  refine ⟨4981366658289358709518453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 106269155376839652469726997 4981366658289358709518453)
                  ·
                    refine ⟨467003124214627379017355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4981366658289358709518453 467003124214627379017355)
                    ·
                      rfl

theorem cell23_2728456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_2728456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728456 prefixEnd_2728456 := by exact prefixLift 2728456
  have htrace : WordTrace (prefixWord ++ tailWord_2728456) baseStart_2728456 baseEnd_2728456 := by
    simpa [prefixWord, tailWord_2728456, baseEnd_2728456] using wordTrace_append hprefix tailTrace_2728456
  have hstable : (prefixWord ++ tailWord_2728456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728456).length < 2 ^ (prefixWord ++ tailWord_2728456).sum := by decide
  have hdescent : baseEnd_2728456 < baseStart_2728456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728494 : List Nat := [4, 1, 3, 1, 3, 2, 2, 2, 5]
def baseStart_2728494 : Nat := 118140960795 + 2728494 * 2 ^ 59
def prefixEnd_2728494 : Nat := 4983230072969 + 3 ^ 40 * 2728494 * 2
def baseEnd_2728494 : Nat := 155669876100972554264099

theorem tailTrace_2728494 : CollatzResearch.WordTrace tailWord_2728494 prefixEnd_2728494 155669876100972554264099 := by
  unfold tailWord_2728494
  simp only [CollatzResearch.WordTrace]
  refine ⟨12439543972142462815122067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66344234518093135013984357 12439543972142462815122067)
  ·
    refine ⟨18659315958213694222683101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12439543972142462815122067 18659315958213694222683101)
    ·
      refine ⟨6997243484330135333506163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18659315958213694222683101 6997243484330135333506163)
      ·
        refine ⟨10495865226495203000259245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6997243484330135333506163 10495865226495203000259245)
        ·
          refine ⟨3935949459935701125097217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10495865226495203000259245 3935949459935701125097217)
          ·
            refine ⟨2951962094951775843822913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3935949459935701125097217 2951962094951775843822913)
            ·
              refine ⟨2213971571213831882867185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2951962094951775843822913 2213971571213831882867185)
              ·
                refine ⟨1660478678410373912150389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2213971571213831882867185 1660478678410373912150389)
                ·
                  refine ⟨155669876100972554264099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1660478678410373912150389 155669876100972554264099)
                  ·
                    rfl

theorem cell23_2728494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2, 5].length) (baseStart_2728494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728494 prefixEnd_2728494 := by exact prefixLift 2728494
  have htrace : WordTrace (prefixWord ++ tailWord_2728494) baseStart_2728494 baseEnd_2728494 := by
    simpa [prefixWord, tailWord_2728494, baseEnd_2728494] using wordTrace_append hprefix tailTrace_2728494
  have hstable : (prefixWord ++ tailWord_2728494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728494).length < 2 ^ (prefixWord ++ tailWord_2728494).sum := by decide
  have hdescent : baseEnd_2728494 < baseStart_2728494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728503 : List Nat := [1, 1, 3, 1, 2, 3, 2, 3, 3, 4]
def baseStart_2728503 : Nat := 118140960795 + 2728503 * 2 ^ 59
def prefixEnd_2728503 : Nat := 4983230072969 + 3 ^ 40 * 2728503 * 2
def baseEnd_2728503 : Nat := 467011168744881151054783

theorem tailTrace_2728503 : CollatzResearch.WordTrace tailWord_2728503 prefixEnd_2728503 467011168744881151054783 := by
  unfold tailWord_2728503
  simp only [CollatzResearch.WordTrace]
  refine ⟨99516680034107097058054163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66344453356071398038702775 99516680034107097058054163)
  ·
    refine ⟨149275020051160645587081245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99516680034107097058054163 149275020051160645587081245)
    ·
      refine ⟨55978132519185242095155467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149275020051160645587081245 55978132519185242095155467)
      ·
        refine ⟨83967198778777863142733201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55978132519185242095155467 83967198778777863142733201)
        ·
          refine ⟨62975399084083397357049901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83967198778777863142733201 62975399084083397357049901)
          ·
            refine ⟨23615774656531274008893713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62975399084083397357049901 23615774656531274008893713)
            ·
              refine ⟨17711830992398455506670285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23615774656531274008893713 17711830992398455506670285)
              ·
                refine ⟨6641936622149420815001357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17711830992398455506670285 6641936622149420815001357)
                ·
                  refine ⟨2490726233306032805625509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6641936622149420815001357 2490726233306032805625509)
                  ·
                    refine ⟨467011168744881151054783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2490726233306032805625509 467011168744881151054783)
                    ·
                      rfl

theorem cell23_2728503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3, 4].length) (baseStart_2728503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728503 prefixEnd_2728503 := by exact prefixLift 2728503
  have htrace : WordTrace (prefixWord ++ tailWord_2728503) baseStart_2728503 baseEnd_2728503 := by
    simpa [prefixWord, tailWord_2728503, baseEnd_2728503] using wordTrace_append hprefix tailTrace_2728503
  have hstable : (prefixWord ++ tailWord_2728503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728503).length < 2 ^ (prefixWord ++ tailWord_2728503).sum := by decide
  have hdescent : baseEnd_2728503 < baseStart_2728503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728580 : List Nat := [2, 3, 2, 1, 3, 1, 1, 4, 1, 5]
def baseStart_2728580 : Nat := 118140960795 + 2728580 * 2 ^ 59
def prefixEnd_2728580 : Nat := 4983230072969 + 3 ^ 40 * 2728580 * 2
def baseEnd_2728580 : Nat := 467024348081679883967165

theorem tailTrace_2728580 : CollatzResearch.WordTrace tailWord_2728580 prefixEnd_2728580 467024348081679883967165 := by
  unfold tailWord_2728580
  simp only [CollatzResearch.WordTrace]
  refine ⟨49759744227414069604303597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66346325636552092805738129 49759744227414069604303597)
  ·
    refine ⟨18659904085280276101613849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49759744227414069604303597 18659904085280276101613849)
    ·
      refine ⟨13994928063960207076210387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18659904085280276101613849 13994928063960207076210387)
      ·
        refine ⟨20992392095940310614315581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13994928063960207076210387 20992392095940310614315581)
        ·
          refine ⟨7872147035977616480368343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20992392095940310614315581 7872147035977616480368343)
          ·
            refine ⟨11808220553966424720552515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7872147035977616480368343 11808220553966424720552515)
            ·
              refine ⟨17712330830949637080828773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11808220553966424720552515 17712330830949637080828773)
              ·
                refine ⟨3321062030803056952655395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17712330830949637080828773 3321062030803056952655395)
                ·
                  refine ⟨4981593046204585428983093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3321062030803056952655395 4981593046204585428983093)
                  ·
                    refine ⟨467024348081679883967165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4981593046204585428983093 467024348081679883967165)
                    ·
                      rfl

theorem cell23_2728580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_2728580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728580 prefixEnd_2728580 := by exact prefixLift 2728580
  have htrace : WordTrace (prefixWord ++ tailWord_2728580) baseStart_2728580 baseEnd_2728580 := by
    simpa [prefixWord, tailWord_2728580, baseEnd_2728580] using wordTrace_append hprefix tailTrace_2728580
  have hstable : (prefixWord ++ tailWord_2728580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728580).length < 2 ^ (prefixWord ++ tailWord_2728580).sum := by decide
  have hdescent : baseEnd_2728580 < baseStart_2728580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728600 : List Nat := [2, 1, 2, 4, 1, 1, 1, 5, 1, 1, 4]
def baseStart_2728600 : Nat := 118140960795 + 2728600 * 2 ^ 59
def prefixEnd_2728600 : Nat := 4983230072969 + 3 ^ 40 * 2728600 * 2
def baseEnd_2728600 : Nat := 1401083313858129573651403

theorem tailTrace_2728600 : CollatzResearch.WordTrace tailWord_2728600 prefixEnd_2728600 1401083313858129573651403 := by
  unfold tailWord_2728600
  simp only [CollatzResearch.WordTrace]
  refine ⟨49760108957377841312167627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66346811943170455082890169 49760108957377841312167627)
  ·
    refine ⟨74640163436066761968251441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49760108957377841312167627 74640163436066761968251441)
    ·
      refine ⟨55980122577050071476188581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74640163436066761968251441 55980122577050071476188581)
      ·
        refine ⟨10496272983196888401785359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55980122577050071476188581 10496272983196888401785359)
        ·
          refine ⟨15744409474795332602678039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10496272983196888401785359 15744409474795332602678039)
          ·
            refine ⟨23616614212192998904017059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15744409474795332602678039 23616614212192998904017059)
            ·
              refine ⟨35424921318289498356025589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23616614212192998904017059 35424921318289498356025589)
              ·
                refine ⟨3321086373589640470877399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35424921318289498356025589 3321086373589640470877399)
                ·
                  refine ⟨4981629560384460706316099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3321086373589640470877399 4981629560384460706316099)
                  ·
                    refine ⟨7472444340576691059474149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4981629560384460706316099 7472444340576691059474149)
                    ·
                      refine ⟨1401083313858129573651403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7472444340576691059474149 1401083313858129573651403)
                      ·
                        rfl

theorem cell23_2728600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_2728600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728600 prefixEnd_2728600 := by exact prefixLift 2728600
  have htrace : WordTrace (prefixWord ++ tailWord_2728600) baseStart_2728600 baseEnd_2728600 := by
    simpa [prefixWord, tailWord_2728600, baseEnd_2728600] using wordTrace_append hprefix tailTrace_2728600
  have hstable : (prefixWord ++ tailWord_2728600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728600).length < 2 ^ (prefixWord ++ tailWord_2728600).sum := by decide
  have hdescent : baseEnd_2728600 < baseStart_2728600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728623 : List Nat := [1, 1, 2, 1, 2, 6, 2, 8]
def baseStart_2728623 : Nat := 118140960795 + 2728623 * 2 ^ 59
def prefixEnd_2728623 : Nat := 4983230072969 + 3 ^ 40 * 2728623 * 2
def baseEnd_2728623 : Nat := 51892411996784554950511

theorem tailTrace_2728623 : CollatzResearch.WordTrace tailWord_2728623 prefixEnd_2728623 51892411996784554950511 := by
  unfold tailWord_2728623
  simp only [CollatzResearch.WordTrace]
  refine ⟨99521056793672357552422523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66347371195781571701615015 99521056793672357552422523)
  ·
    refine ⟨149281585190508536328633785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99521056793672357552422523 149281585190508536328633785)
    ·
      refine ⟨111961188892881402246475339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149281585190508536328633785 111961188892881402246475339)
      ·
        refine ⟨167941783339322103369713009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111961188892881402246475339 167941783339322103369713009)
        ·
          refine ⟨125956337504491577527284757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167941783339322103369713009 125956337504491577527284757)
          ·
            refine ⟨5904203320523042696591473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 125956337504491577527284757 5904203320523042696591473)
            ·
              refine ⟨4428152490392282022443605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5904203320523042696591473 4428152490392282022443605)
              ·
                refine ⟨51892411996784554950511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4428152490392282022443605 51892411996784554950511)
                ·
                  rfl

theorem cell23_2728623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 8].length) (baseStart_2728623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728623 prefixEnd_2728623 := by exact prefixLift 2728623
  have htrace : WordTrace (prefixWord ++ tailWord_2728623) baseStart_2728623 baseEnd_2728623 := by
    simpa [prefixWord, tailWord_2728623, baseEnd_2728623] using wordTrace_append hprefix tailTrace_2728623
  have hstable : (prefixWord ++ tailWord_2728623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728623).length < 2 ^ (prefixWord ++ tailWord_2728623).sum := by decide
  have hdescent : baseEnd_2728623 < baseStart_2728623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728627 : List Nat := [1, 1, 1, 2, 3, 4, 4, 1, 2, 4]
def baseStart_2728627 : Nat := 118140960795 + 2728627 * 2 ^ 59
def prefixEnd_2728627 : Nat := 4983230072969 + 3 ^ 40 * 2728627 * 2
def baseEnd_2728627 : Nat := 467032392611933656004593

theorem tailTrace_2728627 : CollatzResearch.WordTrace tailWord_2728627 prefixEnd_2728627 467032392611933656004593 := by
  unfold tailWord_2728627
  simp only [CollatzResearch.WordTrace]
  refine ⟨99521202685657866235568135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66347468457105244157045423 99521202685657866235568135)
  ·
    refine ⟨149281804028486799353352203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99521202685657866235568135 149281804028486799353352203)
    ·
      refine ⟨223922706042730199030028305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149281804028486799353352203 223922706042730199030028305)
      ·
        refine ⟨167942029532047649272521229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223922706042730199030028305 167942029532047649272521229)
        ·
          refine ⟨62978261074517868477195461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167942029532047649272521229 62978261074517868477195461)
          ·
            refine ⟨11808423951472100339474149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62978261074517868477195461 11808423951472100339474149)
            ·
              refine ⟨2214079490901018813651403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11808423951472100339474149 2214079490901018813651403)
              ·
                refine ⟨3321119236351528220477105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2214079490901018813651403 3321119236351528220477105)
                ·
                  refine ⟨2490839427263646165357829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3321119236351528220477105 2490839427263646165357829)
                  ·
                    refine ⟨467032392611933656004593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2490839427263646165357829 467032392611933656004593)
                    ·
                      rfl

theorem cell23_2728627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 2, 4].length) (baseStart_2728627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728627 prefixEnd_2728627 := by exact prefixLift 2728627
  have htrace : WordTrace (prefixWord ++ tailWord_2728627) baseStart_2728627 baseEnd_2728627 := by
    simpa [prefixWord, tailWord_2728627, baseEnd_2728627] using wordTrace_append hprefix tailTrace_2728627
  have hstable : (prefixWord ++ tailWord_2728627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728627).length < 2 ^ (prefixWord ++ tailWord_2728627).sum := by decide
  have hdescent : baseEnd_2728627 < baseStart_2728627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728637 : List Nat := [1, 4, 1, 2, 1, 3, 3, 2, 1, 2, 3]
def baseStart_2728637 : Nat := 118140960795 + 2728637 * 2 ^ 59
def prefixEnd_2728637 : Nat := 4983230072969 + 3 ^ 40 * 2728637 * 2
def baseEnd_2728637 : Nat := 1401102312642345928888733

theorem tailTrace_2728637 : CollatzResearch.WordTrace tailWord_2728637 prefixEnd_2728637 1401102312642345928888733 := by
  unfold tailWord_2728637
  simp only [CollatzResearch.WordTrace]
  refine ⟨99521567415621637943432165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66347711610414425295621443 99521567415621637943432165)
  ·
    refine ⟨18660293890429057114393531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99521567415621637943432165 18660293890429057114393531)
    ·
      refine ⟨27990440835643585671590297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18660293890429057114393531 27990440835643585671590297)
      ·
        refine ⟨20992830626732689253692723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27990440835643585671590297 20992830626732689253692723)
        ·
          refine ⟨31489245940099033880539085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20992830626732689253692723 31489245940099033880539085)
          ·
            refine ⟨11808467227537137705202157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31489245940099033880539085 11808467227537137705202157)
            ·
              refine ⟨4428175210326426639450809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11808467227537137705202157 4428175210326426639450809)
              ·
                refine ⟨3321131407744819979588107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4428175210326426639450809 3321131407744819979588107)
                ·
                  refine ⟨4981697111617229969382161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3321131407744819979588107 4981697111617229969382161)
                  ·
                    refine ⟨3736272833712922477036621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4981697111617229969382161 3736272833712922477036621)
                    ·
                      refine ⟨1401102312642345928888733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3736272833712922477036621 1401102312642345928888733)
                      ·
                        rfl

theorem cell23_2728637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_2728637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728637 prefixEnd_2728637 := by exact prefixLift 2728637
  have htrace : WordTrace (prefixWord ++ tailWord_2728637) baseStart_2728637 baseEnd_2728637 := by
    simpa [prefixWord, tailWord_2728637, baseEnd_2728637] using wordTrace_append hprefix tailTrace_2728637
  have hstable : (prefixWord ++ tailWord_2728637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728637).length < 2 ^ (prefixWord ++ tailWord_2728637).sum := by decide
  have hdescent : baseEnd_2728637 < baseStart_2728637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728650 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 3, 3, 3]
def baseStart_2728650 : Nat := 118140960795 + 2728650 * 2 ^ 59
def prefixEnd_2728650 : Nat := 4983230072969 + 3 ^ 40 * 2728650 * 2
def baseEnd_2728650 : Nat := 1401108987890854378026173

theorem tailTrace_2728650 : CollatzResearch.WordTrace tailWord_2728650 prefixEnd_2728650 1401108987890854378026173 := by
  unfold tailWord_2728650
  simp only [CollatzResearch.WordTrace]
  refine ⟨24880510391143635290913851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66348027709716360775770269 24880510391143635290913851)
  ·
    refine ⟨37320765586715452936370777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24880510391143635290913851 37320765586715452936370777)
    ·
      refine ⟨27990574190036589702278083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37320765586715452936370777 27990574190036589702278083)
      ·
        refine ⟨41985861285054884553417125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27990574190036589702278083 41985861285054884553417125)
        ·
          refine ⟨7872348990947790853765711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41985861285054884553417125 7872348990947790853765711)
          ·
            refine ⟨11808523486421686280648567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7872348990947790853765711 11808523486421686280648567)
            ·
              refine ⟨17712785229632529420972851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11808523486421686280648567 17712785229632529420972851)
              ·
                refine ⟨26569177844448794131459277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17712785229632529420972851 26569177844448794131459277)
                ·
                  refine ⟨9963441691668297799297229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26569177844448794131459277 9963441691668297799297229)
                  ·
                    refine ⟨3736290634375611674736461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9963441691668297799297229 3736290634375611674736461)
                    ·
                      refine ⟨1401108987890854378026173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3736290634375611674736461 1401108987890854378026173)
                      ·
                        rfl

theorem cell23_2728650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_2728650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728650 prefixEnd_2728650 := by exact prefixLift 2728650
  have htrace : WordTrace (prefixWord ++ tailWord_2728650) baseStart_2728650 baseEnd_2728650 := by
    simpa [prefixWord, tailWord_2728650, baseEnd_2728650] using wordTrace_append hprefix tailTrace_2728650
  have hstable : (prefixWord ++ tailWord_2728650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728650).length < 2 ^ (prefixWord ++ tailWord_2728650).sum := by decide
  have hdescent : baseEnd_2728650 < baseStart_2728650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728654 : List Nat := [4, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3]
def baseStart_2728654 : Nat := 118140960795 + 2728654 * 2 ^ 59
def prefixEnd_2728654 : Nat := 4983230072969 + 3 ^ 40 * 2728654 * 2
def baseEnd_2728654 : Nat := 1401111041813472362376155

theorem tailTrace_2728654 : CollatzResearch.WordTrace tailWord_2728654 prefixEnd_2728654 1401111041813472362376155 := by
  unfold tailWord_2728654
  simp only [CollatzResearch.WordTrace]
  refine ⟨12440273432070006230850127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66348124971040033231200677 12440273432070006230850127)
  ·
    refine ⟨18660410148105009346275191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12440273432070006230850127 18660410148105009346275191)
    ·
      refine ⟨27990615222157514019412787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18660410148105009346275191 27990615222157514019412787)
      ·
        refine ⟨41985922833236271029119181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27990615222157514019412787 41985922833236271029119181)
        ·
          refine ⟨15744721062463601635919693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41985922833236271029119181 15744721062463601635919693)
          ·
            refine ⟨5904270398423850613469885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15744721062463601635919693 5904270398423850613469885)
            ·
              refine ⟨2214101399408943980051207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5904270398423850613469885 2214101399408943980051207)
              ·
                refine ⟨3321152099113415970076811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2214101399408943980051207 3321152099113415970076811)
                ·
                  refine ⟨4981728148670123955115217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3321152099113415970076811 4981728148670123955115217)
                  ·
                    refine ⟨3736296111502592966336413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4981728148670123955115217 3736296111502592966336413)
                    ·
                      refine ⟨1401111041813472362376155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3736296111502592966336413 1401111041813472362376155)
                      ·
                        rfl

theorem cell23_2728654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3].length) (baseStart_2728654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728654 prefixEnd_2728654 := by exact prefixLift 2728654
  have htrace : WordTrace (prefixWord ++ tailWord_2728654) baseStart_2728654 baseEnd_2728654 := by
    simpa [prefixWord, tailWord_2728654, baseEnd_2728654] using wordTrace_append hprefix tailTrace_2728654
  have hstable : (prefixWord ++ tailWord_2728654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728654).length < 2 ^ (prefixWord ++ tailWord_2728654).sum := by decide
  have hdescent : baseEnd_2728654 < baseStart_2728654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728668 : List Nat := [2, 2, 5, 1, 1, 2, 1, 4, 1, 2, 2]
def baseStart_2728668 : Nat := 118140960795 + 2728668 * 2 ^ 59
def prefixEnd_2728668 : Nat := 4983230072969 + 3 ^ 40 * 2728668 * 2
def baseEnd_2728668 : Nat := 1401118230542635307601091

theorem tailTrace_2728668 : CollatzResearch.WordTrace tailWord_2728668 prefixEnd_2728668 1401118230542635307601091 := by
  unfold tailWord_2728668
  simp only [CollatzResearch.WordTrace]
  refine ⟨49761349039254665118905329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66348465385672886825207105 49761349039254665118905329)
  ·
    refine ⟨37321011779440998839178997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49761349039254665118905329 37321011779440998839178997)
    ·
      refine ⟨3498844854322593641173031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37321011779440998839178997 3498844854322593641173031)
      ·
        refine ⟨5248267281483890461759547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3498844854322593641173031 5248267281483890461759547)
        ·
          refine ⟨7872400922225835692639321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5248267281483890461759547 7872400922225835692639321)
          ·
            refine ⟨5904300691669376769479491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7872400922225835692639321 5904300691669376769479491)
            ·
              refine ⟨8856451037504065154219237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5904300691669376769479491 8856451037504065154219237)
              ·
                refine ⟨1660584569532012216416107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8856451037504065154219237 1660584569532012216416107)
                ·
                  refine ⟨2490876854298018324624161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1660584569532012216416107 2490876854298018324624161)
                  ·
                    refine ⟨1868157640723513743468121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2490876854298018324624161 1868157640723513743468121)
                    ·
                      refine ⟨1401118230542635307601091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1868157640723513743468121 1401118230542635307601091)
                      ·
                        rfl

theorem cell23_2728668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_2728668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728668 prefixEnd_2728668 := by exact prefixLift 2728668
  have htrace : WordTrace (prefixWord ++ tailWord_2728668) baseStart_2728668 baseEnd_2728668 := by
    simpa [prefixWord, tailWord_2728668, baseEnd_2728668] using wordTrace_append hprefix tailTrace_2728668
  have hstable : (prefixWord ++ tailWord_2728668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728668).length < 2 ^ (prefixWord ++ tailWord_2728668).sum := by decide
  have hdescent : baseEnd_2728668 < baseStart_2728668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728677 : List Nat := [1, 3, 1, 4, 1, 2, 1, 2, 3, 3, 2]
def baseStart_2728677 : Nat := 118140960795 + 2728677 * 2 ^ 59
def prefixEnd_2728677 : Nat := 4983230072969 + 3 ^ 40 * 2728677 * 2
def baseEnd_2728677 : Nat := 1401122851868525772388549

theorem tailTrace_2728677 : CollatzResearch.WordTrace tailWord_2728677 prefixEnd_2728677 1401122851868525772388549 := by
  unfold tailWord_2728677
  simp only [CollatzResearch.WordTrace]
  refine ⟨99523026335476724774888285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66348684223651149849925523 99523026335476724774888285)
  ·
    refine ⟨37321134875803771790583107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99523026335476724774888285 37321134875803771790583107)
    ·
      refine ⟨55981702313705657685874661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37321134875803771790583107 55981702313705657685874661)
      ·
        refine ⟨10496569183819810816101499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55981702313705657685874661 10496569183819810816101499)
        ·
          refine ⟨15744853775729716224152249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10496569183819810816101499 15744853775729716224152249)
          ·
            refine ⟨11808640331797287168114187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15744853775729716224152249 11808640331797287168114187)
            ·
              refine ⟨17712960497695930752171281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11808640331797287168114187 17712960497695930752171281)
              ·
                refine ⟨13284720373271948064128461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17712960497695930752171281 13284720373271948064128461)
                ·
                  refine ⟨4981770139976980524048173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13284720373271948064128461 4981770139976980524048173)
                  ·
                    refine ⟨1868163802491367696518065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4981770139976980524048173 1868163802491367696518065)
                    ·
                      refine ⟨1401122851868525772388549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1868163802491367696518065 1401122851868525772388549)
                      ·
                        rfl

theorem cell23_2728677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_2728677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728677 prefixEnd_2728677 := by exact prefixLift 2728677
  have htrace : WordTrace (prefixWord ++ tailWord_2728677) baseStart_2728677 baseEnd_2728677 := by
    simpa [prefixWord, tailWord_2728677, baseEnd_2728677] using wordTrace_append hprefix tailTrace_2728677
  have hstable : (prefixWord ++ tailWord_2728677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728677).length < 2 ^ (prefixWord ++ tailWord_2728677).sum := by decide
  have hdescent : baseEnd_2728677 < baseStart_2728677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728694 : List Nat := [5, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2]
def baseStart_2728694 : Nat := 118140960795 + 2728694 * 2 ^ 59
def prefixEnd_2728694 : Nat := 4983230072969 + 3 ^ 40 * 2728694 * 2
def baseEnd_2728694 : Nat := 1401131581039652205875971

theorem tailTrace_2728694 : CollatzResearch.WordTrace tailWord_2728694 prefixEnd_2728694 1401131581039652205875971 := by
  unfold tailWord_2728694
  simp only [CollatzResearch.WordTrace]
  refine ⟨6220227898525946042391071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66349097584276757785504757 6220227898525946042391071)
  ·
    refine ⟨9330341847788919063586607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6220227898525946042391071 9330341847788919063586607)
    ·
      refine ⟨13995512771683378595379911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9330341847788919063586607 13995512771683378595379911)
      ·
        refine ⟨20993269157525067893069867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13995512771683378595379911 20993269157525067893069867)
        ·
          refine ⟨31489903736287601839604801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20993269157525067893069867 31489903736287601839604801)
          ·
            refine ⟨23617427802215701379703601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31489903736287601839604801 23617427802215701379703601)
            ·
              refine ⟨17713070851661776034777701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23617427802215701379703601 17713070851661776034777701)
              ·
                refine ⟨3321200784686583006520819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17713070851661776034777701 3321200784686583006520819)
                ·
                  refine ⟨4981801177029874509781229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3321200784686583006520819 4981801177029874509781229)
                  ·
                    refine ⟨1868175441386202941167961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4981801177029874509781229 1868175441386202941167961)
                    ·
                      refine ⟨1401131581039652205875971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1868175441386202941167961 1401131581039652205875971)
                      ·
                        rfl

theorem cell23_2728694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_2728694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728694 prefixEnd_2728694 := by exact prefixLift 2728694
  have htrace : WordTrace (prefixWord ++ tailWord_2728694) baseStart_2728694 baseEnd_2728694 := by
    simpa [prefixWord, tailWord_2728694, baseEnd_2728694] using wordTrace_append hprefix tailTrace_2728694
  have hstable : (prefixWord ++ tailWord_2728694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728694).length < 2 ^ (prefixWord ++ tailWord_2728694).sum := by decide
  have hdescent : baseEnd_2728694 < baseStart_2728694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728703 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 4]
def baseStart_2728703 : Nat := 118140960795 + 2728703 * 2 ^ 59
def prefixEnd_2728703 : Nat := 4983230072969 + 3 ^ 40 * 2728703 * 2
def baseEnd_2728703 : Nat := 1401136202365542670663429

theorem tailTrace_2728703 : CollatzResearch.WordTrace tailWord_2728703 prefixEnd_2728703 1401136202365542670663429 := by
  unfold tailWord_2728703
  simp only [CollatzResearch.WordTrace]
  refine ⟨99523974633382531215334763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66349316422255020810223175 99523974633382531215334763)
  ·
    refine ⟨149285961950073796823002145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99523974633382531215334763 149285961950073796823002145)
    ·
      refine ⟨111964471462555347617251609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149285961950073796823002145 111964471462555347617251609)
      ·
        refine ⟨83973353596916510712938707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111964471462555347617251609 83973353596916510712938707)
        ·
          refine ⟨125960030395374766069408061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83973353596916510712938707 125960030395374766069408061)
          ·
            refine ⟨47235011398265537276028023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125960030395374766069408061 47235011398265537276028023)
            ·
              refine ⟨70852517097398305914042035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47235011398265537276028023 70852517097398305914042035)
              ·
                refine ⟨106278775646097458871063053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70852517097398305914042035 106278775646097458871063053)
                ·
                  refine ⟨39854540867286547076648645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106278775646097458871063053 39854540867286547076648645)
                  ·
                    refine ⟨7472726412616227576871621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39854540867286547076648645 7472726412616227576871621)
                    ·
                      refine ⟨1401136202365542670663429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7472726412616227576871621 1401136202365542670663429)
                      ·
                        rfl

theorem cell23_2728703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_2728703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728703 prefixEnd_2728703 := by exact prefixLift 2728703
  have htrace : WordTrace (prefixWord ++ tailWord_2728703) baseStart_2728703 baseEnd_2728703 := by
    simpa [prefixWord, tailWord_2728703, baseEnd_2728703] using wordTrace_append hprefix tailTrace_2728703
  have hstable : (prefixWord ++ tailWord_2728703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728703).length < 2 ^ (prefixWord ++ tailWord_2728703).sum := by decide
  have hdescent : baseEnd_2728703 < baseStart_2728703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728707 : List Nat := [1, 1, 1, 3, 2, 2, 1, 4, 4, 2, 2]
def baseStart_2728707 : Nat := 118140960795 + 2728707 * 2 ^ 59
def prefixEnd_2728707 : Nat := 4983230072969 + 3 ^ 40 * 2728707 * 2
def baseEnd_2728707 : Nat := 1401138256288160655013411

theorem tailTrace_2728707 : CollatzResearch.WordTrace tailWord_2728707 prefixEnd_2728707 1401138256288160655013411 := by
  unfold tailWord_2728707
  simp only [CollatzResearch.WordTrace]
  refine ⟨99524120525368039898480375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66349413683578693265653583 99524120525368039898480375)
  ·
    refine ⟨149286180788052059847720563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99524120525368039898480375 149286180788052059847720563)
    ·
      refine ⟨223929271182078089771580845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149286180788052059847720563 223929271182078089771580845)
      ·
        refine ⟨83973476693279283664342817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223929271182078089771580845 83973476693279283664342817)
        ·
          refine ⟨62980107519959462748257113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83973476693279283664342817 62980107519959462748257113)
          ·
            refine ⟨47235080639969597061192835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62980107519959462748257113 47235080639969597061192835)
            ·
              refine ⟨70852620959954395591789253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47235080639969597061192835 70852620959954395591789253)
              ·
                refine ⟨13284866429991449173460485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70852620959954395591789253 13284866429991449173460485)
                ·
                  refine ⟨2490912455623396720023841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13284866429991449173460485 2490912455623396720023841)
                  ·
                    refine ⟨1868184341717547540017881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2490912455623396720023841 1868184341717547540017881)
                    ·
                      refine ⟨1401138256288160655013411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1868184341717547540017881 1401138256288160655013411)
                      ·
                        rfl

theorem cell23_2728707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4, 2, 2].length) (baseStart_2728707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728707 prefixEnd_2728707 := by exact prefixLift 2728707
  have htrace : WordTrace (prefixWord ++ tailWord_2728707) baseStart_2728707 baseEnd_2728707 := by
    simpa [prefixWord, tailWord_2728707, baseEnd_2728707] using wordTrace_append hprefix tailTrace_2728707
  have hstable : (prefixWord ++ tailWord_2728707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728707).length < 2 ^ (prefixWord ++ tailWord_2728707).sum := by decide
  have hdescent : baseEnd_2728707 < baseStart_2728707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728711 : List Nat := [1, 1, 4, 4, 1, 1, 4, 1, 1, 3, 2]
def baseStart_2728711 : Nat := 118140960795 + 2728711 * 2 ^ 59
def prefixEnd_2728711 : Nat := 4983230072969 + 3 ^ 40 * 2728711 * 2
def baseEnd_2728711 : Nat := 1401140310210778639363393

theorem tailTrace_2728711 : CollatzResearch.WordTrace tailWord_2728711 prefixEnd_2728711 1401140310210778639363393 := by
  unfold tailWord_2728711
  simp only [CollatzResearch.WordTrace]
  refine ⟨99524266417353548581625987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66349510944902365721083991 99524266417353548581625987)
  ·
    refine ⟨149286399626030322872438981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99524266417353548581625987 149286399626030322872438981)
    ·
      refine ⟨27991199929880685538582309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149286399626030322872438981 27991199929880685538582309)
      ·
        refine ⟨5248349986852628538484183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27991199929880685538582309 5248349986852628538484183)
        ·
          refine ⟨7872524980278942807726275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5248349986852628538484183 7872524980278942807726275)
          ·
            refine ⟨11808787470418414211589413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7872524980278942807726275 11808787470418414211589413)
            ·
              refine ⟨2214147650703452664673015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11808787470418414211589413 2214147650703452664673015)
              ·
                refine ⟨3321221476055178997009523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2214147650703452664673015 3321221476055178997009523)
                ·
                  refine ⟨4981832214082768495514285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3321221476055178997009523 4981832214082768495514285)
                  ·
                    refine ⟨1868187080281038185817857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4981832214082768495514285 1868187080281038185817857)
                    ·
                      refine ⟨1401140310210778639363393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1868187080281038185817857 1401140310210778639363393)
                      ·
                        rfl

theorem cell23_2728711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_2728711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728711 prefixEnd_2728711 := by exact prefixLift 2728711
  have htrace : WordTrace (prefixWord ++ tailWord_2728711) baseStart_2728711 baseEnd_2728711 := by
    simpa [prefixWord, tailWord_2728711, baseEnd_2728711] using wordTrace_append hprefix tailTrace_2728711
  have hstable : (prefixWord ++ tailWord_2728711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728711).length < 2 ^ (prefixWord ++ tailWord_2728711).sum := by decide
  have hdescent : baseEnd_2728711 < baseStart_2728711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728730 : List Nat := [3, 1, 1, 3, 2, 1, 4, 1, 7]
def baseStart_2728730 : Nat := 118140960795 + 2728730 * 2 ^ 59
def prefixEnd_2728730 : Nat := 4983230072969 + 3 ^ 40 * 2728730 * 2
def baseEnd_2728730 : Nat := 155683340704801562780645

theorem tailTrace_2728730 : CollatzResearch.WordTrace tailWord_2728730 prefixEnd_2728730 155683340704801562780645 := by
  unfold tailWord_2728730
  simp only [CollatzResearch.WordTrace]
  refine ⟨24881239851071178706641911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66349972936189809884378429 24881239851071178706641911)
  ·
    refine ⟨37321859776606768059962867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24881239851071178706641911 37321859776606768059962867)
    ·
      refine ⟨55982789664910152089944301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37321859776606768059962867 55982789664910152089944301)
      ·
        refine ⟨20993546124341307033729113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55982789664910152089944301 20993546124341307033729113)
        ·
          refine ⟨15745159593255980275296835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20993546124341307033729113 15745159593255980275296835)
          ·
            refine ⟨23617739389883970412945253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15745159593255980275296835 23617739389883970412945253)
            ·
              refine ⟨4428326135603244452427235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23617739389883970412945253 4428326135603244452427235)
              ·
                refine ⟨6642489203404866678640853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4428326135603244452427235 6642489203404866678640853)
                ·
                  refine ⟨155683340704801562780645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6642489203404866678640853 155683340704801562780645)
                  ·
                    rfl

theorem cell23_2728730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 7].length) (baseStart_2728730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728730 prefixEnd_2728730 := by exact prefixLift 2728730
  have htrace : WordTrace (prefixWord ++ tailWord_2728730) baseStart_2728730 baseEnd_2728730 := by
    simpa [prefixWord, tailWord_2728730, baseEnd_2728730] using wordTrace_append hprefix tailTrace_2728730
  have hstable : (prefixWord ++ tailWord_2728730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728730).length < 2 ^ (prefixWord ++ tailWord_2728730).sum := by decide
  have hdescent : baseEnd_2728730 < baseStart_2728730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728741 : List Nat := [1, 3, 1, 2, 3, 1, 5, 1, 2, 2, 2]
def baseStart_2728741 : Nat := 118140960795 + 2728741 * 2 ^ 59
def prefixEnd_2728741 : Nat := 4983230072969 + 3 ^ 40 * 2728741 * 2
def baseEnd_2728741 : Nat := 1401155714630413521988255

theorem tailTrace_2728741 : CollatzResearch.WordTrace tailWord_2728741 prefixEnd_2728741 1401155714630413521988255 := by
  unfold tailWord_2728741
  simp only [CollatzResearch.WordTrace]
  refine ⟨99525360607244863705218077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66350240404829909136812051 99525360607244863705218077)
  ·
    refine ⟨37322010227716823889456779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99525360607244863705218077 37322010227716823889456779)
    ·
      refine ⟨55983015341575235834185169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37322010227716823889456779 55983015341575235834185169)
      ·
        refine ⟨41987261506181426875638877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55983015341575235834185169 41987261506181426875638877)
        ·
          refine ⟨15745223064818035078364579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41987261506181426875638877 15745223064818035078364579)
          ·
            refine ⟨23617834597227052617546869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15745223064818035078364579 23617834597227052617546869)
            ·
              refine ⟨2214171993490036182895019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23617834597227052617546869 2214171993490036182895019)
              ·
                refine ⟨3321257990235054274342529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2214171993490036182895019 3321257990235054274342529)
                ·
                  refine ⟨2490943492676290705756897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3321257990235054274342529 2490943492676290705756897)
                  ·
                    refine ⟨1868207619507218029317673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2490943492676290705756897 1868207619507218029317673)
                    ·
                      refine ⟨1401155714630413521988255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1868207619507218029317673 1401155714630413521988255)
                      ·
                        rfl

theorem cell23_2728741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 2, 2, 2].length) (baseStart_2728741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728741 prefixEnd_2728741 := by exact prefixLift 2728741
  have htrace : WordTrace (prefixWord ++ tailWord_2728741) baseStart_2728741 baseEnd_2728741 := by
    simpa [prefixWord, tailWord_2728741, baseEnd_2728741] using wordTrace_append hprefix tailTrace_2728741
  have hstable : (prefixWord ++ tailWord_2728741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728741).length < 2 ^ (prefixWord ++ tailWord_2728741).sum := by decide
  have hdescent : baseEnd_2728741 < baseStart_2728741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728760 : List Nat := [2, 1, 2, 1, 3, 2, 2, 3, 2, 5]
def baseStart_2728760 : Nat := 118140960795 + 2728760 * 2 ^ 59
def prefixEnd_2728760 : Nat := 4983230072969 + 3 ^ 40 * 2728760 * 2
def baseEnd_2728760 : Nat := 467055156920949649216889

theorem tailTrace_2728760 : CollatzResearch.WordTrace tailWord_2728760 prefixEnd_2728760 467055156920949649216889 := by
  unfold tailWord_2728760
  simp only [CollatzResearch.WordTrace]
  refine ⟨49763026797088014975079867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66350702396117353300106489 49763026797088014975079867)
  ·
    refine ⟨74644540195632022462619801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49763026797088014975079867 74644540195632022462619801)
    ·
      refine ⟨55983405146724016846964851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74644540195632022462619801 55983405146724016846964851)
      ·
        refine ⟨83975107720086025270447277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55983405146724016846964851 83975107720086025270447277)
        ·
          refine ⟨31490665395032259476417729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83975107720086025270447277 31490665395032259476417729)
          ·
            refine ⟨23617999046274194607313297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31490665395032259476417729 23617999046274194607313297)
            ·
              refine ⟨17713499284705645955484973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23617999046274194607313297 17713499284705645955484973)
              ·
                refine ⟨6642562231764617233306865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17713499284705645955484973 6642562231764617233306865)
                ·
                  refine ⟨4981921673823462924980149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6642562231764617233306865 4981921673823462924980149)
                  ·
                    refine ⟨467055156920949649216889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4981921673823462924980149 467055156920949649216889)
                    ·
                      rfl

theorem cell23_2728760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 2, 5].length) (baseStart_2728760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728760 prefixEnd_2728760 := by exact prefixLift 2728760
  have htrace : WordTrace (prefixWord ++ tailWord_2728760) baseStart_2728760 baseEnd_2728760 := by
    simpa [prefixWord, tailWord_2728760, baseEnd_2728760] using wordTrace_append hprefix tailTrace_2728760
  have hstable : (prefixWord ++ tailWord_2728760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728760).length < 2 ^ (prefixWord ++ tailWord_2728760).sum := by decide
  have hdescent : baseEnd_2728760 < baseStart_2728760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728781 : List Nat := [1, 6, 1, 2, 3, 1, 1, 1, 7]
def baseStart_2728781 : Nat := 118140960795 + 2728781 * 2 ^ 59
def prefixEnd_2728781 : Nat := 4983230072969 + 3 ^ 40 * 2728781 * 2
def baseEnd_2728781 : Nat := 155686250428510373943119

theorem tailTrace_2728781 : CollatzResearch.WordTrace tailWord_2728781 prefixEnd_2728781 155686250428510373943119 := by
  unfold tailWord_2728781
  simp only [CollatzResearch.WordTrace]
  refine ⟨99526819527099950536674197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66351213018066633691116131 99526819527099950536674197)
  ·
    refine ⟨4665319665332810181406603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 99526819527099950536674197 4665319665332810181406603)
    ·
      refine ⟨6997979497999215272109905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4665319665332810181406603 6997979497999215272109905)
      ·
        refine ⟨5248484623499411454082429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6997979497999215272109905 5248484623499411454082429)
        ·
          refine ⟨1968181733812279295280911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5248484623499411454082429 1968181733812279295280911)
          ·
            refine ⟨2952272600718418942921367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1968181733812279295280911 2952272600718418942921367)
            ·
              refine ⟨4428408901077628414382051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2952272600718418942921367 4428408901077628414382051)
              ·
                refine ⟨6642613351616442621573077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4428408901077628414382051 6642613351616442621573077)
                ·
                  refine ⟨155686250428510373943119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6642613351616442621573077 155686250428510373943119)
                  ·
                    rfl

theorem cell23_2728781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_2728781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728781 prefixEnd_2728781 := by exact prefixLift 2728781
  have htrace : WordTrace (prefixWord ++ tailWord_2728781) baseStart_2728781 baseEnd_2728781 := by
    simpa [prefixWord, tailWord_2728781, baseEnd_2728781] using wordTrace_append hprefix tailTrace_2728781
  have hstable : (prefixWord ++ tailWord_2728781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728781).length < 2 ^ (prefixWord ++ tailWord_2728781).sum := by decide
  have hdescent : baseEnd_2728781 < baseStart_2728781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728817 : List Nat := [1, 2, 2, 2, 1, 4, 1, 3, 2, 2, 3]
def baseStart_2728817 : Nat := 118140960795 + 2728817 * 2 ^ 59
def prefixEnd_2728817 : Nat := 4983230072969 + 3 ^ 40 * 2728817 * 2
def baseEnd_2728817 : Nat := 1401194739160155224637905

theorem tailTrace_2728817 : CollatzResearch.WordTrace tailWord_2728817 prefixEnd_2728817 1401194739160155224637905 := by
  unfold tailWord_2728817
  simp only [CollatzResearch.WordTrace]
  refine ⟨99528132554969528684984705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66352088369979685789989803 99528132554969528684984705)
  ·
    refine ⟨74646099416227146513738529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99528132554969528684984705 74646099416227146513738529)
    ·
      refine ⟨55984574562170359885303897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74646099416227146513738529 55984574562170359885303897)
      ·
        refine ⟨41988430921627769913977923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55984574562170359885303897 41988430921627769913977923)
        ·
          refine ⟨62982646382441654870966885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41988430921627769913977923 62982646382441654870966885)
          ·
            refine ⟨11809246196707810288306291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62982646382441654870966885 11809246196707810288306291)
            ·
              refine ⟨17713869295061715432459437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11809246196707810288306291 17713869295061715432459437)
              ·
                refine ⟨6642700985648143287172289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17713869295061715432459437 6642700985648143287172289)
                ·
                  refine ⟨4982025739236107465379217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6642700985648143287172289 4982025739236107465379217)
                  ·
                    refine ⟨3736519304427080599034413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4982025739236107465379217 3736519304427080599034413)
                    ·
                      refine ⟨1401194739160155224637905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3736519304427080599034413 1401194739160155224637905)
                      ·
                        rfl

theorem cell23_2728817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_2728817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728817 prefixEnd_2728817 := by exact prefixLift 2728817
  have htrace : WordTrace (prefixWord ++ tailWord_2728817) baseStart_2728817 baseEnd_2728817 := by
    simpa [prefixWord, tailWord_2728817, baseEnd_2728817] using wordTrace_append hprefix tailTrace_2728817
  have hstable : (prefixWord ++ tailWord_2728817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728817).length < 2 ^ (prefixWord ++ tailWord_2728817).sum := by decide
  have hdescent : baseEnd_2728817 < baseStart_2728817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728837 : List Nat := [1, 3, 1, 1, 3, 4, 2, 2, 6]
def baseStart_2728837 : Nat := 118140960795 + 2728837 * 2 ^ 59
def prefixEnd_2728837 : Nat := 4983230072969 + 3 ^ 40 * 2728837 * 2
def baseEnd_2728837 : Nat := 155689445419249460709757

theorem tailTrace_2728837 : CollatzResearch.WordTrace tailWord_2728837 prefixEnd_2728837 155689445419249460709757 := by
  unfold tailWord_2728837
  simp only [CollatzResearch.WordTrace]
  refine ⟨99528862014897072100712765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66352574676598048067141843 99528862014897072100712765)
  ·
    refine ⟨37323323255586402037767287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99528862014897072100712765 37323323255586402037767287)
    ·
      refine ⟨55984984883379603056650931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37323323255586402037767287 55984984883379603056650931)
      ·
        refine ⟨83977477325069404584976397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55984984883379603056650931 83977477325069404584976397)
        ·
          refine ⟨31491553996901026719366149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83977477325069404584976397 31491553996901026719366149)
          ·
            refine ⟨5904666374418942509881153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31491553996901026719366149 5904666374418942509881153)
            ·
              refine ⟨4428499780814206882410865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5904666374418942509881153 4428499780814206882410865)
              ·
                refine ⟨3321374835610655161808149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4428499780814206882410865 3321374835610655161808149)
                ·
                  refine ⟨155689445419249460709757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3321374835610655161808149 155689445419249460709757)
                  ·
                    rfl

theorem cell23_2728837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 6].length) (baseStart_2728837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728837 prefixEnd_2728837 := by exact prefixLift 2728837
  have htrace : WordTrace (prefixWord ++ tailWord_2728837) baseStart_2728837 baseEnd_2728837 := by
    simpa [prefixWord, tailWord_2728837, baseEnd_2728837] using wordTrace_append hprefix tailTrace_2728837
  have hstable : (prefixWord ++ tailWord_2728837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728837).length < 2 ^ (prefixWord ++ tailWord_2728837).sum := by decide
  have hdescent : baseEnd_2728837 < baseStart_2728837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728841 : List Nat := [1, 2, 1, 1, 5, 2, 4, 2, 1, 4]
def baseStart_2728841 : Nat := 118140960795 + 2728841 * 2 ^ 59
def prefixEnd_2728841 : Nat := 4983230072969 + 3 ^ 40 * 2728841 * 2
def baseEnd_2728841 : Nat := 467069020898621043579265

theorem tailTrace_2728841 : CollatzResearch.WordTrace tailWord_2728841 prefixEnd_2728841 467069020898621043579265 := by
  unfold tailWord_2728841
  simp only [CollatzResearch.WordTrace]
  refine ⟨99529007906882580783858377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66352671937921720522572251 99529007906882580783858377)
  ·
    refine ⟨74646755930161935587893783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99529007906882580783858377 74646755930161935587893783)
    ·
      refine ⟨111970133895242903381840675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74646755930161935587893783 111970133895242903381840675)
      ·
        refine ⟨167955200842864355072761013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111970133895242903381840675 167955200842864355072761013)
        ·
          refine ⟨15745800079018533288071345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 167955200842864355072761013 15745800079018533288071345)
          ·
            refine ⟨11809350059263899966053509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15745800079018533288071345 11809350059263899966053509)
            ·
              refine ⟨2214253136111981243635033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11809350059263899966053509 2214253136111981243635033)
              ·
                refine ⟨1660689852083985932726275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2214253136111981243635033 1660689852083985932726275)
                ·
                  refine ⟨2491034778125978899089413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1660689852083985932726275 2491034778125978899089413)
                  ·
                    refine ⟨467069020898621043579265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2491034778125978899089413 467069020898621043579265)
                    ·
                      rfl

theorem cell23_2728841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2, 1, 4].length) (baseStart_2728841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728841 prefixEnd_2728841 := by exact prefixLift 2728841
  have htrace : WordTrace (prefixWord ++ tailWord_2728841) baseStart_2728841 baseEnd_2728841 := by
    simpa [prefixWord, tailWord_2728841, baseEnd_2728841] using wordTrace_append hprefix tailTrace_2728841
  have hstable : (prefixWord ++ tailWord_2728841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728841).length < 2 ^ (prefixWord ++ tailWord_2728841).sum := by decide
  have hdescent : baseEnd_2728841 < baseStart_2728841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728857 : List Nat := [1, 2, 1, 2, 1, 3, 1, 4, 1, 5, 2]
def baseStart_2728857 : Nat := 118140960795 + 2728857 * 2 ^ 59
def prefixEnd_2728857 : Nat := 4983230072969 + 3 ^ 40 * 2728857 * 2
def baseEnd_2728857 : Nat := 1401215278386335068137721

theorem tailTrace_2728857 : CollatzResearch.WordTrace tailWord_2728857 prefixEnd_2728857 1401215278386335068137721 := by
  unfold tailWord_2728857
  simp only [CollatzResearch.WordTrace]
  refine ⟨99529591474824615516440825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66353060983216410344293883 99529591474824615516440825)
  ·
    refine ⟨74647193606118461637330619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99529591474824615516440825 74647193606118461637330619)
    ·
      refine ⟨111970790409177692455995929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74647193606118461637330619 111970790409177692455995929)
      ·
        refine ⟨83978092806883269341996947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111970790409177692455995929 83978092806883269341996947)
        ·
          refine ⟨125967139210324904012995421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83978092806883269341996947 125967139210324904012995421)
          ·
            refine ⟨47237677203871839004873283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125967139210324904012995421 47237677203871839004873283)
            ·
              refine ⟨70856515805807758507309925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47237677203871839004873283 70856515805807758507309925)
              ·
                refine ⟨13285596713588954720120611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70856515805807758507309925 13285596713588954720120611)
                ·
                  refine ⟨19928395070383432080180917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13285596713588954720120611 19928395070383432080180917)
                  ·
                    refine ⟨1868287037848446757516961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19928395070383432080180917 1868287037848446757516961)
                    ·
                      refine ⟨1401215278386335068137721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1868287037848446757516961 1401215278386335068137721)
                      ·
                        rfl

theorem cell23_2728857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 5, 2].length) (baseStart_2728857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728857 prefixEnd_2728857 := by exact prefixLift 2728857
  have htrace : WordTrace (prefixWord ++ tailWord_2728857) baseStart_2728857 baseEnd_2728857 := by
    simpa [prefixWord, tailWord_2728857, baseEnd_2728857] using wordTrace_append hprefix tailTrace_2728857
  have hstable : (prefixWord ++ tailWord_2728857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728857).length < 2 ^ (prefixWord ++ tailWord_2728857).sum := by decide
  have hdescent : baseEnd_2728857 < baseStart_2728857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728907 : List Nat := [1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 5]
def baseStart_2728907 : Nat := 118140960795 + 2728907 * 2 ^ 59
def prefixEnd_2728907 : Nat := 4983230072969 + 3 ^ 40 * 2728907 * 2
def baseEnd_2728907 : Nat := 1401240952419059872512491

theorem tailTrace_2728907 : CollatzResearch.WordTrace tailWord_2728907 prefixEnd_2728907 1401240952419059872512491 := by
  unfold tailWord_2728907
  simp only [CollatzResearch.WordTrace]
  refine ⟨99531415124643474055760975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66354276749762316037173983 99531415124643474055760975)
  ·
    refine ⟨149297122686965211083641463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99531415124643474055760975 149297122686965211083641463)
    ·
      refine ⟨223945684030447816625462195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149297122686965211083641463 223945684030447816625462195)
      ·
        refine ⟨335918526045671724938193293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223945684030447816625462195 335918526045671724938193293)
        ·
          refine ⟨125969447267126896851822485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 335918526045671724938193293 125969447267126896851822485)
          ·
            refine ⟨5904817840646573289929179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 125969447267126896851822485 5904817840646573289929179)
            ·
              refine ⟨8857226760969859934893769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5904817840646573289929179 8857226760969859934893769)
              ·
                refine ⟨6642920070727394951170327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8857226760969859934893769 6642920070727394951170327)
                ·
                  refine ⟨9964380106091092426755491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6642920070727394951170327 9964380106091092426755491)
                  ·
                    refine ⟨14946570159136638640133237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9964380106091092426755491 14946570159136638640133237)
                    ·
                      refine ⟨1401240952419059872512491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14946570159136638640133237 1401240952419059872512491)
                      ·
                        rfl

theorem cell23_2728907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 5].length) (baseStart_2728907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728907 prefixEnd_2728907 := by exact prefixLift 2728907
  have htrace : WordTrace (prefixWord ++ tailWord_2728907) baseStart_2728907 baseEnd_2728907 := by
    simpa [prefixWord, tailWord_2728907, baseEnd_2728907] using wordTrace_append hprefix tailTrace_2728907
  have hstable : (prefixWord ++ tailWord_2728907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728907).length < 2 ^ (prefixWord ++ tailWord_2728907).sum := by decide
  have hdescent : baseEnd_2728907 < baseStart_2728907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728914 : List Nat := [3, 2, 2, 3, 1, 1, 3, 1, 1, 6]
def baseStart_2728914 : Nat := 118140960795 + 2728914 * 2 ^ 59
def prefixEnd_2728914 : Nat := 4983230072969 + 3 ^ 40 * 2728914 * 2
def baseEnd_2728914 : Nat := 467081515594547115041653

theorem tailTrace_2728914 : CollatzResearch.WordTrace tailWord_2728914 prefixEnd_2728914 467081515594547115041653 := by
  unfold tailWord_2728914
  simp only [CollatzResearch.WordTrace]
  refine ⟨24882917608904528562816449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66354446957078742834177197 24882917608904528562816449)
  ·
    refine ⟨18662188206678396422112337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24882917608904528562816449 18662188206678396422112337)
    ·
      refine ⟨13996641155008797316584253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18662188206678396422112337 13996641155008797316584253)
      ·
        refine ⟨5248740433128298993719095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13996641155008797316584253 5248740433128298993719095)
        ·
          refine ⟨7873110649692448490578643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5248740433128298993719095 7873110649692448490578643)
          ·
            refine ⟨11809665974538672735867965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7873110649692448490578643 11809665974538672735867965)
            ·
              refine ⟨4428624740452002275950487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11809665974538672735867965 4428624740452002275950487)
              ·
                refine ⟨6642937110678003413925731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4428624740452002275950487 6642937110678003413925731)
                ·
                  refine ⟨9964405666017005120888597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6642937110678003413925731 9964405666017005120888597)
                  ·
                    refine ⟨467081515594547115041653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9964405666017005120888597 467081515594547115041653)
                    ·
                      rfl

theorem cell23_2728914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_2728914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728914 prefixEnd_2728914 := by exact prefixLift 2728914
  have htrace : WordTrace (prefixWord ++ tailWord_2728914) baseStart_2728914 baseEnd_2728914 := by
    simpa [prefixWord, tailWord_2728914, baseEnd_2728914] using wordTrace_append hprefix tailTrace_2728914
  have hstable : (prefixWord ++ tailWord_2728914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728914).length < 2 ^ (prefixWord ++ tailWord_2728914).sum := by decide
  have hdescent : baseEnd_2728914 < baseStart_2728914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728921 : List Nat := [1, 2, 1, 2, 5, 1, 2, 2, 3, 2, 2]
def baseStart_2728921 : Nat := 118140960795 + 2728921 * 2 ^ 59
def prefixEnd_2728921 : Nat := 4983230072969 + 3 ^ 40 * 2728921 * 2
def baseEnd_2728921 : Nat := 1401248141148222817737427

theorem tailTrace_2728921 : CollatzResearch.WordTrace tailWord_2728921 prefixEnd_2728921 1401248141148222817737427 := by
  unfold tailWord_2728921
  simp only [CollatzResearch.WordTrace]
  refine ⟨99531925746592754446770617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66354617164395169631180411 99531925746592754446770617)
  ·
    refine ⟨74648944309944565835077963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99531925746592754446770617 74648944309944565835077963)
    ·
      refine ⟨111973416464916848752616945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74648944309944565835077963 111973416464916848752616945)
      ·
        refine ⟨83980062348687636564462709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111973416464916848752616945 83980062348687636564462709)
        ·
          refine ⟨7873130845189465927918379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83980062348687636564462709 7873130845189465927918379)
          ·
            refine ⟨11809696267784198891877569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7873130845189465927918379 11809696267784198891877569)
            ·
              refine ⟨8857272200838149168908177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11809696267784198891877569 8857272200838149168908177)
              ·
                refine ⟨6642954150628611876681133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8857272200838149168908177 6642954150628611876681133)
                ·
                  refine ⟨2491107806485729453755425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6642954150628611876681133 2491107806485729453755425)
                  ·
                    refine ⟨1868330854864297090316569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2491107806485729453755425 1868330854864297090316569)
                    ·
                      refine ⟨1401248141148222817737427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1868330854864297090316569 1401248141148222817737427)
                      ·
                        rfl

theorem cell23_2728921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3, 2, 2].length) (baseStart_2728921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728921 prefixEnd_2728921 := by exact prefixLift 2728921
  have htrace : WordTrace (prefixWord ++ tailWord_2728921) baseStart_2728921 baseEnd_2728921 := by
    simpa [prefixWord, tailWord_2728921, baseEnd_2728921] using wordTrace_append hprefix tailTrace_2728921
  have hstable : (prefixWord ++ tailWord_2728921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728921).length < 2 ^ (prefixWord ++ tailWord_2728921).sum := by decide
  have hdescent : baseEnd_2728921 < baseStart_2728921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728927 : List Nat := [1, 1, 2, 3, 5, 1, 1, 9]
def baseStart_2728927 : Nat := 118140960795 + 2728927 * 2 ^ 59
def prefixEnd_2728927 : Nat := 4983230072969 + 3 ^ 40 * 2728927 * 2
def baseEnd_2728927 : Nat := 51898193408598140528237

theorem tailTrace_2728927 : CollatzResearch.WordTrace tailWord_2728927 prefixEnd_2728927 51898193408598140528237 := by
  unfold tailWord_2728927
  simp only [CollatzResearch.WordTrace]
  refine ⟨99532144584571017471489035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66354763056380678314326023 99532144584571017471489035)
  ·
    refine ⟨149298216876856526207233553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99532144584571017471489035 149298216876856526207233553)
    ·
      refine ⟨111973662657642394655425165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149298216876856526207233553 111973662657642394655425165)
      ·
        refine ⟨41990123496615897995784437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111973662657642394655425165 41990123496615897995784437)
        ·
          refine ⟨3936574077807740437104791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41990123496615897995784437 3936574077807740437104791)
          ·
            refine ⟨5904861116711610655657187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3936574077807740437104791 5904861116711610655657187)
            ·
              refine ⟨8857291675067415983485781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5904861116711610655657187 8857291675067415983485781)
              ·
                refine ⟨51898193408598140528237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8857291675067415983485781 51898193408598140528237)
                ·
                  rfl

theorem cell23_2728927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 9].length) (baseStart_2728927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728927 prefixEnd_2728927 := by exact prefixLift 2728927
  have htrace : WordTrace (prefixWord ++ tailWord_2728927) baseStart_2728927 baseEnd_2728927 := by
    simpa [prefixWord, tailWord_2728927, baseEnd_2728927] using wordTrace_append hprefix tailTrace_2728927
  have hstable : (prefixWord ++ tailWord_2728927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728927).length < 2 ^ (prefixWord ++ tailWord_2728927).sum := by decide
  have hdescent : baseEnd_2728927 < baseStart_2728927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728940 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 3, 9]
def baseStart_2728940 : Nat := 118140960795 + 2728940 * 2 ^ 59
def prefixEnd_2728940 : Nat := 4983230072969 + 3 ^ 40 * 2728940 * 2
def baseEnd_2728940 : Nat := 467085965760219414466613

theorem tailTrace_2728940 : CollatzResearch.WordTrace tailWord_2728940 prefixEnd_2728940 467085965760219414466613 := by
  unfold tailWord_2728940
  simp only [CollatzResearch.WordTrace]
  refine ⟨49766309366761960345856137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66355079155682613794474849 49766309366761960345856137)
  ·
    refine ⟨37324732025071470259392103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49766309366761960345856137 37324732025071470259392103)
    ·
      refine ⟨55987098037607205389088155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37324732025071470259392103 55987098037607205389088155)
      ·
        refine ⟨83980647056410808083632233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55987098037607205389088155 83980647056410808083632233)
        ·
          refine ⟨62985485292308106062724175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83980647056410808083632233 62985485292308106062724175)
          ·
            refine ⟨94478227938462159094086263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62985485292308106062724175 94478227938462159094086263)
            ·
              refine ⟨141717341907693238641129395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94478227938462159094086263 141717341907693238641129395)
              ·
                refine ⟨212576012861539857961694093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141717341907693238641129395 212576012861539857961694093)
                ·
                  refine ⟨79716004823077446735635285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 212576012861539857961694093 79716004823077446735635285)
                  ·
                    refine ⟨467085965760219414466613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 79716004823077446735635285 467085965760219414466613)
                    ·
                      rfl

theorem cell23_2728940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 9].length) (baseStart_2728940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728940 prefixEnd_2728940 := by exact prefixLift 2728940
  have htrace : WordTrace (prefixWord ++ tailWord_2728940) baseStart_2728940 baseEnd_2728940 := by
    simpa [prefixWord, tailWord_2728940, baseEnd_2728940] using wordTrace_append hprefix tailTrace_2728940
  have hstable : (prefixWord ++ tailWord_2728940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728940).length < 2 ^ (prefixWord ++ tailWord_2728940).sum := by decide
  have hdescent : baseEnd_2728940 < baseStart_2728940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728960 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 10]
def baseStart_2728960 : Nat := 118140960795 + 2728960 * 2 ^ 59
def prefixEnd_2728960 : Nat := 4983230072969 + 3 ^ 40 * 2728960 * 2
def baseEnd_2728960 : Nat := 1401268166893748165149747

theorem tailTrace_2728960 : CollatzResearch.WordTrace tailWord_2728960 prefixEnd_2728960 1401268166893748165149747 := by
  unfold tailWord_2728960
  simp only [CollatzResearch.WordTrace]
  refine ⟨49766674096725732053720167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66355565462300976071626889 49766674096725732053720167)
  ·
    refine ⟨74650011145088598080580251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49766674096725732053720167 74650011145088598080580251)
    ·
      refine ⟨111975016717632897120870377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74650011145088598080580251 111975016717632897120870377)
      ·
        refine ⟨83981262538224672840652783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111975016717632897120870377 83981262538224672840652783)
        ·
          refine ⟨125971893807337009260979175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83981262538224672840652783 125971893807337009260979175)
          ·
            refine ⟨188957840711005513891468763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125971893807337009260979175 188957840711005513891468763)
            ·
              refine ⟨283436761066508270837203145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188957840711005513891468763 283436761066508270837203145)
              ·
                refine ⟨212577570799881203127902359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283436761066508270837203145 212577570799881203127902359)
                ·
                  refine ⟨318866356199821804691853539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212577570799881203127902359 318866356199821804691853539)
                  ·
                    refine ⟨478299534299732707037780309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 318866356199821804691853539 478299534299732707037780309)
                    ·
                      refine ⟨1401268166893748165149747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 478299534299732707037780309 1401268166893748165149747)
                      ·
                        rfl

theorem cell23_2728960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_2728960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728960 prefixEnd_2728960 := by exact prefixLift 2728960
  have htrace : WordTrace (prefixWord ++ tailWord_2728960) baseStart_2728960 baseEnd_2728960 := by
    simpa [prefixWord, tailWord_2728960, baseEnd_2728960] using wordTrace_append hprefix tailTrace_2728960
  have hstable : (prefixWord ++ tailWord_2728960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728960).length < 2 ^ (prefixWord ++ tailWord_2728960).sum := by decide
  have hdescent : baseEnd_2728960 < baseStart_2728960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728971 : List Nat := [1, 1, 1, 1, 6, 3, 1, 3, 2, 1, 3]
def baseStart_2728971 : Nat := 118140960795 + 2728971 * 2 ^ 59
def prefixEnd_2728971 : Nat := 4983230072969 + 3 ^ 40 * 2728971 * 2
def baseEnd_2728971 : Nat := 1401273815180947622112197

theorem tailTrace_2728971 : CollatzResearch.WordTrace tailWord_2728971 prefixEnd_2728971 1401273815180947622112197 := by
  unfold tailWord_2728971
  simp only [CollatzResearch.WordTrace]
  refine ⟨99533749396411612986090767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66355832930941075324060511 99533749396411612986090767)
  ·
    refine ⟨149300624094617419479136151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99533749396411612986090767 149300624094617419479136151)
    ·
      refine ⟨223950936141926129218704227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149300624094617419479136151 223950936141926129218704227)
      ·
        refine ⟨335926404212889193828056341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223950936141926129218704227 335926404212889193828056341)
        ·
          refine ⟨15746550197479180960690141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 335926404212889193828056341 15746550197479180960690141)
          ·
            refine ⟨5904956324054692860258803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15746550197479180960690141 5904956324054692860258803)
            ·
              refine ⟨8857434486082039290388205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5904956324054692860258803 8857434486082039290388205)
              ·
                refine ⟨3321537932280764733895577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8857434486082039290388205 3321537932280764733895577)
                ·
                  refine ⟨2491153449210573550421683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3321537932280764733895577 2491153449210573550421683)
                  ·
                    refine ⟨3736730173815860325632525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2491153449210573550421683 3736730173815860325632525)
                    ·
                      refine ⟨1401273815180947622112197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3736730173815860325632525 1401273815180947622112197)
                      ·
                        rfl

theorem cell23_2728971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2, 1, 3].length) (baseStart_2728971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728971 prefixEnd_2728971 := by exact prefixLift 2728971
  have htrace : WordTrace (prefixWord ++ tailWord_2728971) baseStart_2728971 baseEnd_2728971 := by
    simpa [prefixWord, tailWord_2728971, baseEnd_2728971] using wordTrace_append hprefix tailTrace_2728971
  have hstable : (prefixWord ++ tailWord_2728971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728971).length < 2 ^ (prefixWord ++ tailWord_2728971).sum := by decide
  have hdescent : baseEnd_2728971 < baseStart_2728971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728981 : List Nat := [1, 3, 2, 1, 4, 2, 1, 1, 3, 3, 2]
def baseStart_2728981 : Nat := 118140960795 + 2728981 * 2 ^ 59
def prefixEnd_2728981 : Nat := 4983230072969 + 3 ^ 40 * 2728981 * 2
def baseEnd_2728981 : Nat := 1401278949987492582987151

theorem tailTrace_2728981 : CollatzResearch.WordTrace tailWord_2728981 prefixEnd_2728981 1401278949987492582987151 := by
  unfold tailWord_2728981
  simp only [CollatzResearch.WordTrace]
  refine ⟨99534114126375384693954797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66356076084250256462636531 99534114126375384693954797)
  ·
    refine ⟨37325292797390769260233049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99534114126375384693954797 37325292797390769260233049)
    ·
      refine ⟨27993969598043076945174787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37325292797390769260233049 27993969598043076945174787)
      ·
        refine ⟨41990954397064615417762181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27993969598043076945174787 41990954397064615417762181)
        ·
          refine ⟨7873303949449615390830409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41990954397064615417762181 7873303949449615390830409)
          ·
            refine ⟨5904977962087211543122807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7873303949449615390830409 5904977962087211543122807)
            ·
              refine ⟨8857466943130817314684211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5904977962087211543122807 8857466943130817314684211)
              ·
                refine ⟨13286200414696225972026317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8857466943130817314684211 13286200414696225972026317)
                ·
                  refine ⟨4982325155511084739509869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13286200414696225972026317 4982325155511084739509869)
                  ·
                    refine ⟨1868371933316656777316201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4982325155511084739509869 1868371933316656777316201)
                    ·
                      refine ⟨1401278949987492582987151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1868371933316656777316201 1401278949987492582987151)
                      ·
                        rfl

theorem cell23_2728981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 3, 2].length) (baseStart_2728981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728981 prefixEnd_2728981 := by exact prefixLift 2728981
  have htrace : WordTrace (prefixWord ++ tailWord_2728981) baseStart_2728981 baseEnd_2728981 := by
    simpa [prefixWord, tailWord_2728981, baseEnd_2728981] using wordTrace_append hprefix tailTrace_2728981
  have hstable : (prefixWord ++ tailWord_2728981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728981).length < 2 ^ (prefixWord ++ tailWord_2728981).sum := by decide
  have hdescent : baseEnd_2728981 < baseStart_2728981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728997 : List Nat := [1, 3, 1, 2, 2, 2, 1, 3, 2, 1, 5]
def baseStart_2728997 : Nat := 118140960795 + 2728997 * 2 ^ 59
def prefixEnd_2728997 : Nat := 4983230072969 + 3 ^ 40 * 2728997 * 2
def baseEnd_2728997 : Nat := 1401287165677964520387077

theorem tailTrace_2728997 : CollatzResearch.WordTrace tailWord_2728997 prefixEnd_2728997 1401287165677964520387077 := by
  unfold tailWord_2728997
  simp only [CollatzResearch.WordTrace]
  refine ⟨99534697694317419426537245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66356465129544946284358163 99534697694317419426537245)
  ·
    refine ⟨37325511635369032284951467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99534697694317419426537245 37325511635369032284951467)
    ·
      refine ⟨55988267453053548427427201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37325511635369032284951467 55988267453053548427427201)
      ·
        refine ⟨41991200589790161320570401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55988267453053548427427201 41991200589790161320570401)
        ·
          refine ⟨31493400442342620990427801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41991200589790161320570401 31493400442342620990427801)
          ·
            refine ⟨23620050331756965742820851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31493400442342620990427801 23620050331756965742820851)
            ·
              refine ⟨35430075497635448614231277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23620050331756965742820851 35430075497635448614231277)
              ·
                refine ⟨13286278311613293230336729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35430075497635448614231277 13286278311613293230336729)
                ·
                  refine ⟨9964708733709969922752547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13286278311613293230336729 9964708733709969922752547)
                  ·
                    refine ⟨14947063100564954884128821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9964708733709969922752547 14947063100564954884128821)
                    ·
                      refine ⟨1401287165677964520387077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14947063100564954884128821 1401287165677964520387077)
                      ·
                        rfl

theorem cell23_2728997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_2728997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2728997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2728997 prefixEnd_2728997 := by exact prefixLift 2728997
  have htrace : WordTrace (prefixWord ++ tailWord_2728997) baseStart_2728997 baseEnd_2728997 := by
    simpa [prefixWord, tailWord_2728997, baseEnd_2728997] using wordTrace_append hprefix tailTrace_2728997
  have hstable : (prefixWord ++ tailWord_2728997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728997).length < 2 ^ (prefixWord ++ tailWord_2728997).sum := by decide
  have hdescent : baseEnd_2728997 < baseStart_2728997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729057 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 3, 2, 5]
def baseStart_2729057 : Nat := 118140960795 + 2729057 * 2 ^ 59
def prefixEnd_2729057 : Nat := 4983230072969 + 3 ^ 40 * 2729057 * 2
def baseEnd_2729057 : Nat := 1401317974517234285636801

theorem tailTrace_2729057 : CollatzResearch.WordTrace tailWord_2729057 prefixEnd_2729057 1401317974517234285636801 := by
  unfold tailWord_2729057
  simp only [CollatzResearch.WordTrace]
  refine ⟨99536886074100049673721425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66357924049400033115814283 99536886074100049673721425)
  ·
    refine ⟨74652664555575037255291069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99536886074100049673721425 74652664555575037255291069)
    ·
      refine ⟨27994749208340638970734151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74652664555575037255291069 27994749208340638970734151)
      ·
        refine ⟨41992123812510958456101227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27994749208340638970734151 41992123812510958456101227)
        ·
          refine ⟨62988185718766437684151841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41992123812510958456101227 62988185718766437684151841)
          ·
            refine ⟨47241139289074828263113881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62988185718766437684151841 47241139289074828263113881)
            ·
              refine ⟨35430854466806121197335411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47241139289074828263113881 35430854466806121197335411)
              ·
                refine ⟨53146281700209181796003117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35430854466806121197335411 53146281700209181796003117)
                ·
                  refine ⟨19929855637578443173501169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53146281700209181796003117 19929855637578443173501169)
                  ·
                    refine ⟨14947391728183832380125877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19929855637578443173501169 14947391728183832380125877)
                    ·
                      refine ⟨1401317974517234285636801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14947391728183832380125877 1401317974517234285636801)
                      ·
                        rfl

theorem cell23_2729057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_2729057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729057 prefixEnd_2729057 := by exact prefixLift 2729057
  have htrace : WordTrace (prefixWord ++ tailWord_2729057) baseStart_2729057 baseEnd_2729057 := by
    simpa [prefixWord, tailWord_2729057, baseEnd_2729057] using wordTrace_append hprefix tailTrace_2729057
  have hstable : (prefixWord ++ tailWord_2729057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729057).length < 2 ^ (prefixWord ++ tailWord_2729057).sum := by decide
  have hdescent : baseEnd_2729057 < baseStart_2729057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729107 : List Nat := [1, 1, 1, 2, 1, 2, 5, 2, 8]
def baseStart_2729107 : Nat := 118140960795 + 2729107 * 2 ^ 59
def prefixEnd_2729107 : Nat := 4983230072969 + 3 ^ 40 * 2729107 * 2
def baseEnd_2729107 : Nat := 155704849838884343334619

theorem tailTrace_2729107 : CollatzResearch.WordTrace tailWord_2729107 prefixEnd_2729107 155704849838884343334619 := by
  unfold tailWord_2729107
  simp only [CollatzResearch.WordTrace]
  refine ⟨99538709723918908213041575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66359139815945938808694383 99538709723918908213041575)
  ·
    refine ⟨149308064585878362319562363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99538709723918908213041575 149308064585878362319562363)
    ·
      refine ⟨223962096878817543479343545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149308064585878362319562363 223962096878817543479343545)
      ·
        refine ⟨167971572659113157609507659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223962096878817543479343545 167971572659113157609507659)
        ·
          refine ⟨251957358988669736414261489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167971572659113157609507659 251957358988669736414261489)
          ·
            refine ⟨188968019241502302310696117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251957358988669736414261489 188968019241502302310696117)
            ·
              refine ⟨17715751803890840841627761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 188968019241502302310696117 17715751803890840841627761)
              ·
                refine ⟨13286813852918130631220821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17715751803890840841627761 13286813852918130631220821)
                ·
                  refine ⟨155704849838884343334619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13286813852918130631220821 155704849838884343334619)
                  ·
                    rfl

theorem cell23_2729107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 8].length) (baseStart_2729107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729107 prefixEnd_2729107 := by exact prefixLift 2729107
  have htrace : WordTrace (prefixWord ++ tailWord_2729107) baseStart_2729107 baseEnd_2729107 := by
    simpa [prefixWord, tailWord_2729107, baseEnd_2729107] using wordTrace_append hprefix tailTrace_2729107
  have hstable : (prefixWord ++ tailWord_2729107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729107).length < 2 ^ (prefixWord ++ tailWord_2729107).sum := by decide
  have hdescent : baseEnd_2729107 < baseStart_2729107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729118 : List Nat := [4, 3, 1, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_2729118 : Nat := 118140960795 + 2729118 * 2 ^ 59
def prefixEnd_2729118 : Nat := 4983230072969 + 3 ^ 40 * 2729118 * 2
def baseEnd_2729118 : Nat := 1401349296837158546974021

theorem tailTrace_2729118 : CollatzResearch.WordTrace tailWord_2729118 prefixEnd_2729118 1401349296837158546974021 := by
  unfold tailWord_2729118
  simp only [CollatzResearch.WordTrace]
  refine ⟨12442388865859882136461501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66359407284586038061128005 12442388865859882136461501)
  ·
    refine ⟨4665895824697455801173063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12442388865859882136461501 4665895824697455801173063)
    ·
      refine ⟨6998843737046183701759595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4665895824697455801173063 6998843737046183701759595)
      ·
        refine ⟨10498265605569275552639393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6998843737046183701759595 10498265605569275552639393)
        ·
          refine ⟨7873699204176956664479545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10498265605569275552639393 7873699204176956664479545)
          ·
            refine ⟨5905274403132717498359659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7873699204176956664479545 5905274403132717498359659)
            ·
              refine ⟨8857911604699076247539489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5905274403132717498359659 8857911604699076247539489)
              ·
                refine ⟨6643433703524307185654617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8857911604699076247539489 6643433703524307185654617)
                ·
                  refine ⟨4982575277643230389240963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6643433703524307185654617 4982575277643230389240963)
                  ·
                    refine ⟨7473862916464845583861445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4982575277643230389240963 7473862916464845583861445)
                    ·
                      refine ⟨1401349296837158546974021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7473862916464845583861445 1401349296837158546974021)
                      ·
                        rfl

theorem cell23_2729118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_2729118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729118 prefixEnd_2729118 := by exact prefixLift 2729118
  have htrace : WordTrace (prefixWord ++ tailWord_2729118) baseStart_2729118 baseEnd_2729118 := by
    simpa [prefixWord, tailWord_2729118, baseEnd_2729118] using wordTrace_append hprefix tailTrace_2729118
  have hstable : (prefixWord ++ tailWord_2729118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729118).length < 2 ^ (prefixWord ++ tailWord_2729118).sum := by decide
  have hdescent : baseEnd_2729118 < baseStart_2729118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729121 : List Nat := [1, 2, 3, 3, 1, 1, 3, 2, 2, 2, 3]
def baseStart_2729121 : Nat := 118140960795 + 2729121 * 2 ^ 59
def prefixEnd_2729121 : Nat := 4983230072969 + 3 ^ 40 * 2729121 * 2
def baseEnd_2729121 : Nat := 1401350837279122035236507

theorem tailTrace_2729121 : CollatzResearch.WordTrace tailWord_2729121 prefixEnd_2729121 1401350837279122035236507 := by
  unfold tailWord_2729121
  simp only [CollatzResearch.WordTrace]
  refine ⟨99539220345868188604051217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66359480230578792402700811 99539220345868188604051217)
  ·
    refine ⟨74654415259401141453038413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99539220345868188604051217 74654415259401141453038413)
    ·
      refine ⟨27995405722275428044889405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74654415259401141453038413 27995405722275428044889405)
      ·
        refine ⟨10498277145853285516833527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27995405722275428044889405 10498277145853285516833527)
        ·
          refine ⟨15747415718779928275250291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10498277145853285516833527 15747415718779928275250291)
          ·
            refine ⟨23621123578169892412875437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15747415718779928275250291 23621123578169892412875437)
            ·
              refine ⟨8857921341813709654828289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23621123578169892412875437 8857921341813709654828289)
              ·
                refine ⟨6643441006360282241121217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8857921341813709654828289 6643441006360282241121217)
                ·
                  refine ⟨4982580754770211680840913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6643441006360282241121217 4982580754770211680840913)
                  ·
                    refine ⟨3736935566077658760630685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4982580754770211680840913 3736935566077658760630685)
                    ·
                      refine ⟨1401350837279122035236507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3736935566077658760630685 1401350837279122035236507)
                      ·
                        rfl

theorem cell23_2729121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_2729121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729121 prefixEnd_2729121 := by exact prefixLift 2729121
  have htrace : WordTrace (prefixWord ++ tailWord_2729121) baseStart_2729121 baseEnd_2729121 := by
    simpa [prefixWord, tailWord_2729121, baseEnd_2729121] using wordTrace_append hprefix tailTrace_2729121
  have hstable : (prefixWord ++ tailWord_2729121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729121).length < 2 ^ (prefixWord ++ tailWord_2729121).sum := by decide
  have hdescent : baseEnd_2729121 < baseStart_2729121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729124 : List Nat := [2, 3, 1, 2, 3, 1, 2, 1, 8]
def baseStart_2729124 : Nat := 118140960795 + 2729124 * 2 ^ 59
def prefixEnd_2729124 : Nat := 4983230072969 + 3 ^ 40 * 2729124 * 2
def baseEnd_2729124 : Nat := 155705819746787280388777

theorem tailTrace_2729124 : CollatzResearch.WordTrace tailWord_2729124 prefixEnd_2729124 155705819746787280388777 := by
  unfold tailWord_2729124
  simp only [CollatzResearch.WordTrace]
  refine ⟨49769664882428660058205213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66359553176571546744273617 49769664882428660058205213)
  ·
    refine ⟨18663624330910747521826955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49769664882428660058205213 18663624330910747521826955)
    ·
      refine ⟨27995436496366121282740433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18663624330910747521826955 27995436496366121282740433)
      ·
        refine ⟨20996577372274590962055325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27995436496366121282740433 20996577372274590962055325)
        ·
          refine ⟨7873716514602971610770747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20996577372274590962055325 7873716514602971610770747)
          ·
            refine ⟨11810574771904457416156121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7873716514602971610770747 11810574771904457416156121)
            ·
              refine ⟨8857931078928343062117091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11810574771904457416156121 8857931078928343062117091)
              ·
                refine ⟨13286896618392514593175637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8857931078928343062117091 13286896618392514593175637)
                ·
                  refine ⟨155705819746787280388777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13286896618392514593175637 155705819746787280388777)
                  ·
                    rfl

theorem cell23_2729124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 8].length) (baseStart_2729124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729124 prefixEnd_2729124 := by exact prefixLift 2729124
  have htrace : WordTrace (prefixWord ++ tailWord_2729124) baseStart_2729124 baseEnd_2729124 := by
    simpa [prefixWord, tailWord_2729124, baseEnd_2729124] using wordTrace_append hprefix tailTrace_2729124
  have hstable : (prefixWord ++ tailWord_2729124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729124).length < 2 ^ (prefixWord ++ tailWord_2729124).sum := by decide
  have hdescent : baseEnd_2729124 < baseStart_2729124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729147 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 7]
def baseStart_2729147 : Nat := 118140960795 + 2729147 * 2 ^ 59
def prefixEnd_2729147 : Nat := 4983230072969 + 3 ^ 40 * 2729147 * 2
def baseEnd_2729147 : Nat := 1401364187776138933511387

theorem tailTrace_2729147 : CollatzResearch.WordTrace tailWord_2729147 prefixEnd_2729147 1401364187776138933511387 := by
  unfold tailWord_2729147
  simp only [CollatzResearch.WordTrace]
  refine ⟨99540168643773995044497695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66360112429182663362998463 99540168643773995044497695)
  ·
    refine ⟨149310252965660992566746543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99540168643773995044497695 149310252965660992566746543)
    ·
      refine ⟨223965379448491488850119815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149310252965660992566746543 223965379448491488850119815)
      ·
        refine ⟨335948069172737233275179723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223965379448491488850119815 335948069172737233275179723)
        ·
          refine ⟨503922103759105849912769585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335948069172737233275179723 503922103759105849912769585)
          ·
            refine ⟨377941577819329387434577189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 503922103759105849912769585 377941577819329387434577189)
            ·
              refine ⟨70864045841124260143983223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 377941577819329387434577189 70864045841124260143983223)
              ·
                refine ⟨106296068761686390215974835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70864045841124260143983223 106296068761686390215974835)
                ·
                  refine ⟨159444103142529585323962253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106296068761686390215974835 159444103142529585323962253)
                  ·
                    refine ⟨59791538678448594496485845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 159444103142529585323962253 59791538678448594496485845)
                    ·
                      refine ⟨1401364187776138933511387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59791538678448594496485845 1401364187776138933511387)
                      ·
                        rfl

theorem cell23_2729147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 7].length) (baseStart_2729147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729147 prefixEnd_2729147 := by exact prefixLift 2729147
  have htrace : WordTrace (prefixWord ++ tailWord_2729147) baseStart_2729147 baseEnd_2729147 := by
    simpa [prefixWord, tailWord_2729147, baseEnd_2729147] using wordTrace_append hprefix tailTrace_2729147
  have hstable : (prefixWord ++ tailWord_2729147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729147).length < 2 ^ (prefixWord ++ tailWord_2729147).sum := by decide
  have hdescent : baseEnd_2729147 < baseStart_2729147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729151 : List Nat := [1, 1, 2, 2, 2, 2, 2, 4, 3, 1, 3]
def baseStart_2729151 : Nat := 118140960795 + 2729151 * 2 ^ 59
def prefixEnd_2729151 : Nat := 4983230072969 + 3 ^ 40 * 2729151 * 2
def baseEnd_2729151 : Nat := 1401366241698756917861369

theorem tailTrace_2729151 : CollatzResearch.WordTrace tailWord_2729151 prefixEnd_2729151 1401366241698756917861369 := by
  unfold tailWord_2729151
  simp only [CollatzResearch.WordTrace]
  refine ⟨99540314535759503727643307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66360209690506335818428871 99540314535759503727643307)
  ·
    refine ⟨149310471803639255591464961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99540314535759503727643307 149310471803639255591464961)
    ·
      refine ⟨111982853852729441693598721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149310471803639255591464961 111982853852729441693598721)
      ·
        refine ⟨83987140389547081270199041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111982853852729441693598721 83987140389547081270199041)
        ·
          refine ⟨62990355292160310952649281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83987140389547081270199041 62990355292160310952649281)
          ·
            refine ⟨47242766469120233214486961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62990355292160310952649281 47242766469120233214486961)
            ·
              refine ⟨35432074851840174910865221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47242766469120233214486961 35432074851840174910865221)
              ·
                refine ⟨6643514034720032795787229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35432074851840174910865221 6643514034720032795787229)
                ·
                  refine ⟨2491317763020012298420211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6643514034720032795787229 2491317763020012298420211)
                  ·
                    refine ⟨3736976644530018447630317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2491317763020012298420211 3736976644530018447630317)
                    ·
                      refine ⟨1401366241698756917861369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3736976644530018447630317 1401366241698756917861369)
                      ·
                        rfl

theorem cell23_2729151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3, 1, 3].length) (baseStart_2729151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729151 prefixEnd_2729151 := by exact prefixLift 2729151
  have htrace : WordTrace (prefixWord ++ tailWord_2729151) baseStart_2729151 baseEnd_2729151 := by
    simpa [prefixWord, tailWord_2729151, baseEnd_2729151] using wordTrace_append hprefix tailTrace_2729151
  have hstable : (prefixWord ++ tailWord_2729151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729151).length < 2 ^ (prefixWord ++ tailWord_2729151).sum := by decide
  have hdescent : baseEnd_2729151 < baseStart_2729151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729185 : List Nat := [1, 2, 3, 1, 3, 3, 1, 4, 1, 1, 3]
def baseStart_2729185 : Nat := 118140960795 + 2729185 * 2 ^ 59
def prefixEnd_2729185 : Nat := 4983230072969 + 3 ^ 40 * 2729185 * 2
def baseEnd_2729185 : Nat := 1401383700041009784836213

theorem tailTrace_2729185 : CollatzResearch.WordTrace tailWord_2729185 prefixEnd_2729185 1401383700041009784836213 := by
  unfold tailWord_2729185
  simp only [CollatzResearch.WordTrace]
  refine ⟨99541554617636327534381009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66361036411757551689587339 99541554617636327534381009)
  ·
    refine ⟨74656165963227245650785757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99541554617636327534381009 74656165963227245650785757)
    ·
      refine ⟨27996062236210217119044659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74656165963227245650785757 27996062236210217119044659)
      ·
        refine ⟨41994093354315325678566989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27996062236210217119044659 41994093354315325678566989)
        ·
          refine ⟨15747785007868247129462621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41994093354315325678566989 15747785007868247129462621)
          ·
            refine ⟨5905419377950592673548483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15747785007868247129462621 5905419377950592673548483)
            ·
              refine ⟨8858129066925889010322725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5905419377950592673548483 8858129066925889010322725)
              ·
                refine ⟨1660899200048604189435511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8858129066925889010322725 1660899200048604189435511)
                ·
                  refine ⟨2491348800072906284153267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1660899200048604189435511 2491348800072906284153267)
                  ·
                    refine ⟨3737023200109359426229901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2491348800072906284153267 3737023200109359426229901)
                    ·
                      refine ⟨1401383700041009784836213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3737023200109359426229901 1401383700041009784836213)
                      ·
                        rfl

theorem cell23_2729185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4, 1, 1, 3].length) (baseStart_2729185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729185 prefixEnd_2729185 := by exact prefixLift 2729185
  have htrace : WordTrace (prefixWord ++ tailWord_2729185) baseStart_2729185 baseEnd_2729185 := by
    simpa [prefixWord, tailWord_2729185, baseEnd_2729185] using wordTrace_append hprefix tailTrace_2729185
  have hstable : (prefixWord ++ tailWord_2729185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729185).length < 2 ^ (prefixWord ++ tailWord_2729185).sum := by decide
  have hdescent : baseEnd_2729185 < baseStart_2729185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729212 : List Nat := [2, 2, 2, 1, 6, 1, 1, 1, 2, 3, 2]
def baseStart_2729212 : Nat := 118140960795 + 2729212 * 2 ^ 59
def prefixEnd_2729212 : Nat := 4983230072969 + 3 ^ 40 * 2729212 * 2
def baseEnd_2729212 : Nat := 1401397564018681179198589

theorem tailTrace_2729212 : CollatzResearch.WordTrace tailWord_2729212 prefixEnd_2729212 1401397564018681179198589 := by
  unfold tailWord_2729212
  simp only [CollatzResearch.WordTrace]
  refine ⟨49771269694269255572806945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66361692925692340763742593 49771269694269255572806945)
  ·
    refine ⟨37328452270701941679605209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49771269694269255572806945 37328452270701941679605209)
    ·
      refine ⟨27996339203026456259703907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37328452270701941679605209 27996339203026456259703907)
      ·
        refine ⟨41994508804539684389555861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27996339203026456259703907 41994508804539684389555861)
        ·
          refine ⟨1968492600212797705760431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41994508804539684389555861 1968492600212797705760431)
          ·
            refine ⟨2952738900319196558640647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1968492600212797705760431 2952738900319196558640647)
            ·
              refine ⟨4429108350478794837960971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2952738900319196558640647 4429108350478794837960971)
              ·
                refine ⟨6643662525718192256941457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4429108350478794837960971 6643662525718192256941457)
                ·
                  refine ⟨4982746894288644192706093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6643662525718192256941457 4982746894288644192706093)
                  ·
                    refine ⟨1868530085358241572264785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4982746894288644192706093 1868530085358241572264785)
                    ·
                      refine ⟨1401397564018681179198589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1868530085358241572264785 1401397564018681179198589)
                      ·
                        rfl

theorem cell23_2729212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 2, 3, 2].length) (baseStart_2729212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729212 prefixEnd_2729212 := by exact prefixLift 2729212
  have htrace : WordTrace (prefixWord ++ tailWord_2729212) baseStart_2729212 baseEnd_2729212 := by
    simpa [prefixWord, tailWord_2729212, baseEnd_2729212] using wordTrace_append hprefix tailTrace_2729212
  have hstable : (prefixWord ++ tailWord_2729212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729212).length < 2 ^ (prefixWord ++ tailWord_2729212).sum := by decide
  have hdescent : baseEnd_2729212 < baseStart_2729212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729228 : List Nat := [2, 2, 1, 2, 2, 4, 1, 3, 1, 2, 3]
def baseStart_2729228 : Nat := 118140960795 + 2729228 * 2 ^ 59
def prefixEnd_2729228 : Nat := 4983230072969 + 3 ^ 40 * 2729228 * 2
def baseEnd_2729228 : Nat := 1401405779709153116598515

theorem tailTrace_2729228 : CollatzResearch.WordTrace tailWord_2729228 prefixEnd_2729228 1401405779709153116598515 := by
  unfold tailWord_2729228
  simp only [CollatzResearch.WordTrace]
  refine ⟨49771561478240272939098169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66362081970987030585464225 49771561478240272939098169)
  ·
    refine ⟨37328671108680204704323627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49771561478240272939098169 37328671108680204704323627)
    ·
      refine ⟨55993006663020307056485441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37328671108680204704323627 55993006663020307056485441)
      ·
        refine ⟨41994754997265230292364081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55993006663020307056485441 41994754997265230292364081)
        ·
          refine ⟨31496066247948922719273061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41994754997265230292364081 31496066247948922719273061)
          ·
            refine ⟨5905512421490423009863699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31496066247948922719273061 5905512421490423009863699)
            ·
              refine ⟨8858268632235634514795549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5905512421490423009863699 8858268632235634514795549)
              ·
                refine ⟨3321850737088362943048331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8858268632235634514795549 3321850737088362943048331)
                ·
                  refine ⟨4982776105632544414572497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3321850737088362943048331 4982776105632544414572497)
                  ·
                    refine ⟨3737082079224408310929373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4982776105632544414572497 3737082079224408310929373)
                    ·
                      refine ⟨1401405779709153116598515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3737082079224408310929373 1401405779709153116598515)
                      ·
                        rfl

theorem cell23_2729228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_2729228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729228 prefixEnd_2729228 := by exact prefixLift 2729228
  have htrace : WordTrace (prefixWord ++ tailWord_2729228) baseStart_2729228 baseEnd_2729228 := by
    simpa [prefixWord, tailWord_2729228, baseEnd_2729228] using wordTrace_append hprefix tailTrace_2729228
  have hstable : (prefixWord ++ tailWord_2729228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729228).length < 2 ^ (prefixWord ++ tailWord_2729228).sum := by decide
  have hdescent : baseEnd_2729228 < baseStart_2729228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729242 : List Nat := [3, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2]
def baseStart_2729242 : Nat := 118140960795 + 2729242 * 2 ^ 59
def prefixEnd_2729242 : Nat := 4983230072969 + 3 ^ 40 * 2729242 * 2
def baseEnd_2729242 : Nat := 1401412968438316061823451

theorem tailTrace_2729242 : CollatzResearch.WordTrace tailWord_2729242 prefixEnd_2729242 1401412968438316061823451 := by
  unfold tailWord_2729242
  simp only [CollatzResearch.WordTrace]
  refine ⟨24885908394607456567301495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66362422385619884179470653 24885908394607456567301495)
  ·
    refine ⟨37328862591911184850952243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24885908394607456567301495 37328862591911184850952243)
    ·
      refine ⟨55993293887866777276428365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37328862591911184850952243 55993293887866777276428365)
      ·
        refine ⟨20997485207950041478660637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55993293887866777276428365 20997485207950041478660637)
        ·
          refine ⟨7874056952981265554497739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20997485207950041478660637 7874056952981265554497739)
          ·
            refine ⟨11811085429471898331746609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7874056952981265554497739 11811085429471898331746609)
            ·
              refine ⟨8858314072103923748809957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11811085429471898331746609 8858314072103923748809957)
              ·
                refine ⟨1660933888519485702901867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8858314072103923748809957 1660933888519485702901867)
                ·
                  refine ⟨2491400832779228554352801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1660933888519485702901867 2491400832779228554352801)
                  ·
                    refine ⟨1868550624584421415764601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2491400832779228554352801 1868550624584421415764601)
                    ·
                      refine ⟨1401412968438316061823451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1868550624584421415764601 1401412968438316061823451)
                      ·
                        rfl

theorem cell23_2729242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_2729242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729242 prefixEnd_2729242 := by exact prefixLift 2729242
  have htrace : WordTrace (prefixWord ++ tailWord_2729242) baseStart_2729242 baseEnd_2729242 := by
    simpa [prefixWord, tailWord_2729242, baseEnd_2729242] using wordTrace_append hprefix tailTrace_2729242
  have hstable : (prefixWord ++ tailWord_2729242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729242).length < 2 ^ (prefixWord ++ tailWord_2729242).sum := by decide
  have hdescent : baseEnd_2729242 < baseStart_2729242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729244 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 1, 9]
def baseStart_2729244 : Nat := 118140960795 + 2729244 * 2 ^ 59
def prefixEnd_2729244 : Nat := 4983230072969 + 3 ^ 40 * 2729244 * 2
def baseEnd_2729244 : Nat := 467137998466541684666147

theorem tailTrace_2729244 : CollatzResearch.WordTrace tailWord_2729244 prefixEnd_2729244 467137998466541684666147 := by
  unfold tailWord_2729244
  simp only [CollatzResearch.WordTrace]
  refine ⟨49771853262211290305389393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66362471016281720407185857 49771853262211290305389393)
  ·
    refine ⟨37328889946658467729042045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49771853262211290305389393 37328889946658467729042045)
    ·
      refine ⟨13998333729996925398390767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37328889946658467729042045 13998333729996925398390767)
      ·
        refine ⟨20997500594995388097586151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13998333729996925398390767 20997500594995388097586151)
        ·
          refine ⟨31496250892493082146379227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20997500594995388097586151 31496250892493082146379227)
          ·
            refine ⟨47244376338739623219568841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31496250892493082146379227 47244376338739623219568841)
            ·
              refine ⟨35433282254054717414676631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47244376338739623219568841 35433282254054717414676631)
              ·
                refine ⟨53149923381082076122014947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35433282254054717414676631 53149923381082076122014947)
                ·
                  refine ⟨79724885071623114183022421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53149923381082076122014947 79724885071623114183022421)
                  ·
                    refine ⟨467137998466541684666147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 79724885071623114183022421 467137998466541684666147)
                    ·
                      rfl

theorem cell23_2729244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_2729244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729244 prefixEnd_2729244 := by exact prefixLift 2729244
  have htrace : WordTrace (prefixWord ++ tailWord_2729244) baseStart_2729244 baseEnd_2729244 := by
    simpa [prefixWord, tailWord_2729244, baseEnd_2729244] using wordTrace_append hprefix tailTrace_2729244
  have hstable : (prefixWord ++ tailWord_2729244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729244).length < 2 ^ (prefixWord ++ tailWord_2729244).sum := by decide
  have hdescent : baseEnd_2729244 < baseStart_2729244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729293 : List Nat := [1, 6, 1, 3, 1, 1, 3, 2, 1, 2, 2]
def baseStart_2729293 : Nat := 118140960795 + 2729293 * 2 ^ 59
def prefixEnd_2729293 : Nat := 4983230072969 + 3 ^ 40 * 2729293 * 2
def baseEnd_2729293 : Nat := 1401439155951695362285717

theorem tailTrace_2729293 : CollatzResearch.WordTrace tailWord_2729293 prefixEnd_2729293 1401439155951695362285717 := by
  unfold tailWord_2729293
  simp only [CollatzResearch.WordTrace]
  refine ⟨99545493701245061979312533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66363662467496707986208355 99545493701245061979312533)
  ·
    refine ⟨4666195017245862280280275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 99545493701245061979312533 4666195017245862280280275)
    ·
      refine ⟨6999292525868793420420413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4666195017245862280280275 6999292525868793420420413)
      ·
        refine ⟨2624734697200797532657655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6999292525868793420420413 2624734697200797532657655)
        ·
          refine ⟨3937102045801196298986483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2624734697200797532657655 3937102045801196298986483)
          ·
            refine ⟨5905653068701794448479725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3937102045801196298986483 5905653068701794448479725)
            ·
              refine ⟨2214619900763172918179897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5905653068701794448479725 2214619900763172918179897)
              ·
                refine ⟨1660964925572379688634923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2214619900763172918179897 1660964925572379688634923)
                ·
                  refine ⟨2491447388358569532952385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1660964925572379688634923 2491447388358569532952385)
                  ·
                    refine ⟨1868585541268927149714289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2491447388358569532952385 1868585541268927149714289)
                    ·
                      refine ⟨1401439155951695362285717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1868585541268927149714289 1401439155951695362285717)
                      ·
                        rfl

theorem cell23_2729293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_2729293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729293 prefixEnd_2729293 := by exact prefixLift 2729293
  have htrace : WordTrace (prefixWord ++ tailWord_2729293) baseStart_2729293 baseEnd_2729293 := by
    simpa [prefixWord, tailWord_2729293, baseEnd_2729293] using wordTrace_append hprefix tailTrace_2729293
  have hstable : (prefixWord ++ tailWord_2729293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729293).length < 2 ^ (prefixWord ++ tailWord_2729293).sum := by decide
  have hdescent : baseEnd_2729293 < baseStart_2729293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729319 : List Nat := [1, 1, 5, 1, 5, 1, 1, 2, 1, 3, 2]
def baseStart_2729319 : Nat := 118140960795 + 2729319 * 2 ^ 59
def prefixEnd_2729319 : Nat := 4983230072969 + 3 ^ 40 * 2729319 * 2
def baseEnd_2729319 : Nat := 1401452506448712260560597

theorem tailTrace_2729319 : CollatzResearch.WordTrace tailWord_2729319 prefixEnd_2729319 1401452506448712260560597 := by
  unfold tailWord_2729319
  simp only [CollatzResearch.WordTrace]
  refine ⟨99546441999150868419759011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66364294666100578946506007 99546441999150868419759011)
  ·
    refine ⟨149319662998726302629638517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99546441999150868419759011 149319662998726302629638517)
    ·
      refine ⟨13998718406130590871528611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149319662998726302629638517 13998718406130590871528611)
      ·
        refine ⟨20998077609195886307292917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13998718406130590871528611 20998077609195886307292917)
        ·
          refine ⟨1968569775862114341308711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20998077609195886307292917 1968569775862114341308711)
          ·
            refine ⟨2952854663793171511963067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1968569775862114341308711 2952854663793171511963067)
            ·
              refine ⟨4429281995689757267944601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2952854663793171511963067 4429281995689757267944601)
              ·
                refine ⟨3321961496767317950958451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4429281995689757267944601 3321961496767317950958451)
                ·
                  refine ⟨4982942245150976926437677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3321961496767317950958451 4982942245150976926437677)
                  ·
                    refine ⟨1868603341931616347414129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4982942245150976926437677 1868603341931616347414129)
                    ·
                      refine ⟨1401452506448712260560597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1868603341931616347414129 1401452506448712260560597)
                      ·
                        rfl

theorem cell23_2729319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_2729319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729319 prefixEnd_2729319 := by exact prefixLift 2729319
  have htrace : WordTrace (prefixWord ++ tailWord_2729319) baseStart_2729319 baseEnd_2729319 := by
    simpa [prefixWord, tailWord_2729319, baseEnd_2729319] using wordTrace_append hprefix tailTrace_2729319
  have hstable : (prefixWord ++ tailWord_2729319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729319).length < 2 ^ (prefixWord ++ tailWord_2729319).sum := by decide
  have hdescent : baseEnd_2729319 < baseStart_2729319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729388 : List Nat := [2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 4]
def baseStart_2729388 : Nat := 118140960795 + 2729388 * 2 ^ 59
def prefixEnd_2729388 : Nat := 4983230072969 + 3 ^ 40 * 2729388 * 2
def baseEnd_2729388 : Nat := 1401487936613872490597779

theorem tailTrace_2729388 : CollatzResearch.WordTrace tailWord_2729388 prefixEnd_2729388 1401487936613872490597779 := by
  unfold tailWord_2729388
  simp only [CollatzResearch.WordTrace]
  refine ⟨49774479317950446602010409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66365972423933928802680545 49774479317950446602010409)
  ·
    refine ⟨37330859488462834951507807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49774479317950446602010409 37330859488462834951507807)
    ·
      refine ⟨55996289232694252427261711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37330859488462834951507807 55996289232694252427261711)
      ·
        refine ⟨83994433849041378640892567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55996289232694252427261711 83994433849041378640892567)
        ·
          refine ⟨125991650773562067961338851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83994433849041378640892567 125991650773562067961338851)
          ·
            refine ⟨188987476160343101942008277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125991650773562067961338851 188987476160343101942008277)
            ·
              refine ⟨4429393972508041451765819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 188987476160343101942008277 4429393972508041451765819)
              ·
                refine ⟨6644090958762062177648729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4429393972508041451765819 6644090958762062177648729)
                ·
                  refine ⟨4983068219071546633236547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6644090958762062177648729 4983068219071546633236547)
                  ·
                    refine ⟨7474602328607319949854821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4983068219071546633236547 7474602328607319949854821)
                    ·
                      refine ⟨1401487936613872490597779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7474602328607319949854821 1401487936613872490597779)
                      ·
                        rfl

theorem cell23_2729388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 4].length) (baseStart_2729388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729388 prefixEnd_2729388 := by exact prefixLift 2729388
  have htrace : WordTrace (prefixWord ++ tailWord_2729388) baseStart_2729388 baseEnd_2729388 := by
    simpa [prefixWord, tailWord_2729388, baseEnd_2729388] using wordTrace_append hprefix tailTrace_2729388
  have hstable : (prefixWord ++ tailWord_2729388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729388).length < 2 ^ (prefixWord ++ tailWord_2729388).sum := by decide
  have hdescent : baseEnd_2729388 < baseStart_2729388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729408 : List Nat := [2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 3]
def baseStart_2729408 : Nat := 118140960795 + 2729408 * 2 ^ 59
def prefixEnd_2729408 : Nat := 4983230072969 + 3 ^ 40 * 2729408 * 2
def baseEnd_2729408 : Nat := 1401498206226962412347687

theorem tailTrace_2729408 : CollatzResearch.WordTrace tailWord_2729408 prefixEnd_2729408 1401498206226962412347687 := by
  unfold tailWord_2729408
  simp only [CollatzResearch.WordTrace]
  refine ⟨49774844047914218309874439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66366458730552291079832585 49774844047914218309874439)
  ·
    refine ⟨74662266071871327464811659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49774844047914218309874439 74662266071871327464811659)
    ·
      refine ⟨111993399107806991197217489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74662266071871327464811659 111993399107806991197217489)
      ·
        refine ⟨83995049330855243397913117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111993399107806991197217489 83995049330855243397913117)
        ·
          refine ⟨31498143499070716274217419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83995049330855243397913117 31498143499070716274217419)
          ·
            refine ⟨47247215248606074411326129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31498143499070716274217419 47247215248606074411326129)
            ·
              refine ⟨35435411436454555808494597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47247215248606074411326129 35435411436454555808494597)
              ·
                refine ⟨6644139644335229214092737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35435411436454555808494597 6644139644335229214092737)
                ·
                  refine ⟨4983104733251421910569553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6644139644335229214092737 4983104733251421910569553)
                  ·
                    refine ⟨3737328549938566432927165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4983104733251421910569553 3737328549938566432927165)
                    ·
                      refine ⟨1401498206226962412347687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3737328549938566432927165 1401498206226962412347687)
                      ·
                        rfl

theorem cell23_2729408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 3].length) (baseStart_2729408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729408 prefixEnd_2729408 := by exact prefixLift 2729408
  have htrace : WordTrace (prefixWord ++ tailWord_2729408) baseStart_2729408 baseEnd_2729408 := by
    simpa [prefixWord, tailWord_2729408, baseEnd_2729408] using wordTrace_append hprefix tailTrace_2729408
  have hstable : (prefixWord ++ tailWord_2729408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729408).length < 2 ^ (prefixWord ++ tailWord_2729408).sum := by decide
  have hdescent : baseEnd_2729408 < baseStart_2729408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729415 : List Nat := [1, 1, 4, 1, 1, 3, 1, 6, 1, 4]
def baseStart_2729415 : Nat := 118140960795 + 2729415 * 2 ^ 59
def prefixEnd_2729415 : Nat := 4983230072969 + 3 ^ 40 * 2729415 * 2
def baseEnd_2729415 : Nat := 467167266863847961653385

theorem tailTrace_2729415 : CollatzResearch.WordTrace tailWord_2729415 prefixEnd_2729415 467167266863847961653385 := by
  unfold tailWord_2729415
  simp only [CollatzResearch.WordTrace]
  refine ⟨99549943406803076815253699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66366628937868717876835799 99549943406803076815253699)
  ·
    refine ⟨149324915110204615222880549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99549943406803076815253699 149324915110204615222880549)
    ·
      refine ⟨27998421583163365354290103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149324915110204615222880549 27998421583163365354290103)
      ·
        refine ⟨41997632374745048031435155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27998421583163365354290103 41997632374745048031435155)
        ·
          refine ⟨62996448562117572047152733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41997632374745048031435155 62996448562117572047152733)
          ·
            refine ⟨23623668210794089517682275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62996448562117572047152733 23623668210794089517682275)
            ·
              refine ⟨35435502316191134276523413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23623668210794089517682275 35435502316191134276523413)
              ·
                refine ⟨1661039171071459419212035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35435502316191134276523413 1661039171071459419212035)
                ·
                  refine ⟨2491558756607189128818053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1661039171071459419212035 2491558756607189128818053)
                  ·
                    refine ⟨467167266863847961653385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2491558756607189128818053 467167266863847961653385)
                    ·
                      rfl

theorem cell23_2729415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_2729415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729415 prefixEnd_2729415 := by exact prefixLift 2729415
  have htrace : WordTrace (prefixWord ++ tailWord_2729415) baseStart_2729415 baseEnd_2729415 := by
    simpa [prefixWord, tailWord_2729415, baseEnd_2729415] using wordTrace_append hprefix tailTrace_2729415
  have hstable : (prefixWord ++ tailWord_2729415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729415).length < 2 ^ (prefixWord ++ tailWord_2729415).sum := by decide
  have hdescent : baseEnd_2729415 < baseStart_2729415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729471 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 5, 6]
def baseStart_2729471 : Nat := 118140960795 + 2729471 * 2 ^ 59
def prefixEnd_2729471 : Nat := 4983230072969 + 3 ^ 40 * 2729471 * 2
def baseEnd_2729471 : Nat := 467176851836065221953299

theorem tailTrace_2729471 : CollatzResearch.WordTrace tailWord_2729471 prefixEnd_2729471 467176851836065221953299 := by
  unfold tailWord_2729471
  simp only [CollatzResearch.WordTrace]
  refine ⟨99551985894600198379292267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66367990596400132252861511 99551985894600198379292267)
  ·
    refine ⟨149327978841900297568938401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99551985894600198379292267 149327978841900297568938401)
    ·
      refine ⟨111995984131425223176703801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149327978841900297568938401 111995984131425223176703801)
      ·
        refine ⟨83996988098568917382527851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111995984131425223176703801 83996988098568917382527851)
        ·
          refine ⟨125995482147853376073791777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83996988098568917382527851 125995482147853376073791777)
          ·
            refine ⟨94496611610890032055343833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125995482147853376073791777 94496611610890032055343833)
            ·
              refine ⟨70872458708167524041507875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94496611610890032055343833 70872458708167524041507875)
              ·
                refine ⟨106308688062251286062261813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70872458708167524041507875 106308688062251286062261813)
                ·
                  refine ⟨9966439505836058068337045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106308688062251286062261813 9966439505836058068337045)
                  ·
                    refine ⟨467176851836065221953299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9966439505836058068337045 467176851836065221953299)
                    ·
                      rfl

theorem cell23_2729471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 6].length) (baseStart_2729471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729471 prefixEnd_2729471 := by exact prefixLift 2729471
  have htrace : WordTrace (prefixWord ++ tailWord_2729471) baseStart_2729471 baseEnd_2729471 := by
    simpa [prefixWord, tailWord_2729471, baseEnd_2729471] using wordTrace_append hprefix tailTrace_2729471
  have hstable : (prefixWord ++ tailWord_2729471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729471).length < 2 ^ (prefixWord ++ tailWord_2729471).sum := by decide
  have hdescent : baseEnd_2729471 < baseStart_2729471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729492 : List Nat := [2, 4, 3, 1, 2, 1, 1, 1, 3, 5]
def baseStart_2729492 : Nat := 118140960795 + 2729492 * 2 ^ 59
def prefixEnd_2729492 : Nat := 4983230072969 + 3 ^ 40 * 2729492 * 2
def baseEnd_2729492 : Nat := 467180446200646694565767

theorem tailTrace_2729492 : CollatzResearch.WordTrace tailWord_2729492 prefixEnd_2729492 467180446200646694565767 := by
  unfold tailWord_2729492
  simp only [CollatzResearch.WordTrace]
  refine ⟨49776375913762059482903365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66368501218349412643871153 49776375913762059482903365)
  ·
    refine ⟨9333070483830386153044381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49776375913762059482903365 9333070483830386153044381)
    ·
      refine ⟨3499901431436394807391643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9333070483830386153044381 3499901431436394807391643)
      ·
        refine ⟨5249852147154592211087465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3499901431436394807391643 5249852147154592211087465)
        ·
          refine ⟨3937389110365944158315599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5249852147154592211087465 3937389110365944158315599)
          ·
            refine ⟨5906083665548916237473399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3937389110365944158315599 5906083665548916237473399)
            ·
              refine ⟨8859125498323374356210099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5906083665548916237473399 8859125498323374356210099)
              ·
                refine ⟨13288688247485061534315149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8859125498323374356210099 13288688247485061534315149)
                ·
                  refine ⟨4983258092806898075368181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13288688247485061534315149 4983258092806898075368181)
                  ·
                    refine ⟨467180446200646694565767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4983258092806898075368181 467180446200646694565767)
                    ·
                      rfl

theorem cell23_2729492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_2729492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729492 prefixEnd_2729492 := by exact prefixLift 2729492
  have htrace : WordTrace (prefixWord ++ tailWord_2729492) baseStart_2729492 baseEnd_2729492 := by
    simpa [prefixWord, tailWord_2729492, baseEnd_2729492] using wordTrace_append hprefix tailTrace_2729492
  have hstable : (prefixWord ++ tailWord_2729492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729492).length < 2 ^ (prefixWord ++ tailWord_2729492).sum := by decide
  have hdescent : baseEnd_2729492 < baseStart_2729492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729518 : List Nat := [4, 1, 3, 1, 2, 12]
def baseStart_2729518 : Nat := 118140960795 + 2729518 * 2 ^ 59
def prefixEnd_2729518 : Nat := 4983230072969 + 3 ^ 40 * 2729518 * 2
def baseEnd_2729518 : Nat := 5767714769954555481367

theorem tailTrace_2729518 : CollatzResearch.WordTrace tailWord_2729518 prefixEnd_2729518 5767714769954555481367 := by
  unfold tailWord_2729518
  simp only [CollatzResearch.WordTrace]
  refine ⟨12444212515678740675781651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66369133416953283604168805 12444212515678740675781651)
  ·
    refine ⟨18666318773518111013672477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12444212515678740675781651 18666318773518111013672477)
    ·
      refine ⟨6999869540069291630127179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18666318773518111013672477 6999869540069291630127179)
      ·
        refine ⟨10499804310103937445190769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6999869540069291630127179 10499804310103937445190769)
        ·
          refine ⟨7874853232577953083893077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10499804310103937445190769 7874853232577953083893077)
          ·
            refine ⟨5767714769954555481367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 7874853232577953083893077 5767714769954555481367)
            ·
              rfl

theorem cell23_2729518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 12].length) (baseStart_2729518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729518 prefixEnd_2729518 := by exact prefixLift 2729518
  have htrace : WordTrace (prefixWord ++ tailWord_2729518) baseStart_2729518 baseEnd_2729518 := by
    simpa [prefixWord, tailWord_2729518, baseEnd_2729518] using wordTrace_append hprefix tailTrace_2729518
  have hstable : (prefixWord ++ tailWord_2729518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729518).length < 2 ^ (prefixWord ++ tailWord_2729518).sum := by decide
  have hdescent : baseEnd_2729518 < baseStart_2729518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729585 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 3, 4, 2]
def baseStart_2729585 : Nat := 118140960795 + 2729585 * 2 ^ 59
def prefixEnd_2729585 : Nat := 4983230072969 + 3 ^ 40 * 2729585 * 2
def baseEnd_2729585 : Nat := 1401589092302808219834373

theorem tailTrace_2729585 : CollatzResearch.WordTrace tailWord_2729585 prefixEnd_2729585 1401589092302808219834373 := by
  unfold tailWord_2729585
  simp only [CollatzResearch.WordTrace]
  refine ⟨99556143816187195848942209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66370762544124797232628139 99556143816187195848942209)
  ·
    refine ⟨74667107862140396886706657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99556143816187195848942209 74667107862140396886706657)
    ·
      refine ⟨56000330896605297665029993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74667107862140396886706657 56000330896605297665029993)
      ·
        refine ⟨42000248172453973248772495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56000330896605297665029993 42000248172453973248772495)
        ·
          refine ⟨63000372258680959873158743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42000248172453973248772495 63000372258680959873158743)
          ·
            refine ⟨94500558388021439809738115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63000372258680959873158743 94500558388021439809738115)
            ·
              refine ⟨141750837582032159714607173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94500558388021439809738115 141750837582032159714607173)
              ·
                refine ⟨26578282046631029946488845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141750837582032159714607173 26578282046631029946488845)
                ·
                  refine ⟨9966855767486636229933317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26578282046631029946488845 9966855767486636229933317)
                  ·
                    refine ⟨1868785456403744293112497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9966855767486636229933317 1868785456403744293112497)
                    ·
                      refine ⟨1401589092302808219834373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1868785456403744293112497 1401589092302808219834373)
                      ·
                        rfl

theorem cell23_2729585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 4, 2].length) (baseStart_2729585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729585 prefixEnd_2729585 := by exact prefixLift 2729585
  have htrace : WordTrace (prefixWord ++ tailWord_2729585) baseStart_2729585 baseEnd_2729585 := by
    simpa [prefixWord, tailWord_2729585, baseEnd_2729585] using wordTrace_append hprefix tailTrace_2729585
  have hstable : (prefixWord ++ tailWord_2729585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729585).length < 2 ^ (prefixWord ++ tailWord_2729585).sum := by decide
  have hdescent : baseEnd_2729585 < baseStart_2729585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729625 : List Nat := [1, 2, 1, 2, 1, 2, 2, 7, 5]
def baseStart_2729625 : Nat := 118140960795 + 2729625 * 2 ^ 59
def prefixEnd_2729625 : Nat := 4983230072969 + 3 ^ 40 * 2729625 * 2
def baseEnd_2729625 : Nat := 155734403503220895926021

theorem tailTrace_2729625 : CollatzResearch.WordTrace tailWord_2729625 prefixEnd_2729625 155734403503220895926021 := by
  unfold tailWord_2729625
  simp only [CollatzResearch.WordTrace]
  refine ⟨99557602736042282680398329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66371735157361521786932219 99557602736042282680398329)
  ·
    refine ⟨74668202052031712010298747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99557602736042282680398329 74668202052031712010298747)
    ·
      refine ⟨112002303078047568015448121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74668202052031712010298747 112002303078047568015448121)
      ·
        refine ⟨84001727308535676011586091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112002303078047568015448121 84001727308535676011586091)
        ·
          refine ⟨126002590962803514017379137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84001727308535676011586091 126002590962803514017379137)
          ·
            refine ⟨94501943222102635513034353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126002590962803514017379137 94501943222102635513034353)
            ·
              refine ⟨70876457416576976634775765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94501943222102635513034353 70876457416576976634775765)
              ·
                refine ⟨1661166970701022889877557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 70876457416576976634775765 1661166970701022889877557)
                ·
                  refine ⟨155734403503220895926021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1661166970701022889877557 155734403503220895926021)
                  ·
                    rfl

theorem cell23_2729625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7, 5].length) (baseStart_2729625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729625 prefixEnd_2729625 := by exact prefixLift 2729625
  have htrace : WordTrace (prefixWord ++ tailWord_2729625) baseStart_2729625 baseEnd_2729625 := by
    simpa [prefixWord, tailWord_2729625, baseEnd_2729625] using wordTrace_append hprefix tailTrace_2729625
  have hstable : (prefixWord ++ tailWord_2729625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729625).length < 2 ^ (prefixWord ++ tailWord_2729625).sum := by decide
  have hdescent : baseEnd_2729625 < baseStart_2729625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729648 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 7]
def baseStart_2729648 : Nat := 118140960795 + 2729648 * 2 ^ 59
def prefixEnd_2729648 : Nat := 4983230072969 + 3 ^ 40 * 2729648 * 2
def baseEnd_2729648 : Nat := 1401621441584041473346583

theorem tailTrace_2729648 : CollatzResearch.WordTrace tailWord_2729648 prefixEnd_2729648 1401621441584041473346583 := by
  unfold tailWord_2729648
  simp only [CollatzResearch.WordTrace]
  refine ⟨49779220807479478804242799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66372294409972638405657065 49779220807479478804242799)
  ·
    refine ⟨74668831211219218206364199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49779220807479478804242799 74668831211219218206364199)
    ·
      refine ⟨112003246816828827309546299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74668831211219218206364199 112003246816828827309546299)
      ·
        refine ⟨168004870225243240964319449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112003246816828827309546299 168004870225243240964319449)
        ·
          refine ⟨126003652668932430723239587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168004870225243240964319449 126003652668932430723239587)
          ·
            refine ⟨189005479003398646084859381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126003652668932430723239587 189005479003398646084859381)
            ·
              refine ⟨17719263656568623070455567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 189005479003398646084859381 17719263656568623070455567)
              ·
                refine ⟨26578895484852934605683351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17719263656568623070455567 26578895484852934605683351)
                ·
                  refine ⟨39868343227279401908525027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26578895484852934605683351 39868343227279401908525027)
                  ·
                    refine ⟨59802514840919102862787541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39868343227279401908525027 59802514840919102862787541)
                    ·
                      refine ⟨1401621441584041473346583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59802514840919102862787541 1401621441584041473346583)
                      ·
                        rfl

theorem cell23_2729648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 7].length) (baseStart_2729648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729648 prefixEnd_2729648 := by exact prefixLift 2729648
  have htrace : WordTrace (prefixWord ++ tailWord_2729648) baseStart_2729648 baseEnd_2729648 := by
    simpa [prefixWord, tailWord_2729648, baseEnd_2729648] using wordTrace_append hprefix tailTrace_2729648
  have hstable : (prefixWord ++ tailWord_2729648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729648).length < 2 ^ (prefixWord ++ tailWord_2729648).sum := by decide
  have hdescent : baseEnd_2729648 < baseStart_2729648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729693 : List Nat := [1, 4, 3, 3, 1, 2, 2, 2, 5]
def baseStart_2729693 : Nat := 118140960795 + 2729693 * 2 ^ 59
def prefixEnd_2729693 : Nat := 4983230072969 + 3 ^ 40 * 2729693 * 2
def baseEnd_2729693 : Nat := 155738283134832644142653

theorem tailTrace_2729693 : CollatzResearch.WordTrace tailWord_2729693 prefixEnd_2729693 155738283134832644142653 := by
  unfold tailWord_2729693
  simp only [CollatzResearch.WordTrace]
  refine ⟨99560082899795930293873733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66373388599863953529249155 99560082899795930293873733)
  ·
    refine ⟨18667515543711736930101325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99560082899795930293873733 18667515543711736930101325)
    ·
      refine ⟨7000318328891901348787997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18667515543711736930101325 7000318328891901348787997)
      ·
        refine ⟨2625119373334463005795499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7000318328891901348787997 2625119373334463005795499)
        ·
          refine ⟨3937679060001694508693249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2625119373334463005795499 3937679060001694508693249)
          ·
            refine ⟨2953259295001270881519937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3937679060001694508693249 2953259295001270881519937)
            ·
              refine ⟨2214944471250953161139953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2953259295001270881519937 2214944471250953161139953)
              ·
                refine ⟨1661208353438214870854965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2214944471250953161139953 1661208353438214870854965)
                ·
                  refine ⟨155738283134832644142653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1661208353438214870854965 155738283134832644142653)
                  ·
                    rfl

theorem cell23_2729693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2, 5].length) (baseStart_2729693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729693 prefixEnd_2729693 := by exact prefixLift 2729693
  have htrace : WordTrace (prefixWord ++ tailWord_2729693) baseStart_2729693 baseEnd_2729693 := by
    simpa [prefixWord, tailWord_2729693, baseEnd_2729693] using wordTrace_append hprefix tailTrace_2729693
  have hstable : (prefixWord ++ tailWord_2729693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729693).length < 2 ^ (prefixWord ++ tailWord_2729693).sum := by decide
  have hdescent : baseEnd_2729693 < baseStart_2729693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729709 : List Nat := [1, 5, 1, 2, 1, 3, 1, 1, 2, 4, 2]
def baseStart_2729709 : Nat := 118140960795 + 2729709 * 2 ^ 59
def prefixEnd_2729709 : Nat := 4983230072969 + 3 ^ 40 * 2729709 * 2
def baseEnd_2729709 : Nat := 1401652763903965734683803

theorem tailTrace_2729709 : CollatzResearch.WordTrace tailWord_2729709 prefixEnd_2729709 1401652763903965734683803 := by
  unfold tailWord_2729709
  simp only [CollatzResearch.WordTrace]
  refine ⟨99560666467737965026456181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66373777645158643350970787 99560666467737965026456181)
  ·
    refine ⟨9333812481350434221230267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99560666467737965026456181 9333812481350434221230267)
    ·
      refine ⟨14000718722025651331845401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9333812481350434221230267 14000718722025651331845401)
      ·
        refine ⟨10500539041519238498884051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14000718722025651331845401 10500539041519238498884051)
        ·
          refine ⟨15750808562278857748326077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10500539041519238498884051 15750808562278857748326077)
          ·
            refine ⟨5906553210854571655622279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15750808562278857748326077 5906553210854571655622279)
            ·
              refine ⟨8859829816281857483433419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5906553210854571655622279 8859829816281857483433419)
              ·
                refine ⟨13289744724422786225150129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8859829816281857483433419 13289744724422786225150129)
                ·
                  refine ⟨9967308543317089668862597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13289744724422786225150129 9967308543317089668862597)
                  ·
                    refine ⟨1868870351871954312911737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9967308543317089668862597 1868870351871954312911737)
                    ·
                      refine ⟨1401652763903965734683803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1868870351871954312911737 1401652763903965734683803)
                      ·
                        rfl

theorem cell23_2729709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_2729709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729709 prefixEnd_2729709 := by exact prefixLift 2729709
  have htrace : WordTrace (prefixWord ++ tailWord_2729709) baseStart_2729709 baseEnd_2729709 := by
    simpa [prefixWord, tailWord_2729709, baseEnd_2729709] using wordTrace_append hprefix tailTrace_2729709
  have hstable : (prefixWord ++ tailWord_2729709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729709).length < 2 ^ (prefixWord ++ tailWord_2729709).sum := by decide
  have hdescent : baseEnd_2729709 < baseStart_2729709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729715 : List Nat := [1, 1, 1, 2, 2, 3, 4, 3, 6]
def baseStart_2729715 : Nat := 118140960795 + 2729715 * 2 ^ 59
def prefixEnd_2729715 : Nat := 4983230072969 + 3 ^ 40 * 2729715 * 2
def baseEnd_2729715 : Nat := 155739538309765856800975

theorem tailTrace_2729715 : CollatzResearch.WordTrace tailWord_2729715 prefixEnd_2729715 155739538309765856800975 := by
  unfold tailWord_2729715
  simp only [CollatzResearch.WordTrace]
  refine ⟨99560885305716228051174599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66373923537144152034116399 99560885305716228051174599)
  ·
    refine ⟨149341327958574342076761899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99560885305716228051174599 149341327958574342076761899)
    ·
      refine ⟨224011991937861513115142849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149341327958574342076761899 224011991937861513115142849)
      ·
        refine ⟨168008993953396134836357137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224011991937861513115142849 168008993953396134836357137)
        ·
          refine ⟨126006745465047101127267853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168008993953396134836357137 126006745465047101127267853)
          ·
            refine ⟨47252529549392662922725445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126006745465047101127267853 47252529549392662922725445)
            ·
              refine ⟨8859849290511124298011021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47252529549392662922725445 8859849290511124298011021)
              ·
                refine ⟨3322443483941671611754133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8859849290511124298011021 3322443483941671611754133)
                ·
                  refine ⟨155739538309765856800975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3322443483941671611754133 155739538309765856800975)
                  ·
                    rfl

theorem cell23_2729715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 6].length) (baseStart_2729715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729715 prefixEnd_2729715 := by exact prefixLift 2729715
  have htrace : WordTrace (prefixWord ++ tailWord_2729715) baseStart_2729715 baseEnd_2729715 := by
    simpa [prefixWord, tailWord_2729715, baseEnd_2729715] using wordTrace_append hprefix tailTrace_2729715
  have hstable : (prefixWord ++ tailWord_2729715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729715).length < 2 ^ (prefixWord ++ tailWord_2729715).sum := by decide
  have hdescent : baseEnd_2729715 < baseStart_2729715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729725 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 1, 7, 3]
def baseStart_2729725 : Nat := 118140960795 + 2729725 * 2 ^ 59
def prefixEnd_2729725 : Nat := 4983230072969 + 3 ^ 40 * 2729725 * 2
def baseEnd_2729725 : Nat := 1401660979594437672083729

theorem tailTrace_2729725 : CollatzResearch.WordTrace tailWord_2729725 prefixEnd_2729725 1401660979594437672083729 := by
  unfold tailWord_2729725
  simp only [CollatzResearch.WordTrace]
  refine ⟨99561250035679999759038629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66374166690453333172692419 99561250035679999759038629)
  ·
    refine ⟨18667734381689999954819743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99561250035679999759038629 18667734381689999954819743)
    ·
      refine ⟨28001601572534999932229615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18667734381689999954819743 28001601572534999932229615)
      ·
        refine ⟨42002402358802499898344423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28001601572534999932229615 42002402358802499898344423)
        ·
          refine ⟨63003603538203749847516635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42002402358802499898344423 63003603538203749847516635)
          ·
            refine ⟨94505405307305624771274953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63003603538203749847516635 94505405307305624771274953)
            ·
              refine ⟨70879053980479218578456215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94505405307305624771274953 70879053980479218578456215)
              ·
                refine ⟨106318580970718827867684323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70879053980479218578456215 106318580970718827867684323)
                ·
                  refine ⟨159477871456078241801526485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106318580970718827867684323 159477871456078241801526485)
                  ·
                    refine ⟨3737762612251833792223277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 159477871456078241801526485 3737762612251833792223277)
                    ·
                      refine ⟨1401660979594437672083729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3737762612251833792223277 1401660979594437672083729)
                      ·
                        rfl

theorem cell23_2729725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_2729725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729725 prefixEnd_2729725 := by exact prefixLift 2729725
  have htrace : WordTrace (prefixWord ++ tailWord_2729725) baseStart_2729725 baseEnd_2729725 := by
    simpa [prefixWord, tailWord_2729725, baseEnd_2729725] using wordTrace_append hprefix tailTrace_2729725
  have hstable : (prefixWord ++ tailWord_2729725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729725).length < 2 ^ (prefixWord ++ tailWord_2729725).sum := by decide
  have hdescent : baseEnd_2729725 < baseStart_2729725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729726 : List Nat := [4, 2, 2, 1, 3, 2, 1, 1, 2, 1, 4]
def baseStart_2729726 : Nat := 118140960795 + 2729726 * 2 ^ 59
def prefixEnd_2729726 : Nat := 4983230072969 + 3 ^ 40 * 2729726 * 2
def baseEnd_2729726 : Nat := 1401661493075092168171225

theorem tailTrace_2729726 : CollatzResearch.WordTrace tailWord_2729726 prefixEnd_2729726 1401661493075092168171225 := by
  unfold tailWord_2729726
  simp only [CollatzResearch.WordTrace]
  refine ⟨12445160813584547116228129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66374191005784251286550021 12445160813584547116228129)
  ·
    refine ⟨9333870610188410337171097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12445160813584547116228129 9333870610188410337171097)
    ·
      refine ⟨7000402957641307752878323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9333870610188410337171097 7000402957641307752878323)
      ·
        refine ⟨10500604436461961629317485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7000402957641307752878323 10500604436461961629317485)
        ·
          refine ⟨3937726663673235610994057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10500604436461961629317485 3937726663673235610994057)
          ·
            refine ⟨2953294997754926708245543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3937726663673235610994057 2953294997754926708245543)
            ·
              refine ⟨4429942496632390062368315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2953294997754926708245543 4429942496632390062368315)
              ·
                refine ⟨6644913744948585093552473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4429942496632390062368315 6644913744948585093552473)
                ·
                  refine ⟨4983685308711438820164355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6644913744948585093552473 4983685308711438820164355)
                  ·
                    refine ⟨7475527963067158230246533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4983685308711438820164355 7475527963067158230246533)
                    ·
                      refine ⟨1401661493075092168171225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7475527963067158230246533 1401661493075092168171225)
                      ·
                        rfl

theorem cell23_2729726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_2729726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729726 prefixEnd_2729726 := by exact prefixLift 2729726
  have htrace : WordTrace (prefixWord ++ tailWord_2729726) baseStart_2729726 baseEnd_2729726 := by
    simpa [prefixWord, tailWord_2729726, baseEnd_2729726] using wordTrace_append hprefix tailTrace_2729726
  have hstable : (prefixWord ++ tailWord_2729726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729726).length < 2 ^ (prefixWord ++ tailWord_2729726).sum := by decide
  have hdescent : baseEnd_2729726 < baseStart_2729726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729759 : List Nat := [1, 1, 2, 4, 2, 1, 4, 1, 3, 1, 3]
def baseStart_2729759 : Nat := 118140960795 + 2729759 * 2 ^ 59
def prefixEnd_2729759 : Nat := 4983230072969 + 3 ^ 40 * 2729759 * 2
def baseEnd_2729759 : Nat := 1401678437936690539058573

theorem tailTrace_2729759 : CollatzResearch.WordTrace tailWord_2729759 prefixEnd_2729759 1401678437936690539058573 := by
  unfold tailWord_2729759
  simp only [CollatzResearch.WordTrace]
  refine ⟨99562490117556823565776331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66374993411704549043850887 99562490117556823565776331)
  ·
    refine ⟨149343735176335235348664497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99562490117556823565776331 149343735176335235348664497)
    ·
      refine ⟨112007801382251426511498373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149343735176335235348664497 112007801382251426511498373)
      ·
        refine ⟨21001462759172142470905945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112007801382251426511498373 21001462759172142470905945)
        ·
          refine ⟨15751097069379106853179459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21001462759172142470905945 15751097069379106853179459)
          ·
            refine ⟨23626645604068660279769189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15751097069379106853179459 23626645604068660279769189)
            ·
              refine ⟨4429996050762873802456723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23626645604068660279769189 4429996050762873802456723)
              ·
                refine ⟨6644994076144310703685085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4429996050762873802456723 6644994076144310703685085)
                ·
                  refine ⟨2491872778554116513881907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6644994076144310703685085 2491872778554116513881907)
                  ·
                    refine ⟨3737809167831174770822861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2491872778554116513881907 3737809167831174770822861)
                    ·
                      refine ⟨1401678437936690539058573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3737809167831174770822861 1401678437936690539058573)
                      ·
                        rfl

theorem cell23_2729759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_2729759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729759 prefixEnd_2729759 := by exact prefixLift 2729759
  have htrace : WordTrace (prefixWord ++ tailWord_2729759) baseStart_2729759 baseEnd_2729759 := by
    simpa [prefixWord, tailWord_2729759, baseEnd_2729759] using wordTrace_append hprefix tailTrace_2729759
  have hstable : (prefixWord ++ tailWord_2729759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729759).length < 2 ^ (prefixWord ++ tailWord_2729759).sum := by decide
  have hdescent : baseEnd_2729759 < baseStart_2729759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729779 : List Nat := [1, 1, 1, 2, 7, 1, 2, 2, 1, 5]
def baseStart_2729779 : Nat := 118140960795 + 2729779 * 2 ^ 59
def prefixEnd_2729779 : Nat := 4983230072969 + 3 ^ 40 * 2729779 * 2
def baseEnd_2729779 : Nat := 467229569183260153602827

theorem tailTrace_2729779 : CollatzResearch.WordTrace tailWord_2729779 prefixEnd_2729779 467229569183260153602827 := by
  unfold tailWord_2729779
  simp only [CollatzResearch.WordTrace]
  refine ⟨99563219577484366981504391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66375479718322911321002927 99563219577484366981504391)
  ·
    refine ⟨149344829366226550472256587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99563219577484366981504391 149344829366226550472256587)
    ·
      refine ⟨224017244049339825708384881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149344829366226550472256587 224017244049339825708384881)
      ·
        refine ⟨168012933037004869281288661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224017244049339825708384881 168012933037004869281288661)
        ·
          refine ⟨3937803118054801623780203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 168012933037004869281288661 3937803118054801623780203)
          ·
            refine ⟨5906704677082202435670305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3937803118054801623780203 5906704677082202435670305)
            ·
              refine ⟨4430028507811651826752729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5906704677082202435670305 4430028507811651826752729)
              ·
                refine ⟨3322521380858738870064547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4430028507811651826752729 3322521380858738870064547)
                ·
                  refine ⟨4983782071288108305096821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3322521380858738870064547 4983782071288108305096821)
                  ·
                    refine ⟨467229569183260153602827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4983782071288108305096821 467229569183260153602827)
                    ·
                      rfl

theorem cell23_2729779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 5].length) (baseStart_2729779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729779 prefixEnd_2729779 := by exact prefixLift 2729779
  have htrace : WordTrace (prefixWord ++ tailWord_2729779) baseStart_2729779 baseEnd_2729779 := by
    simpa [prefixWord, tailWord_2729779, baseEnd_2729779] using wordTrace_append hprefix tailTrace_2729779
  have hstable : (prefixWord ++ tailWord_2729779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729779).length < 2 ^ (prefixWord ++ tailWord_2729779).sum := by decide
  have hdescent : baseEnd_2729779 < baseStart_2729779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729799 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 5, 2, 2]
def baseStart_2729799 : Nat := 118140960795 + 2729799 * 2 ^ 59
def prefixEnd_2729799 : Nat := 4983230072969 + 3 ^ 40 * 2729799 * 2
def baseEnd_2729799 : Nat := 1401698977162870382558389

theorem tailTrace_2729799 : CollatzResearch.WordTrace tailWord_2729799 prefixEnd_2729799 1401698977162870382558389 := by
  unfold tailWord_2729799
  simp only [CollatzResearch.WordTrace]
  refine ⟨99563949037411910397232451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66375966024941273598154967 99563949037411910397232451)
  ·
    refine ⟨149345923556117865595848677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99563949037411910397232451 149345923556117865595848677)
    ·
      refine ⟨28002360666772099799221627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149345923556117865595848677 28002360666772099799221627)
      ·
        refine ⟨42003541000158149698832441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28002360666772099799221627 42003541000158149698832441)
        ·
          refine ⟨31502655750118612274124331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42003541000158149698832441 31502655750118612274124331)
          ·
            refine ⟨47253983625177918411186497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31502655750118612274124331 47253983625177918411186497)
            ·
              refine ⟨35440487718883438808389873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47253983625177918411186497 35440487718883438808389873)
              ·
                refine ⟨26580365789162579106292405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35440487718883438808389873 26580365789162579106292405)
                ·
                  refine ⟨2491909292733991791214913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26580365789162579106292405 2491909292733991791214913)
                  ·
                    refine ⟨1868931969550493843411185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2491909292733991791214913 1868931969550493843411185)
                    ·
                      refine ⟨1401698977162870382558389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1868931969550493843411185 1401698977162870382558389)
                      ·
                        rfl

theorem cell23_2729799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5, 2, 2].length) (baseStart_2729799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729799 prefixEnd_2729799 := by exact prefixLift 2729799
  have htrace : WordTrace (prefixWord ++ tailWord_2729799) baseStart_2729799 baseEnd_2729799 := by
    simpa [prefixWord, tailWord_2729799, baseEnd_2729799] using wordTrace_append hprefix tailTrace_2729799
  have hstable : (prefixWord ++ tailWord_2729799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729799).length < 2 ^ (prefixWord ++ tailWord_2729799).sum := by decide
  have hdescent : baseEnd_2729799 < baseStart_2729799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729802 : List Nat := [3, 1, 2, 1, 1, 1, 6, 1, 1, 1, 5]
def baseStart_2729802 : Nat := 118140960795 + 2729802 * 2 ^ 59
def prefixEnd_2729802 : Nat := 4983230072969 + 3 ^ 40 * 2729802 * 2
def baseEnd_2729802 : Nat := 1401700517604833870820875

theorem tailTrace_2729802 : CollatzResearch.WordTrace tailWord_2729802 prefixEnd_2729802 1401700517604833870820875 := by
  unfold tailWord_2729802
  simp only [CollatzResearch.WordTrace]
  refine ⟨24891014614100260477397915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66376038970934027939727773 24891014614100260477397915)
  ·
    refine ⟨37336521921150390716096873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24891014614100260477397915 37336521921150390716096873)
    ·
      refine ⟨28002391440862793037072655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37336521921150390716096873 28002391440862793037072655)
      ·
        refine ⟨42003587161294189555608983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28002391440862793037072655 42003587161294189555608983)
        ·
          refine ⟨63005380741941284333413475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42003587161294189555608983 63005380741941284333413475)
          ·
            refine ⟨94508071112911926500120213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63005380741941284333413475 94508071112911926500120213)
            ·
              refine ⟨4430065833417746554693135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 94508071112911926500120213 4430065833417746554693135)
              ·
                refine ⟨6645098750126619832039703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4430065833417746554693135 6645098750126619832039703)
                ·
                  refine ⟨9967648125189929748059555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6645098750126619832039703 9967648125189929748059555)
                  ·
                    refine ⟨14951472187784894622089333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9967648125189929748059555 14951472187784894622089333)
                    ·
                      refine ⟨1401700517604833870820875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14951472187784894622089333 1401700517604833870820875)
                      ·
                        rfl

theorem cell23_2729802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_2729802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729802 prefixEnd_2729802 := by exact prefixLift 2729802
  have htrace : WordTrace (prefixWord ++ tailWord_2729802) baseStart_2729802 baseEnd_2729802 := by
    simpa [prefixWord, tailWord_2729802, baseEnd_2729802] using wordTrace_append hprefix tailTrace_2729802
  have hstable : (prefixWord ++ tailWord_2729802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729802).length < 2 ^ (prefixWord ++ tailWord_2729802).sum := by decide
  have hdescent : baseEnd_2729802 < baseStart_2729802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729812 : List Nat := [2, 4, 1, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_2729812 : Nat := 118140960795 + 2729812 * 2 ^ 59
def prefixEnd_2729812 : Nat := 4983230072969 + 3 ^ 40 * 2729812 * 2
def baseEnd_2729812 : Nat := 1401705652411378831695829

theorem tailTrace_2729812 : CollatzResearch.WordTrace tailWord_2729812 prefixEnd_2729812 1401705652411378831695829 := by
  unfold tailWord_2729812
  simp only [CollatzResearch.WordTrace]
  refine ⟨49782211593182406808727845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66376282124243209078303793 49782211593182406808727845)
  ·
    refine ⟨9334164673721701276636471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49782211593182406808727845 9334164673721701276636471)
    ·
      refine ⟨14001247010582551914954707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9334164673721701276636471 14001247010582551914954707)
      ·
        refine ⟨21001870515873827872432061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14001247010582551914954707 21001870515873827872432061)
        ·
          refine ⟨7875701443452685452162023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21001870515873827872432061 7875701443452685452162023)
          ·
            refine ⟨11813552165179028178243035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7875701443452685452162023 11813552165179028178243035)
            ·
              refine ⟨17720328247768542267364553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11813552165179028178243035 17720328247768542267364553)
              ·
                refine ⟨13290246185826406700523415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17720328247768542267364553 13290246185826406700523415)
                ·
                  refine ⟨19935369278739610050785123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13290246185826406700523415 19935369278739610050785123)
                  ·
                    refine ⟨29903053918109415076177685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19935369278739610050785123 29903053918109415076177685)
                    ·
                      refine ⟨1401705652411378831695829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29903053918109415076177685 1401705652411378831695829)
                      ·
                        rfl

theorem cell23_2729812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_2729812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729812 prefixEnd_2729812 := by exact prefixLift 2729812
  have htrace : WordTrace (prefixWord ++ tailWord_2729812) baseStart_2729812 baseEnd_2729812 := by
    simpa [prefixWord, tailWord_2729812, baseEnd_2729812] using wordTrace_append hprefix tailTrace_2729812
  have hstable : (prefixWord ++ tailWord_2729812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729812).length < 2 ^ (prefixWord ++ tailWord_2729812).sum := by decide
  have hdescent : baseEnd_2729812 < baseStart_2729812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729825 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 2, 2, 6]
def baseStart_2729825 : Nat := 118140960795 + 2729825 * 2 ^ 59
def prefixEnd_2729825 : Nat := 4983230072969 + 3 ^ 40 * 2729825 * 2
def baseEnd_2729825 : Nat := 1401712327659887280833269

theorem tailTrace_2729825 : CollatzResearch.WordTrace tailWord_2729825 prefixEnd_2729825 1401712327659887280833269 := by
  unfold tailWord_2729825
  simp only [CollatzResearch.WordTrace]
  refine ⟨99564897335317716837678929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66376598223545144558452619 99564897335317716837678929)
  ·
    refine ⟨74673673001488287628259197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99564897335317716837678929 74673673001488287628259197)
    ·
      refine ⟨28002627375558107860597199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74673673001488287628259197 28002627375558107860597199)
      ·
        refine ⟨42003941063337161790895799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28002627375558107860597199 42003941063337161790895799)
        ·
          refine ⟨63005911595005742686343699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42003941063337161790895799 63005911595005742686343699)
          ·
            refine ⟨94508867392508614029515549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63005911595005742686343699 94508867392508614029515549)
            ·
              refine ⟨35440825272190730261068331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94508867392508614029515549 35440825272190730261068331)
              ·
                refine ⟨53161237908286095391602497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35440825272190730261068331 53161237908286095391602497)
                ·
                  refine ⟨39870928431214571543701873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53161237908286095391602497 39870928431214571543701873)
                  ·
                    refine ⟨29903196323410928657776405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39870928431214571543701873 29903196323410928657776405)
                    ·
                      refine ⟨1401712327659887280833269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29903196323410928657776405 1401712327659887280833269)
                      ·
                        rfl

theorem cell23_2729825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_2729825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729825 prefixEnd_2729825 := by exact prefixLift 2729825
  have htrace : WordTrace (prefixWord ++ tailWord_2729825) baseStart_2729825 baseEnd_2729825 := by
    simpa [prefixWord, tailWord_2729825, baseEnd_2729825] using wordTrace_append hprefix tailTrace_2729825
  have hstable : (prefixWord ++ tailWord_2729825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729825).length < 2 ^ (prefixWord ++ tailWord_2729825).sum := by decide
  have hdescent : baseEnd_2729825 < baseStart_2729825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729826 : List Nat := [3, 3, 2, 1, 2, 2, 1, 3, 2, 4]
def baseStart_2729826 : Nat := 118140960795 + 2729826 * 2 ^ 59
def prefixEnd_2729826 : Nat := 4983230072969 + 3 ^ 40 * 2729826 * 2
def baseEnd_2729826 : Nat := 467237613713513925640255

theorem tailTrace_2729826 : CollatzResearch.WordTrace tailWord_2729826 prefixEnd_2729826 467237613713513925640255 := by
  unfold tailWord_2729826
  simp only [CollatzResearch.WordTrace]
  refine ⟨24891233452078523502116333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66376622538876062672310221 24891233452078523502116333)
  ·
    refine ⟨9334212544529446313293625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24891233452078523502116333 9334212544529446313293625)
    ·
      refine ⟨7000659408397084734970219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9334212544529446313293625 7000659408397084734970219)
      ·
        refine ⟨10500989112595627102455329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7000659408397084734970219 10500989112595627102455329)
        ·
          refine ⟨7875741834446720326841497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10500989112595627102455329 7875741834446720326841497)
          ·
            refine ⟨5906806375835040245131123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7875741834446720326841497 5906806375835040245131123)
            ·
              refine ⟨8860209563752560367696685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5906806375835040245131123 8860209563752560367696685)
              ·
                refine ⟨3322578586407210137886257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8860209563752560367696685 3322578586407210137886257)
                ·
                  refine ⟨2491933939805407603414693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3322578586407210137886257 2491933939805407603414693)
                  ·
                    refine ⟨467237613713513925640255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2491933939805407603414693 467237613713513925640255)
                    ·
                      rfl

theorem cell23_2729826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_2729826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729826 prefixEnd_2729826 := by exact prefixLift 2729826
  have htrace : WordTrace (prefixWord ++ tailWord_2729826) baseStart_2729826 baseEnd_2729826 := by
    simpa [prefixWord, tailWord_2729826, baseEnd_2729826] using wordTrace_append hprefix tailTrace_2729826
  have hstable : (prefixWord ++ tailWord_2729826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729826).length < 2 ^ (prefixWord ++ tailWord_2729826).sum := by decide
  have hdescent : baseEnd_2729826 < baseStart_2729826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729836 : List Nat := [2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 3]
def baseStart_2729836 : Nat := 118140960795 + 2729836 * 2 ^ 59
def prefixEnd_2729836 : Nat := 4983230072969 + 3 ^ 40 * 2729836 * 2
def baseEnd_2729836 : Nat := 1401717975947086737795719

theorem tailTrace_2729836 : CollatzResearch.WordTrace tailWord_2729836 prefixEnd_2729836 1401717975947086737795719 := by
  unfold tailWord_2729836
  simp only [CollatzResearch.WordTrace]
  refine ⟨49782649269138932858164681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66376865692185243810886241 49782649269138932858164681)
  ·
    refine ⟨37336986951854199643623511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49782649269138932858164681 37336986951854199643623511)
    ·
      refine ⟨56005480427781299465435267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37336986951854199643623511 56005480427781299465435267)
      ·
        refine ⟨84008220641671949198152901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56005480427781299465435267 84008220641671949198152901)
        ·
          refine ⟨15751541370313490474653669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84008220641671949198152901 15751541370313490474653669)
          ·
            refine ⟨2953414006933779463997563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15751541370313490474653669 2953414006933779463997563)
            ·
              refine ⟨4430121010400669195996345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2953414006933779463997563 4430121010400669195996345)
              ·
                refine ⟨3322590757800501896997259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4430121010400669195996345 3322590757800501896997259)
                ·
                  refine ⟨4983886136700752845495889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3322590757800501896997259 4983886136700752845495889)
                  ·
                    refine ⟨3737914602525564634121917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4983886136700752845495889 3737914602525564634121917)
                    ·
                      refine ⟨1401717975947086737795719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3737914602525564634121917 1401717975947086737795719)
                      ·
                        rfl

theorem cell23_2729836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 3].length) (baseStart_2729836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729836 prefixEnd_2729836 := by exact prefixLift 2729836
  have htrace : WordTrace (prefixWord ++ tailWord_2729836) baseStart_2729836 baseEnd_2729836 := by
    simpa [prefixWord, tailWord_2729836, baseEnd_2729836] using wordTrace_append hprefix tailTrace_2729836
  have hstable : (prefixWord ++ tailWord_2729836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729836).length < 2 ^ (prefixWord ++ tailWord_2729836).sum := by decide
  have hdescent : baseEnd_2729836 < baseStart_2729836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729846 : List Nat := [5, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4]
def baseStart_2729846 : Nat := 118140960795 + 2729846 * 2 ^ 59
def prefixEnd_2729846 : Nat := 4983230072969 + 3 ^ 40 * 2729846 * 2
def baseEnd_2729846 : Nat := 1401723110753631698670673

theorem tailTrace_2729846 : CollatzResearch.WordTrace tailWord_2729846 prefixEnd_2729846 1401723110753631698670673 := by
  unfold tailWord_2729846
  simp only [CollatzResearch.WordTrace]
  refine ⟨6222853954265102339012087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66377108845494424949462261 6222853954265102339012087)
  ·
    refine ⟨9334280931397653508518131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6222853954265102339012087 9334280931397653508518131)
    ·
      refine ⟨14001421397096480262777197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9334280931397653508518131 14001421397096480262777197)
      ·
        refine ⟨5250533023911180098541449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14001421397096480262777197 5250533023911180098541449)
        ·
          refine ⟨3937899767933385073906087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5250533023911180098541449 3937899767933385073906087)
          ·
            refine ⟨5906849651900077610859131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3937899767933385073906087 5906849651900077610859131)
            ·
              refine ⟨8860274477850116416288697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5906849651900077610859131 8860274477850116416288697)
              ·
                refine ⟨6645205858387587312216523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8860274477850116416288697 6645205858387587312216523)
                ·
                  refine ⟨9967808787581380968324785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6645205858387587312216523 9967808787581380968324785)
                  ·
                    refine ⟨7475856590686035726243589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9967808787581380968324785 7475856590686035726243589)
                    ·
                      refine ⟨1401723110753631698670673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7475856590686035726243589 1401723110753631698670673)
                      ·
                        rfl

theorem cell23_2729846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_2729846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729846 prefixEnd_2729846 := by exact prefixLift 2729846
  have htrace : WordTrace (prefixWord ++ tailWord_2729846) baseStart_2729846 baseEnd_2729846 := by
    simpa [prefixWord, tailWord_2729846, baseEnd_2729846] using wordTrace_append hprefix tailTrace_2729846
  have hstable : (prefixWord ++ tailWord_2729846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729846).length < 2 ^ (prefixWord ++ tailWord_2729846).sum := by decide
  have hdescent : baseEnd_2729846 < baseStart_2729846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729876 : List Nat := [2, 4, 2, 1, 1, 2, 1, 2, 3, 3, 2]
def baseStart_2729876 : Nat := 118140960795 + 2729876 * 2 ^ 59
def prefixEnd_2729876 : Nat := 4983230072969 + 3 ^ 40 * 2729876 * 2
def baseEnd_2729876 : Nat := 1401738515173266581295535

theorem tailTrace_2729876 : CollatzResearch.WordTrace tailWord_2729876 prefixEnd_2729876 1401738515173266581295535 := by
  unfold tailWord_2729876
  simp only [CollatzResearch.WordTrace]
  refine ⟨49783378729066476273892741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66377838305421968365190321 49783378729066476273892741)
  ·
    refine ⟨9334383511699964301354889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49783378729066476273892741 9334383511699964301354889)
    ·
      refine ⟨7000787633774973226016167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9334383511699964301354889 7000787633774973226016167)
      ·
        refine ⟨10501181450662459839024251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7000787633774973226016167 10501181450662459839024251)
        ·
          refine ⟨15751772175993689758536377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10501181450662459839024251 15751772175993689758536377)
          ·
            refine ⟨11813829131995267318902283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15751772175993689758536377 11813829131995267318902283)
            ·
              refine ⟨17720743697992900978353425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11813829131995267318902283 17720743697992900978353425)
              ·
                refine ⟨13290557773494675733765069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17720743697992900978353425 13290557773494675733765069)
                ·
                  refine ⟨4983959165060503400161901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13290557773494675733765069 4983959165060503400161901)
                  ·
                    refine ⟨1868984686897688775060713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4983959165060503400161901 1868984686897688775060713)
                    ·
                      refine ⟨1401738515173266581295535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1868984686897688775060713 1401738515173266581295535)
                      ·
                        rfl

theorem cell23_2729876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_2729876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729876 prefixEnd_2729876 := by exact prefixLift 2729876
  have htrace : WordTrace (prefixWord ++ tailWord_2729876) baseStart_2729876 baseEnd_2729876 := by
    simpa [prefixWord, tailWord_2729876, baseEnd_2729876] using wordTrace_append hprefix tailTrace_2729876
  have hstable : (prefixWord ++ tailWord_2729876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729876).length < 2 ^ (prefixWord ++ tailWord_2729876).sum := by decide
  have hdescent : baseEnd_2729876 < baseStart_2729876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729882 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 1, 8]
def baseStart_2729882 : Nat := 118140960795 + 2729882 * 2 ^ 59
def prefixEnd_2729882 : Nat := 4983230072969 + 3 ^ 40 * 2729882 * 2
def baseEnd_2729882 : Nat := 467247198685731185940169

theorem tailTrace_2729882 : CollatzResearch.WordTrace tailWord_2729882 prefixEnd_2729882 467247198685731185940169 := by
  unfold tailWord_2729882
  simp only [CollatzResearch.WordTrace]
  refine ⟨24891744074027803893125975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66377984197407477048335933 24891744074027803893125975)
  ·
    refine ⟨37337616111041705839688963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24891744074027803893125975 37337616111041705839688963)
    ·
      refine ⟨56006424166562558759533445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37337616111041705839688963 56006424166562558759533445)
      ·
        refine ⟨10501204531230479767412521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56006424166562558759533445 10501204531230479767412521)
        ·
          refine ⟨7875903398422859825559391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10501204531230479767412521 7875903398422859825559391)
          ·
            refine ⟨11813855097634289738339087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7875903398422859825559391 11813855097634289738339087)
            ·
              refine ⟨17720782646451434607508631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11813855097634289738339087 17720782646451434607508631)
              ·
                refine ⟨26581173969677151911262947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17720782646451434607508631 26581173969677151911262947)
                ·
                  refine ⟨39871760954515727866894421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26581173969677151911262947 39871760954515727866894421)
                  ·
                    refine ⟨467247198685731185940169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39871760954515727866894421 467247198685731185940169)
                    ·
                      rfl

theorem cell23_2729882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 1, 8].length) (baseStart_2729882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729882 prefixEnd_2729882 := by exact prefixLift 2729882
  have htrace : WordTrace (prefixWord ++ tailWord_2729882) baseStart_2729882 baseEnd_2729882 := by
    simpa [prefixWord, tailWord_2729882, baseEnd_2729882] using wordTrace_append hprefix tailTrace_2729882
  have hstable : (prefixWord ++ tailWord_2729882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729882).length < 2 ^ (prefixWord ++ tailWord_2729882).sum := by decide
  have hdescent : baseEnd_2729882 < baseStart_2729882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729940 : List Nat := [2, 4, 1, 2, 1, 1, 5, 1, 2, 2, 2]
def baseStart_2729940 : Nat := 118140960795 + 2729940 * 2 ^ 59
def prefixEnd_2729940 : Nat := 4983230072969 + 3 ^ 40 * 2729940 * 2
def baseEnd_2729940 : Nat := 1401771377935154330895241

theorem tailTrace_2729940 : CollatzResearch.WordTrace tailWord_2729940 prefixEnd_2729940 1401771377935154330895241 := by
  unfold tailWord_2729940
  simp only [CollatzResearch.WordTrace]
  refine ⟨49784545864950545739057637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66379394486600727652076849 49784545864950545739057637)
  ·
    refine ⟨9334602349678227326073307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49784545864950545739057637 9334602349678227326073307)
    ·
      refine ⟨14001903524517340989109961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9334602349678227326073307 14001903524517340989109961)
      ·
        refine ⟨10501427643388005741832471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14001903524517340989109961 10501427643388005741832471)
        ·
          refine ⟨15752141465082008612748707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10501427643388005741832471 15752141465082008612748707)
          ·
            refine ⟨23628212197623012919123061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15752141465082008612748707 23628212197623012919123061)
            ·
              refine ⟨2215144893527157461167787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23628212197623012919123061 2215144893527157461167787)
              ·
                refine ⟨3322717340290736191751681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2215144893527157461167787 3322717340290736191751681)
                ·
                  refine ⟨2492038005218052143813761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3322717340290736191751681 2492038005218052143813761)
                  ·
                    refine ⟨1869028503913539107860321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2492038005218052143813761 1869028503913539107860321)
                    ·
                      refine ⟨1401771377935154330895241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1869028503913539107860321 1401771377935154330895241)
                      ·
                        rfl

theorem cell23_2729940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_2729940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729940 prefixEnd_2729940 := by exact prefixLift 2729940
  have htrace : WordTrace (prefixWord ++ tailWord_2729940) baseStart_2729940 baseEnd_2729940 := by
    simpa [prefixWord, tailWord_2729940, baseEnd_2729940] using wordTrace_append hprefix tailTrace_2729940
  have hstable : (prefixWord ++ tailWord_2729940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729940).length < 2 ^ (prefixWord ++ tailWord_2729940).sum := by decide
  have hdescent : baseEnd_2729940 < baseStart_2729940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729979 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 4, 4, 2]
def baseStart_2729979 : Nat := 118140960795 + 2729979 * 2 ^ 59
def prefixEnd_2729979 : Nat := 4983230072969 + 3 ^ 40 * 2729979 * 2
def baseEnd_2729979 : Nat := 1401791403680679678307561

theorem tailTrace_2729979 : CollatzResearch.WordTrace tailWord_2729979 prefixEnd_2729979 1401791403680679678307561 := by
  unfold tailWord_2729979
  simp only [CollatzResearch.WordTrace]
  refine ⟨99570514176759801138784991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66380342784506534092523327 99570514176759801138784991)
  ·
    refine ⟨149355771265139701708177487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99570514176759801138784991 149355771265139701708177487)
    ·
      refine ⟨224033656897709552562266231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149355771265139701708177487 224033656897709552562266231)
      ·
        refine ⟨336050485346564328843399347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224033656897709552562266231 336050485346564328843399347)
        ·
          refine ⟨504075728019846493265099021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336050485346564328843399347 504075728019846493265099021)
          ·
            refine ⟨189028398007442434974412133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 504075728019846493265099021 189028398007442434974412133)
            ·
              refine ⟨35442824626395456557702275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 189028398007442434974412133 35442824626395456557702275)
              ·
                refine ⟨53164236939593184836553413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35442824626395456557702275 53164236939593184836553413)
                ·
                  refine ⟨9968294426173722156853765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53164236939593184836553413 9968294426173722156853765)
                  ·
                    refine ⟨1869055204907572904410081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9968294426173722156853765 1869055204907572904410081)
                    ·
                      refine ⟨1401791403680679678307561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1869055204907572904410081 1401791403680679678307561)
                      ·
                        rfl

theorem cell23_2729979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 4, 2].length) (baseStart_2729979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2729979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2729979 prefixEnd_2729979 := by exact prefixLift 2729979
  have htrace : WordTrace (prefixWord ++ tailWord_2729979) baseStart_2729979 baseEnd_2729979 := by
    simpa [prefixWord, tailWord_2729979, baseEnd_2729979] using wordTrace_append hprefix tailTrace_2729979
  have hstable : (prefixWord ++ tailWord_2729979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729979).length < 2 ^ (prefixWord ++ tailWord_2729979).sum := by decide
  have hdescent : baseEnd_2729979 < baseStart_2729979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730080 : List Nat := [2, 1, 1, 3, 2, 4, 2, 3, 1, 1, 3]
def baseStart_2730080 : Nat := 118140960795 + 2730080 * 2 ^ 59
def prefixEnd_2730080 : Nat := 4983230072969 + 3 ^ 40 * 2730080 * 2
def baseEnd_2730080 : Nat := 1401843265226783783144597

theorem tailTrace_2730080 : CollatzResearch.WordTrace tailWord_2730080 prefixEnd_2730080 1401843265226783783144597 := by
  unfold tailWord_2730080
  simp only [CollatzResearch.WordTrace]
  refine ⟨49787098974696947694105847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66382798632929263592141129 49787098974696947694105847)
  ·
    refine ⟨74680648462045421541158771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49787098974696947694105847 74680648462045421541158771)
    ·
      refine ⟨112020972693068132311738157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74680648462045421541158771 112020972693068132311738157)
      ·
        refine ⟨42007864759900549616901809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112020972693068132311738157 42007864759900549616901809)
        ·
          refine ⟨31505898569925412212676357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42007864759900549616901809 31505898569925412212676357)
          ·
            refine ⟨5907355981861014789876817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31505898569925412212676357 5907355981861014789876817)
            ·
              refine ⟨4430516986395761092407613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5907355981861014789876817 4430516986395761092407613)
              ·
                refine ⟨1661443869898410409652855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4430516986395761092407613 1661443869898410409652855)
                ·
                  refine ⟨2492165804847615614479283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1661443869898410409652855 2492165804847615614479283)
                  ·
                    refine ⟨3738248707271423421718925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2492165804847615614479283 3738248707271423421718925)
                    ·
                      refine ⟨1401843265226783783144597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3738248707271423421718925 1401843265226783783144597)
                      ·
                        rfl

theorem cell23_2730080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3, 1, 1, 3].length) (baseStart_2730080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730080 prefixEnd_2730080 := by exact prefixLift 2730080
  have htrace : WordTrace (prefixWord ++ tailWord_2730080) baseStart_2730080 baseEnd_2730080 := by
    simpa [prefixWord, tailWord_2730080, baseEnd_2730080] using wordTrace_append hprefix tailTrace_2730080
  have hstable : (prefixWord ++ tailWord_2730080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730080).length < 2 ^ (prefixWord ++ tailWord_2730080).sum := by decide
  have hdescent : baseEnd_2730080 < baseStart_2730080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730089 : List Nat := [1, 2, 1, 1, 1, 5, 2, 3, 1, 1, 5]
def baseStart_2730089 : Nat := 118140960795 + 2730089 * 2 ^ 59
def prefixEnd_2730089 : Nat := 4983230072969 + 3 ^ 40 * 2730089 * 2
def baseEnd_2730089 : Nat := 1401847886552674247932055

theorem tailTrace_2730089 : CollatzResearch.WordTrace tailWord_2730089 prefixEnd_2730089 1401847886552674247932055 := by
  unfold tailWord_2730089
  simp only [CollatzResearch.WordTrace]
  refine ⟨99574526206361289925289321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66383017470907526616859547 99574526206361289925289321)
  ·
    refine ⟨74680894654770967443966991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99574526206361289925289321 74680894654770967443966991)
    ·
      refine ⟨112021341982156451165950487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74680894654770967443966991 112021341982156451165950487)
      ·
        refine ⟨168032012973234676748925731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112021341982156451165950487 168032012973234676748925731)
        ·
          refine ⟨252048019459852015123388597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168032012973234676748925731 252048019459852015123388597)
          ·
            refine ⟨23629501824361126417817681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 252048019459852015123388597 23629501824361126417817681)
            ·
              refine ⟨17722126368270844813363261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23629501824361126417817681 17722126368270844813363261)
              ·
                refine ⟨6645797388101566805011223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17722126368270844813363261 6645797388101566805011223)
                ·
                  refine ⟨9968696082152350207516835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6645797388101566805011223 9968696082152350207516835)
                  ·
                    refine ⟨14953044123228525311275253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9968696082152350207516835 14953044123228525311275253)
                    ·
                      refine ⟨1401847886552674247932055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14953044123228525311275253 1401847886552674247932055)
                      ·
                        rfl

theorem cell23_2730089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 1, 5].length) (baseStart_2730089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730089 prefixEnd_2730089 := by exact prefixLift 2730089
  have htrace : WordTrace (prefixWord ++ tailWord_2730089) baseStart_2730089 baseEnd_2730089 := by
    simpa [prefixWord, tailWord_2730089, baseEnd_2730089] using wordTrace_append hprefix tailTrace_2730089
  have hstable : (prefixWord ++ tailWord_2730089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730089).length < 2 ^ (prefixWord ++ tailWord_2730089).sum := by decide
  have hdescent : baseEnd_2730089 < baseStart_2730089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730096 : List Nat := [2, 1, 1, 1, 5, 3, 1, 1, 4, 4]
def baseStart_2730096 : Nat := 118140960795 + 2730096 * 2 ^ 59
def prefixEnd_2730096 : Nat := 4983230072969 + 3 ^ 40 * 2730096 * 2
def baseEnd_2730096 : Nat := 467283826972418573514841

theorem tailTrace_2730096 : CollatzResearch.WordTrace tailWord_2730096 prefixEnd_2730096 467283826972418573514841 := by
  unfold tailWord_2730096
  simp only [CollatzResearch.WordTrace]
  refine ⟨49787390758667965060397071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66383187678223953413862761 49787390758667965060397071)
  ·
    refine ⟨74681086138001947590595607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49787390758667965060397071 74681086138001947590595607)
    ·
      refine ⟨112021629207002921385893411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74681086138001947590595607 112021629207002921385893411)
      ·
        refine ⟨168032443810504382078840117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112021629207002921385893411 168032443810504382078840117)
        ·
          refine ⟨15753041607234785819891261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 168032443810504382078840117 15753041607234785819891261)
          ·
            refine ⟨5907390602713044682459223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15753041607234785819891261 5907390602713044682459223)
            ·
              refine ⟨8861085904069567023688835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5907390602713044682459223 8861085904069567023688835)
              ·
                refine ⟨13291628856104350535533253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8861085904069567023688835 13291628856104350535533253)
                ·
                  refine ⟨2492180410519565725412485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13291628856104350535533253 2492180410519565725412485)
                  ·
                    refine ⟨467283826972418573514841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2492180410519565725412485 467283826972418573514841)
                    ·
                      rfl

theorem cell23_2730096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 4, 4].length) (baseStart_2730096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730096 prefixEnd_2730096 := by exact prefixLift 2730096
  have htrace : WordTrace (prefixWord ++ tailWord_2730096) baseStart_2730096 baseEnd_2730096 := by
    simpa [prefixWord, tailWord_2730096, baseEnd_2730096] using wordTrace_append hprefix tailTrace_2730096
  have hstable : (prefixWord ++ tailWord_2730096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730096).length < 2 ^ (prefixWord ++ tailWord_2730096).sum := by decide
  have hdescent : baseEnd_2730096 < baseStart_2730096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730103 : List Nat := [1, 1, 3, 1, 1, 5, 1, 3, 3, 2, 2]
def baseStart_2730103 : Nat := 118140960795 + 2730103 * 2 ^ 59
def prefixEnd_2730103 : Nat := 4983230072969 + 3 ^ 40 * 2730103 * 2
def baseEnd_2730103 : Nat := 1401855075281837193156991

theorem tailTrace_2730103 : CollatzResearch.WordTrace tailWord_2730103 prefixEnd_2730103 1401855075281837193156991 := by
  unfold tailWord_2730103
  simp only [CollatzResearch.WordTrace]
  refine ⟨99575036828310570316298963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66383357885540380210865975 99575036828310570316298963)
  ·
    refine ⟨149362555242465855474448445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99575036828310570316298963 149362555242465855474448445)
    ·
      refine ⟨56010958215924695802918167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149362555242465855474448445 56010958215924695802918167)
      ·
        refine ⟨84016437323887043704377251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56010958215924695802918167 84016437323887043704377251)
        ·
          refine ⟨126024655985830565556565877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84016437323887043704377251 126024655985830565556565877)
          ·
            refine ⟨11814811498671615520928051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126024655985830565556565877 11814811498671615520928051)
            ·
              refine ⟨17722217248007423281392077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11814811498671615520928051 17722217248007423281392077)
              ·
                refine ⟨6645831468002783730522029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17722217248007423281392077 6645831468002783730522029)
                ·
                  refine ⟨2492186800501043898945761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6645831468002783730522029 2492186800501043898945761)
                  ·
                    refine ⟨1869140100375782924209321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2492186800501043898945761 1869140100375782924209321)
                    ·
                      refine ⟨1401855075281837193156991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1869140100375782924209321 1401855075281837193156991)
                      ·
                        rfl

theorem cell23_2730103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3, 2, 2].length) (baseStart_2730103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730103 prefixEnd_2730103 := by exact prefixLift 2730103
  have htrace : WordTrace (prefixWord ++ tailWord_2730103) baseStart_2730103 baseEnd_2730103 := by
    simpa [prefixWord, tailWord_2730103, baseEnd_2730103] using wordTrace_append hprefix tailTrace_2730103
  have hstable : (prefixWord ++ tailWord_2730103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730103).length < 2 ^ (prefixWord ++ tailWord_2730103).sum := by decide
  have hdescent : baseEnd_2730103 < baseStart_2730103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730113 : List Nat := [1, 2, 4, 2, 3, 2, 1, 1, 1, 6]
def baseStart_2730113 : Nat := 118140960795 + 2730113 * 2 ^ 59
def prefixEnd_2730113 : Nat := 4983230072969 + 3 ^ 40 * 2730113 * 2
def baseEnd_2730113 : Nat := 467286736696127384677315

theorem tailTrace_2730113 : CollatzResearch.WordTrace tailWord_2730113 prefixEnd_2730113 467286736696127384677315 := by
  unfold tailWord_2730113
  simp only [CollatzResearch.WordTrace]
  refine ⟨99575401558274342024162993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66383601038849561349441995 99575401558274342024162993)
  ·
    refine ⟨74681551168705756518122245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99575401558274342024162993 74681551168705756518122245)
    ·
      refine ⟨14002790844132329347147921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74681551168705756518122245 14002790844132329347147921)
      ·
        refine ⟨10502093133099247010360941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14002790844132329347147921 10502093133099247010360941)
        ·
          refine ⟨3938284924912217628885353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10502093133099247010360941 3938284924912217628885353)
          ·
            refine ⟨2953713693684163221664015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3938284924912217628885353 2953713693684163221664015)
            ·
              refine ⟨4430570540526244832496023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2953713693684163221664015 4430570540526244832496023)
              ·
                refine ⟨6645855810789367248744035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4430570540526244832496023 6645855810789367248744035)
                ·
                  refine ⟨9968783716184050873116053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6645855810789367248744035 9968783716184050873116053)
                  ·
                    refine ⟨467286736696127384677315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9968783716184050873116053 467286736696127384677315)
                    ·
                      rfl

theorem cell23_2730113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_2730113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730113 prefixEnd_2730113 := by exact prefixLift 2730113
  have htrace : WordTrace (prefixWord ++ tailWord_2730113) baseStart_2730113 baseEnd_2730113 := by
    simpa [prefixWord, tailWord_2730113, baseEnd_2730113] using wordTrace_append hprefix tailTrace_2730113
  have hstable : (prefixWord ++ tailWord_2730113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730113).length < 2 ^ (prefixWord ++ tailWord_2730113).sum := by decide
  have hdescent : baseEnd_2730113 < baseStart_2730113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730120 : List Nat := [2, 1, 3, 4, 1, 1, 2, 2, 3, 2, 2]
def baseStart_2730120 : Nat := 118140960795 + 2730120 * 2 ^ 59
def prefixEnd_2730120 : Nat := 4983230072969 + 3 ^ 40 * 2730120 * 2
def baseEnd_2730120 : Nat := 1401863804452963626644413

theorem tailTrace_2730120 : CollatzResearch.WordTrace tailWord_2730120 prefixEnd_2730120 1401863804452963626644413 := by
  unfold tailWord_2730120
  simp only [CollatzResearch.WordTrace]
  refine ⟨49787828434624491109833907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66383771246165988146445209 49787828434624491109833907)
  ·
    refine ⟨74681742651936736664750861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49787828434624491109833907 74681742651936736664750861)
    ·
      refine ⟨28005653494476276249281573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74681742651936736664750861 28005653494476276249281573)
      ·
        refine ⟨5251060030214301796740295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28005653494476276249281573 5251060030214301796740295)
        ·
          refine ⟨7876590045321452695110443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5251060030214301796740295 7876590045321452695110443)
          ·
            refine ⟨11814885067982179042665665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7876590045321452695110443 11814885067982179042665665)
            ·
              refine ⟨8861163800986634281999249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11814885067982179042665665 8861163800986634281999249)
              ·
                refine ⟨6645872850739975711499437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8861163800986634281999249 6645872850739975711499437)
                ·
                  refine ⟨2492202319027490891812289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6645872850739975711499437 2492202319027490891812289)
                  ·
                    refine ⟨1869151739270618168859217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2492202319027490891812289 1869151739270618168859217)
                    ·
                      refine ⟨1401863804452963626644413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1869151739270618168859217 1401863804452963626644413)
                      ·
                        rfl

theorem cell23_2730120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_2730120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730120 prefixEnd_2730120 := by exact prefixLift 2730120
  have htrace : WordTrace (prefixWord ++ tailWord_2730120) baseStart_2730120 baseEnd_2730120 := by
    simpa [prefixWord, tailWord_2730120, baseEnd_2730120] using wordTrace_append hprefix tailTrace_2730120
  have hstable : (prefixWord ++ tailWord_2730120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730120).length < 2 ^ (prefixWord ++ tailWord_2730120).sum := by decide
  have hdescent : baseEnd_2730120 < baseStart_2730120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730126 : List Nat := [4, 1, 1, 3, 3, 1, 1, 9]
def baseStart_2730126 : Nat := 118140960795 + 2730126 * 2 ^ 59
def prefixEnd_2730126 : Nat := 4983230072969 + 3 ^ 40 * 2730126 * 2
def baseEnd_2730126 : Nat := 51920995753218170487755

theorem tailTrace_2730126 : CollatzResearch.WordTrace tailWord_2730126 prefixEnd_2730126 51920995753218170487755 := by
  unfold tailWord_2730126
  simp only [CollatzResearch.WordTrace]
  refine ⟨12446984463403405655548279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66383917138151496829590821 12446984463403405655548279)
  ·
    refine ⟨18670476695105108483322419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12446984463403405655548279 18670476695105108483322419)
    ·
      refine ⟨28005715042657662724983629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18670476695105108483322419 28005715042657662724983629)
      ·
        refine ⟨10502143140996623521868861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28005715042657662724983629 10502143140996623521868861)
        ·
          refine ⟨3938303677873733820700823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10502143140996623521868861 3938303677873733820700823)
          ·
            refine ⟨5907455516810600731051235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3938303677873733820700823 5907455516810600731051235)
            ·
              refine ⟨8861183275215901096576853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5907455516810600731051235 8861183275215901096576853)
              ·
                refine ⟨51920995753218170487755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8861183275215901096576853 51920995753218170487755)
                ·
                  rfl

theorem cell23_2730126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 9].length) (baseStart_2730126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730126 prefixEnd_2730126 := by exact prefixLift 2730126
  have htrace : WordTrace (prefixWord ++ tailWord_2730126) baseStart_2730126 baseEnd_2730126 := by
    simpa [prefixWord, tailWord_2730126, baseEnd_2730126] using wordTrace_append hprefix tailTrace_2730126
  have hstable : (prefixWord ++ tailWord_2730126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730126).length < 2 ^ (prefixWord ++ tailWord_2730126).sum := by decide
  have hdescent : baseEnd_2730126 < baseStart_2730126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730149 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 2, 2, 5]
def baseStart_2730149 : Nat := 118140960795 + 2730149 * 2 ^ 59
def prefixEnd_2730149 : Nat := 4983230072969 + 3 ^ 40 * 2730149 * 2
def baseEnd_2730149 : Nat := 1401878695391944013181779

theorem tailTrace_2730149 : CollatzResearch.WordTrace tailWord_2730149 prefixEnd_2730149 1401878695391944013181779 := by
  unfold tailWord_2730149
  simp only [CollatzResearch.WordTrace]
  refine ⟨99576714586143920172473501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66384476390762613448315667 99576714586143920172473501)
  ·
    refine ⟨37341267969803970064677563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99576714586143920172473501 37341267969803970064677563)
    ·
      refine ⟨56011901954705955097016345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37341267969803970064677563 56011901954705955097016345)
      ·
        refine ⟨42008926466029466322762259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56011901954705955097016345 42008926466029466322762259)
        ·
          refine ⟨63013389699044199484143389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42008926466029466322762259 63013389699044199484143389)
          ·
            refine ⟨23630021137141574806553771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63013389699044199484143389 23630021137141574806553771)
            ·
              refine ⟨35445031705712362209830657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23630021137141574806553771 35445031705712362209830657)
              ·
                refine ⟨26583773779284271657372993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35445031705712362209830657 26583773779284271657372993)
                ·
                  refine ⟨19937830334463203743029745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26583773779284271657372993 19937830334463203743029745)
                  ·
                    refine ⟨14953372750847402807272309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19937830334463203743029745 14953372750847402807272309)
                    ·
                      refine ⟨1401878695391944013181779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14953372750847402807272309 1401878695391944013181779)
                      ·
                        rfl

theorem cell23_2730149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_2730149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730149 prefixEnd_2730149 := by exact prefixLift 2730149
  have htrace : WordTrace (prefixWord ++ tailWord_2730149) baseStart_2730149 baseEnd_2730149 := by
    simpa [prefixWord, tailWord_2730149, baseEnd_2730149] using wordTrace_append hprefix tailTrace_2730149
  have hstable : (prefixWord ++ tailWord_2730149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730149).length < 2 ^ (prefixWord ++ tailWord_2730149).sum := by decide
  have hdescent : baseEnd_2730149 < baseStart_2730149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730154 : List Nat := [3, 1, 5, 1, 2, 2, 1, 1, 3, 2, 2]
def baseStart_2730154 : Nat := 118140960795 + 2730154 * 2 ^ 59
def prefixEnd_2730154 : Nat := 4983230072969 + 3 ^ 40 * 2730154 * 2
def baseEnd_2730154 : Nat := 1401881262795216493619257

theorem tailTrace_2730154 : CollatzResearch.WordTrace tailWord_2730154 prefixEnd_2730154 1401881262795216493619257 := by
  unfold tailWord_2730154
  simp only [CollatzResearch.WordTrace]
  refine ⟨24894224237781451506601379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66384597967417204017603677 24894224237781451506601379)
  ·
    refine ⟨37341336356672177259902069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24894224237781451506601379 37341336356672177259902069)
    ·
      refine ⟨3500750283438016618115819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37341336356672177259902069 3500750283438016618115819)
      ·
        refine ⟨5251125425157024927173729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3500750283438016618115819 5251125425157024927173729)
        ·
          refine ⟨3938344068867768695380297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5251125425157024927173729 3938344068867768695380297)
          ·
            refine ⟨2953758051650826521535223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3938344068867768695380297 2953758051650826521535223)
            ·
              refine ⟨4430637077476239782302835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2953758051650826521535223 4430637077476239782302835)
              ·
                refine ⟨6645955616214359673454253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4430637077476239782302835 6645955616214359673454253)
                ·
                  refine ⟨2492233356080384877545345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6645955616214359673454253 2492233356080384877545345)
                  ·
                    refine ⟨1869175017060288658159009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2492233356080384877545345 1869175017060288658159009)
                    ·
                      refine ⟨1401881262795216493619257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1869175017060288658159009 1401881262795216493619257)
                      ·
                        rfl

theorem cell23_2730154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_2730154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730154 prefixEnd_2730154 := by exact prefixLift 2730154
  have htrace : WordTrace (prefixWord ++ tailWord_2730154) baseStart_2730154 baseEnd_2730154 := by
    simpa [prefixWord, tailWord_2730154, baseEnd_2730154] using wordTrace_append hprefix tailTrace_2730154
  have hstable : (prefixWord ++ tailWord_2730154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730154).length < 2 ^ (prefixWord ++ tailWord_2730154).sum := by decide
  have hdescent : baseEnd_2730154 < baseStart_2730154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730159 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 4]
def baseStart_2730159 : Nat := 118140960795 + 2730159 * 2 ^ 59
def prefixEnd_2730159 : Nat := 4983230072969 + 3 ^ 40 * 2730159 * 2
def baseEnd_2730159 : Nat := 1401883830198488974056733

theorem tailTrace_2730159 : CollatzResearch.WordTrace tailWord_2730159 prefixEnd_2730159 1401883830198488974056733 := by
  unfold tailWord_2730159
  simp only [CollatzResearch.WordTrace]
  refine ⟨99577079316107691880337531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66384719544071794586891687 99577079316107691880337531)
  ·
    refine ⟨149365618974161537820506297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99577079316107691880337531 149365618974161537820506297)
    ·
      refine ⟨112024214230621153365379723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149365618974161537820506297 112024214230621153365379723)
      ·
        refine ⟨168036321345931730048069585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112024214230621153365379723 168036321345931730048069585)
        ·
          refine ⟨126027241009448797536052189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168036321345931730048069585 126027241009448797536052189)
          ·
            refine ⟨47260215378543299076019571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126027241009448797536052189 47260215378543299076019571)
            ·
              refine ⟨70890323067814948614029357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47260215378543299076019571 70890323067814948614029357)
              ·
                refine ⟨26583871150430605730261009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70890323067814948614029357 26583871150430605730261009)
                ·
                  refine ⟨19937903362822954297695757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26583871150430605730261009 19937903362822954297695757)
                  ·
                    refine ⟨7476713761058607861635909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19937903362822954297695757 7476713761058607861635909)
                    ·
                      refine ⟨1401883830198488974056733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7476713761058607861635909 1401883830198488974056733)
                      ·
                        rfl

theorem cell23_2730159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 4].length) (baseStart_2730159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730159 prefixEnd_2730159 := by exact prefixLift 2730159
  have htrace : WordTrace (prefixWord ++ tailWord_2730159) baseStart_2730159 baseEnd_2730159 := by
    simpa [prefixWord, tailWord_2730159, baseEnd_2730159] using wordTrace_append hprefix tailTrace_2730159
  have hstable : (prefixWord ++ tailWord_2730159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730159).length < 2 ^ (prefixWord ++ tailWord_2730159).sum := by decide
  have hdescent : baseEnd_2730159 < baseStart_2730159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730164 : List Nat := [2, 5, 3, 1, 1, 1, 1, 3, 2, 4]
def baseStart_2730164 : Nat := 118140960795 + 2730164 * 2 ^ 59
def prefixEnd_2730164 : Nat := 4983230072969 + 3 ^ 40 * 2730164 * 2
def baseEnd_2730164 : Nat := 467295465867253818164737

theorem tailTrace_2730164 : CollatzResearch.WordTrace tailWord_2730164 prefixEnd_2730164 467295465867253818164737 := by
  unfold tailWord_2730164
  simp only [CollatzResearch.WordTrace]
  refine ⟨49788630840544788867134773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66384841120726385156179697 49788630840544788867134773)
  ·
    refine ⟨4667684141301073956293885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49788630840544788867134773 4667684141301073956293885)
    ·
      refine ⟨1750381552987902733610207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4667684141301073956293885 1750381552987902733610207)
      ·
        refine ⟨2625572329481854100415311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1750381552987902733610207 2625572329481854100415311)
        ·
          refine ⟨3938358494222781150622967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2625572329481854100415311 3938358494222781150622967)
          ·
            refine ⟨5907537741334171725934451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3938358494222781150622967 5907537741334171725934451)
            ·
              refine ⟨8861306612001257588901677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5907537741334171725934451 8861306612001257588901677)
              ·
                refine ⟨3322989979500471595838129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8861306612001257588901677 3322989979500471595838129)
                ·
                  refine ⟨2492242484625353696878597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3322989979500471595838129 2492242484625353696878597)
                  ·
                    refine ⟨467295465867253818164737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2492242484625353696878597 467295465867253818164737)
                    ·
                      rfl

theorem cell23_2730164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_2730164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730164 prefixEnd_2730164 := by exact prefixLift 2730164
  have htrace : WordTrace (prefixWord ++ tailWord_2730164) baseStart_2730164 baseEnd_2730164 := by
    simpa [prefixWord, tailWord_2730164, baseEnd_2730164] using wordTrace_append hprefix tailTrace_2730164
  have hstable : (prefixWord ++ tailWord_2730164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730164).length < 2 ^ (prefixWord ++ tailWord_2730164).sum := by decide
  have hdescent : baseEnd_2730164 < baseStart_2730164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730169 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 1, 8]
def baseStart_2730169 : Nat := 118140960795 + 2730169 * 2 ^ 59
def prefixEnd_2730169 : Nat := 4983230072969 + 3 ^ 40 * 2730169 * 2
def baseEnd_2730169 : Nat := 467296321668344644977229

theorem tailTrace_2730169 : CollatzResearch.WordTrace tailWord_2730169 prefixEnd_2730169 467296321668344644977229 := by
  unfold tailWord_2730169
  simp only [CollatzResearch.WordTrace]
  refine ⟨99577444046071463588201561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66384962697380975725467707 99577444046071463588201561)
  ·
    refine ⟨74683083034553597691151171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99577444046071463588201561 74683083034553597691151171)
    ·
      refine ⟨112024624551830396536726757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74683083034553597691151171 112024624551830396536726757)
      ·
        refine ⟨21004617103468199350636267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112024624551830396536726757 21004617103468199350636267)
        ·
          refine ⟨31506925655202299025954401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21004617103468199350636267 31506925655202299025954401)
          ·
            refine ⟨23630194241401724269465801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31506925655202299025954401 23630194241401724269465801)
            ·
              refine ⟨17722645681051293202099351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23630194241401724269465801 17722645681051293202099351)
              ·
                refine ⟨26583968521576939803149027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17722645681051293202099351 26583968521576939803149027)
                ·
                  refine ⟨39875952782365409704723541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26583968521576939803149027 39875952782365409704723541)
                  ·
                    refine ⟨467296321668344644977229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39875952782365409704723541 467296321668344644977229)
                    ·
                      rfl

theorem cell23_2730169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 8].length) (baseStart_2730169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730169 prefixEnd_2730169 := by exact prefixLift 2730169
  have htrace : WordTrace (prefixWord ++ tailWord_2730169) baseStart_2730169 baseEnd_2730169 := by
    simpa [prefixWord, tailWord_2730169, baseEnd_2730169] using wordTrace_append hprefix tailTrace_2730169
  have hstable : (prefixWord ++ tailWord_2730169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730169).length < 2 ^ (prefixWord ++ tailWord_2730169).sum := by decide
  have hdescent : baseEnd_2730169 < baseStart_2730169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730170 : List Nat := [3, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3]
def baseStart_2730170 : Nat := 118140960795 + 2730170 * 2 ^ 59
def prefixEnd_2730170 : Nat := 4983230072969 + 3 ^ 40 * 2730170 * 2
def baseEnd_2730170 : Nat := 1401889478485688431019183

theorem tailTrace_2730170 : CollatzResearch.WordTrace tailWord_2730170 prefixEnd_2730170 1401889478485688431019183 := by
  unfold tailWord_2730170
  simp only [CollatzResearch.WordTrace]
  refine ⟨24894370129766960189746991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66384987012711893839325309 24894370129766960189746991)
  ·
    refine ⟨37341555194650440284620487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24894370129766960189746991 37341555194650440284620487)
    ·
      refine ⟨56012332791975660426930731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37341555194650440284620487 56012332791975660426930731)
      ·
        refine ⟨84018499187963490640396097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56012332791975660426930731 84018499187963490640396097)
        ·
          refine ⟨63013874390972617980297073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84018499187963490640396097 63013874390972617980297073)
          ·
            refine ⟨47260405793229463485222805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63013874390972617980297073 47260405793229463485222805)
            ·
              refine ⟨2215331521557631100869819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47260405793229463485222805 2215331521557631100869819)
              ·
                refine ⟨3322997282336446651304729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2215331521557631100869819 3322997282336446651304729)
                ·
                  refine ⟨2492247961752334988478547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3322997282336446651304729 2492247961752334988478547)
                  ·
                    refine ⟨3738371942628502482717821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2492247961752334988478547 3738371942628502482717821)
                    ·
                      refine ⟨1401889478485688431019183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3738371942628502482717821 1401889478485688431019183)
                      ·
                        rfl

theorem cell23_2730170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3].length) (baseStart_2730170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730170 prefixEnd_2730170 := by exact prefixLift 2730170
  have htrace : WordTrace (prefixWord ++ tailWord_2730170) baseStart_2730170 baseEnd_2730170 := by
    simpa [prefixWord, tailWord_2730170, baseEnd_2730170] using wordTrace_append hprefix tailTrace_2730170
  have hstable : (prefixWord ++ tailWord_2730170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730170).length < 2 ^ (prefixWord ++ tailWord_2730170).sum := by decide
  have hdescent : baseEnd_2730170 < baseStart_2730170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730180 : List Nat := [2, 3, 3, 1, 2, 2, 1, 1, 3, 3, 2]
def baseStart_2730180 : Nat := 118140960795 + 2730180 * 2 ^ 59
def prefixEnd_2730180 : Nat := 4983230072969 + 3 ^ 40 * 2730180 * 2
def baseEnd_2730180 : Nat := 1401894613292233391894137

theorem tailTrace_2730180 : CollatzResearch.WordTrace tailWord_2730180 prefixEnd_2730180 1401894613292233391894137 := by
  unfold tailWord_2730180
  simp only [CollatzResearch.WordTrace]
  refine ⟨49788922624515806233425997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66385230166021074977901329 49788922624515806233425997)
  ·
    refine ⟨18670845984193427337534749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49788922624515806233425997 18670845984193427337534749)
    ·
      refine ⟨7001567244072535251575531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18670845984193427337534749 7001567244072535251575531)
      ·
        refine ⟨10502350866108802877363297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7001567244072535251575531 10502350866108802877363297)
        ·
          refine ⟨7876763149581602158022473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10502350866108802877363297 7876763149581602158022473)
          ·
            refine ⟨5907572362186201618516855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7876763149581602158022473 5907572362186201618516855)
            ·
              refine ⟨8861358543279302427775283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5907572362186201618516855 8861358543279302427775283)
              ·
                refine ⟨13292037814918953641662925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8861358543279302427775283 13292037814918953641662925)
                ·
                  refine ⟨4984514180594607615623597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13292037814918953641662925 4984514180594607615623597)
                  ·
                    refine ⟨1869192817722977855858849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4984514180594607615623597 1869192817722977855858849)
                    ·
                      refine ⟨1401894613292233391894137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1869192817722977855858849 1401894613292233391894137)
                      ·
                        rfl

theorem cell23_2730180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_2730180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730180 prefixEnd_2730180 := by exact prefixLift 2730180
  have htrace : WordTrace (prefixWord ++ tailWord_2730180) baseStart_2730180 baseEnd_2730180 := by
    simpa [prefixWord, tailWord_2730180, baseEnd_2730180] using wordTrace_append hprefix tailTrace_2730180
  have hstable : (prefixWord ++ tailWord_2730180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730180).length < 2 ^ (prefixWord ++ tailWord_2730180).sum := by decide
  have hdescent : baseEnd_2730180 < baseStart_2730180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730193 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 6, 2, 2]
def baseStart_2730193 : Nat := 118140960795 + 2730193 * 2 ^ 59
def prefixEnd_2730193 : Nat := 4983230072969 + 3 ^ 40 * 2730193 * 2
def baseEnd_2730193 : Nat := 1401901288540741841031577

theorem tailTrace_2730193 : CollatzResearch.WordTrace tailWord_2730193 prefixEnd_2730193 1401901288540741841031577 := by
  unfold tailWord_2730193
  simp only [CollatzResearch.WordTrace]
  refine ⟨99578319397984515687075233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66385546265323010458050155 99578319397984515687075233)
  ·
    refine ⟨74683739548488386765306425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99578319397984515687075233 74683739548488386765306425)
    ·
      refine ⟨56012804661366290073979819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74683739548488386765306425 56012804661366290073979819)
      ·
        refine ⟨84019206992049435110969729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56012804661366290073979819 84019206992049435110969729)
        ·
          refine ⟨63014405244037076333227297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84019206992049435110969729 63014405244037076333227297)
          ·
            refine ⟨47260803933027807249920473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63014405244037076333227297 47260803933027807249920473)
            ·
              refine ⟨35445602949770855437440355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47260803933027807249920473 35445602949770855437440355)
              ·
                refine ⟨53168404424656283156160533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35445602949770855437440355 53168404424656283156160533)
                ·
                  refine ⟨2492268957405763272945025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53168404424656283156160533 2492268957405763272945025)
                  ·
                    refine ⟨1869201718054322454708769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2492268957405763272945025 1869201718054322454708769)
                    ·
                      refine ⟨1401901288540741841031577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1869201718054322454708769 1401901288540741841031577)
                      ·
                        rfl

theorem cell23_2730193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6, 2, 2].length) (baseStart_2730193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730193 prefixEnd_2730193 := by exact prefixLift 2730193
  have htrace : WordTrace (prefixWord ++ tailWord_2730193) baseStart_2730193 baseEnd_2730193 := by
    simpa [prefixWord, tailWord_2730193, baseEnd_2730193] using wordTrace_append hprefix tailTrace_2730193
  have hstable : (prefixWord ++ tailWord_2730193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730193).length < 2 ^ (prefixWord ++ tailWord_2730193).sum := by decide
  have hdescent : baseEnd_2730193 < baseStart_2730193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730204 : List Nat := [2, 2, 5, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_2730204 : Nat := 118140960795 + 2730204 * 2 ^ 59
def prefixEnd_2730204 : Nat := 4983230072969 + 3 ^ 40 * 2730204 * 2
def baseEnd_2730204 : Nat := 1401906936827941297994027

theorem tailTrace_2730204 : CollatzResearch.WordTrace tailWord_2730204 prefixEnd_2730204 1401906936827941297994027 := by
  unfold tailWord_2730204
  simp only [CollatzResearch.WordTrace]
  refine ⟨49789360300472332282862833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66385813733963109710483777 49789360300472332282862833)
  ·
    refine ⟨37342020225354249212147125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49789360300472332282862833 37342020225354249212147125)
    ·
      refine ⟨3500814396126960863638793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37342020225354249212147125 3500814396126960863638793)
      ·
        refine ⟨2625610797095220647729095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3500814396126960863638793 2625610797095220647729095)
        ·
          refine ⟨3938416195642830971593643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2625610797095220647729095 3938416195642830971593643)
          ·
            refine ⟨5907624293464246457390465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3938416195642830971593643 5907624293464246457390465)
            ·
              refine ⟨4430718220098184843042849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5907624293464246457390465 4430718220098184843042849)
              ·
                refine ⟨3323038665073638632282137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4430718220098184843042849 3323038665073638632282137)
                ·
                  refine ⟨2492278998805228974211603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3323038665073638632282137 2492278998805228974211603)
                  ·
                    refine ⟨3738418498207843461317405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2492278998805228974211603 3738418498207843461317405)
                    ·
                      refine ⟨1401906936827941297994027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3738418498207843461317405 1401906936827941297994027)
                      ·
                        rfl

theorem cell23_2730204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_2730204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730204 prefixEnd_2730204 := by exact prefixLift 2730204
  have htrace : WordTrace (prefixWord ++ tailWord_2730204) baseStart_2730204 baseEnd_2730204 := by
    simpa [prefixWord, tailWord_2730204, baseEnd_2730204] using wordTrace_append hprefix tailTrace_2730204
  have hstable : (prefixWord ++ tailWord_2730204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730204).length < 2 ^ (prefixWord ++ tailWord_2730204).sum := by decide
  have hdescent : baseEnd_2730204 < baseStart_2730204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730259 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 1, 10]
def baseStart_2730259 : Nat := 118140960795 + 2730259 * 2 ^ 59
def prefixEnd_2730259 : Nat := 4983230072969 + 3 ^ 40 * 2730259 * 2
def baseEnd_2730259 : Nat := 467311726087979527602091

theorem tailTrace_2730259 : CollatzResearch.WordTrace tailWord_2730259 prefixEnd_2730259 467311726087979527602091 := by
  unfold tailWord_2730259
  simp only [CollatzResearch.WordTrace]
  refine ⟨99580726615745408958977831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66387151077163605972651887 99580726615745408958977831)
  ·
    refine ⟨149371089923618113438466747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99580726615745408958977831 149371089923618113438466747)
    ·
      refine ⟨224056634885427170157700121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149371089923618113438466747 224056634885427170157700121)
      ·
        refine ⟨168042476164070377618275091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224056634885427170157700121 168042476164070377618275091)
        ·
          refine ⟨252063714246105566427412637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168042476164070377618275091 252063714246105566427412637)
          ·
            refine ⟨94523892842289587410279739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 252063714246105566427412637 94523892842289587410279739)
            ·
              refine ⟨141785839263434381115419609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94523892842289587410279739 141785839263434381115419609)
              ·
                refine ⟨106339379447575785836564707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141785839263434381115419609 106339379447575785836564707)
                ·
                  refine ⟨159509069171363678754847061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106339379447575785836564707 159509069171363678754847061)
                  ·
                    refine ⟨467311726087979527602091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 159509069171363678754847061 467311726087979527602091)
                    ·
                      rfl

theorem cell23_2730259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 10].length) (baseStart_2730259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730259 prefixEnd_2730259 := by exact prefixLift 2730259
  have htrace : WordTrace (prefixWord ++ tailWord_2730259) baseStart_2730259 baseEnd_2730259 := by
    simpa [prefixWord, tailWord_2730259, baseEnd_2730259] using wordTrace_append hprefix tailTrace_2730259
  have hstable : (prefixWord ++ tailWord_2730259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730259).length < 2 ^ (prefixWord ++ tailWord_2730259).sum := by decide
  have hdescent : baseEnd_2730259 < baseStart_2730259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730293 : List Nat := [1, 3, 3, 1, 2, 1, 1, 4, 3, 4]
def baseStart_2730293 : Nat := 118140960795 + 2730293 * 2 ^ 59
def prefixEnd_2730293 : Nat := 4983230072969 + 3 ^ 40 * 2730293 * 2
def baseEnd_2730293 : Nat := 467317545535397149927039

theorem tailTrace_2730293 : CollatzResearch.WordTrace tailWord_2730293 prefixEnd_2730293 467317545535397149927039 := by
  unfold tailWord_2730293
  simp only [CollatzResearch.WordTrace]
  refine ⟨99581966697622232765715533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66387977798414821843810355 99581966697622232765715533)
  ·
    refine ⟨37343237511608337287143325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99581966697622232765715533 37343237511608337287143325)
    ·
      refine ⟨14003714066853126482678747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37343237511608337287143325 14003714066853126482678747)
      ·
        refine ⟨21005571100279689724018121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14003714066853126482678747 21005571100279689724018121)
        ·
          refine ⟨15754178325209767293013591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21005571100279689724018121 15754178325209767293013591)
          ·
            refine ⟨23631267487814650939520387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15754178325209767293013591 23631267487814650939520387)
            ·
              refine ⟨35446901231721976409280581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23631267487814650939520387 35446901231721976409280581)
              ·
                refine ⟨6646293980947870576740109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35446901231721976409280581 6646293980947870576740109)
                ·
                  refine ⟨2492360242855451466277541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6646293980947870576740109 2492360242855451466277541)
                  ·
                    refine ⟨467317545535397149927039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2492360242855451466277541 467317545535397149927039)
                    ·
                      rfl

theorem cell23_2730293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_2730293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730293 prefixEnd_2730293 := by exact prefixLift 2730293
  have htrace : WordTrace (prefixWord ++ tailWord_2730293) baseStart_2730293 baseEnd_2730293 := by
    simpa [prefixWord, tailWord_2730293, baseEnd_2730293] using wordTrace_append hprefix tailTrace_2730293
  have hstable : (prefixWord ++ tailWord_2730293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730293).length < 2 ^ (prefixWord ++ tailWord_2730293).sum := by decide
  have hdescent : baseEnd_2730293 < baseStart_2730293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730303 : List Nat := [1, 1, 2, 2, 4, 1, 2, 3, 2, 2, 3]
def baseStart_2730303 : Nat := 118140960795 + 2730303 * 2 ^ 59
def prefixEnd_2730303 : Nat := 4983230072969 + 3 ^ 40 * 2730303 * 2
def baseEnd_2730303 : Nat := 1401957771412736410656071

theorem tailTrace_2730303 : CollatzResearch.WordTrace tailWord_2730303 prefixEnd_2730303 1401957771412736410656071 := by
  unfold tailWord_2730303
  simp only [CollatzResearch.WordTrace]
  refine ⟨99582331427586004473579563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66388220951724002982386375 99582331427586004473579563)
  ·
    refine ⟨149373497141379006710369345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99582331427586004473579563 149373497141379006710369345)
    ·
      refine ⟨112030122856034255032777009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149373497141379006710369345 112030122856034255032777009)
      ·
        refine ⟨84022592142025691274582757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112030122856034255032777009 84022592142025691274582757)
        ·
          refine ⟨15754236026629817113984267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84022592142025691274582757 15754236026629817113984267)
          ·
            refine ⟨23631354039944725670976401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15754236026629817113984267 23631354039944725670976401)
            ·
              refine ⟨17723515529958544253232301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23631354039944725670976401 17723515529958544253232301)
              ·
                refine ⟨6646318323734454094962113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17723515529958544253232301 6646318323734454094962113)
                ·
                  refine ⟨4984738742800840571221585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6646318323734454094962113 4984738742800840571221585)
                  ·
                    refine ⟨3738554057100630428416189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4984738742800840571221585 3738554057100630428416189)
                    ·
                      refine ⟨1401957771412736410656071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3738554057100630428416189 1401957771412736410656071)
                      ·
                        rfl

theorem cell23_2730303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2, 3].length) (baseStart_2730303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730303 prefixEnd_2730303 := by exact prefixLift 2730303
  have htrace : WordTrace (prefixWord ++ tailWord_2730303) baseStart_2730303 baseEnd_2730303 := by
    simpa [prefixWord, tailWord_2730303, baseEnd_2730303] using wordTrace_append hprefix tailTrace_2730303
  have hstable : (prefixWord ++ tailWord_2730303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730303).length < 2 ^ (prefixWord ++ tailWord_2730303).sum := by decide
  have hdescent : baseEnd_2730303 < baseStart_2730303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730327 : List Nat := [1, 1, 3, 2, 3, 1, 5, 2, 1, 4]
def baseStart_2730327 : Nat := 118140960795 + 2730327 * 2 ^ 59
def prefixEnd_2730327 : Nat := 4983230072969 + 3 ^ 40 * 2730327 * 2
def baseEnd_2730327 : Nat := 467323364982814772251987

theorem tailTrace_2730327 : CollatzResearch.WordTrace tailWord_2730327 prefixEnd_2730327 467323364982814772251987 := by
  unfold tailWord_2730327
  simp only [CollatzResearch.WordTrace]
  refine ⟨99583206779499056572453235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66388804519666037714968823 99583206779499056572453235)
  ·
    refine ⟨149374810169248584858679853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99583206779499056572453235 149374810169248584858679853)
    ·
      refine ⟨56015553813468219322004945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149374810169248584858679853 56015553813468219322004945)
      ·
        refine ⟨42011665360101164491503709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56015553813468219322004945 42011665360101164491503709)
        ·
          refine ⟨15754374510037936684313891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42011665360101164491503709 15754374510037936684313891)
          ·
            refine ⟨23631561765056905026470837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15754374510037936684313891 23631561765056905026470837)
            ·
              refine ⟨2215458915474084846231641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23631561765056905026470837 2215458915474084846231641)
              ·
                refine ⟨1661594186605563634673731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2215458915474084846231641 1661594186605563634673731)
                ·
                  refine ⟨2492391279908345452010597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1661594186605563634673731 2492391279908345452010597)
                  ·
                    refine ⟨467323364982814772251987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2492391279908345452010597 467323364982814772251987)
                    ·
                      rfl

theorem cell23_2730327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2, 1, 4].length) (baseStart_2730327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730327 prefixEnd_2730327 := by exact prefixLift 2730327
  have htrace : WordTrace (prefixWord ++ tailWord_2730327) baseStart_2730327 baseEnd_2730327 := by
    simpa [prefixWord, tailWord_2730327, baseEnd_2730327] using wordTrace_append hprefix tailTrace_2730327
  have hstable : (prefixWord ++ tailWord_2730327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730327).length < 2 ^ (prefixWord ++ tailWord_2730327).sum := by decide
  have hdescent : baseEnd_2730327 < baseStart_2730327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730378 : List Nat := [3, 1, 2, 5, 2, 1, 2, 2, 1, 4]
def baseStart_2730378 : Nat := 118140960795 + 2730378 * 2 ^ 59
def prefixEnd_2730378 : Nat := 4983230072969 + 3 ^ 40 * 2730378 * 2
def baseEnd_2730378 : Nat := 467332094153941205739409

theorem tailTrace_2730378 : CollatzResearch.WordTrace tailWord_2730378 prefixEnd_2730378 467332094153941205739409 := by
  unfold tailWord_2730378
  simp only [CollatzResearch.WordTrace]
  refine ⟨24896266725578573070639947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66390044601542861521706525 24896266725578573070639947)
  ·
    refine ⟨37344400088367859605959921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24896266725578573070639947 37344400088367859605959921)
    ·
      refine ⟨28008300066275894704469941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37344400088367859605959921 28008300066275894704469941)
      ·
        refine ⟨2625778131213365128544057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28008300066275894704469941 2625778131213365128544057)
        ·
          refine ⟨1969333598410023846408043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2625778131213365128544057 1969333598410023846408043)
          ·
            refine ⟨2954000397615035769612065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1969333598410023846408043 2954000397615035769612065)
            ·
              refine ⟨2215500298211276827209049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2954000397615035769612065 2215500298211276827209049)
              ·
                refine ⟨1661625223658457620406787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2215500298211276827209049 1661625223658457620406787)
                ·
                  refine ⟨2492437835487686430610181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1661625223658457620406787 2492437835487686430610181)
                  ·
                    refine ⟨467332094153941205739409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2492437835487686430610181 467332094153941205739409)
                    ·
                      rfl

theorem cell23_2730378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_2730378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730378 prefixEnd_2730378 := by exact prefixLift 2730378
  have htrace : WordTrace (prefixWord ++ tailWord_2730378) baseStart_2730378 baseEnd_2730378 := by
    simpa [prefixWord, tailWord_2730378, baseEnd_2730378] using wordTrace_append hprefix tailTrace_2730378
  have hstable : (prefixWord ++ tailWord_2730378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730378).length < 2 ^ (prefixWord ++ tailWord_2730378).sum := by decide
  have hdescent : baseEnd_2730378 < baseStart_2730378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730393 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 5, 2, 3]
def baseStart_2730393 : Nat := 118140960795 + 2730393 * 2 ^ 59
def prefixEnd_2730393 : Nat := 4983230072969 + 3 ^ 40 * 2730393 * 2
def baseEnd_2730393 : Nat := 1402003984671641058530657

theorem tailTrace_2730393 : CollatzResearch.WordTrace tailWord_2730393 prefixEnd_2730393 1402003984671641058530657 := by
  unfold tailWord_2730393
  simp only [CollatzResearch.WordTrace]
  refine ⟨99585613997259949844355833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66390409331506633229570555 99585613997259949844355833)
  ·
    refine ⟨74689210497944962383266875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99585613997259949844355833 74689210497944962383266875)
    ·
      refine ⟨112033815746917443574900313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74689210497944962383266875 112033815746917443574900313)
      ·
        refine ⟨84025361810188082681175235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112033815746917443574900313 84025361810188082681175235)
        ·
          refine ⟨126038042715282124021762853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84025361810188082681175235 126038042715282124021762853)
          ·
            refine ⟨23632133009115398254080535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126038042715282124021762853 23632133009115398254080535)
            ·
              refine ⟨35448199513673097381120803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23632133009115398254080535 35448199513673097381120803)
              ·
                refine ⟨53172299270509646071681205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35448199513673097381120803 53172299270509646071681205)
                ·
                  refine ⟨4984903056610279319220113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53172299270509646071681205 4984903056610279319220113)
                  ·
                    refine ⟨3738677292457709489415085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4984903056610279319220113 3738677292457709489415085)
                    ·
                      refine ⟨1402003984671641058530657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3738677292457709489415085 1402003984671641058530657)
                      ·
                        rfl

theorem cell23_2730393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 2, 3].length) (baseStart_2730393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730393 prefixEnd_2730393 := by exact prefixLift 2730393
  have htrace : WordTrace (prefixWord ++ tailWord_2730393) baseStart_2730393 baseEnd_2730393 := by
    simpa [prefixWord, tailWord_2730393, baseEnd_2730393] using wordTrace_append hprefix tailTrace_2730393
  have hstable : (prefixWord ++ tailWord_2730393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730393).length < 2 ^ (prefixWord ++ tailWord_2730393).sum := by decide
  have hdescent : baseEnd_2730393 < baseStart_2730393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730400 : List Nat := [2, 1, 1, 4, 1, 3, 2, 3, 2, 4]
def baseStart_2730400 : Nat := 118140960795 + 2730400 * 2 ^ 59
def prefixEnd_2730400 : Nat := 4983230072969 + 3 ^ 40 * 2730400 * 2
def baseEnd_2730400 : Nat := 467335859678740843714375

theorem tailTrace_2730400 : CollatzResearch.WordTrace tailWord_2730400 prefixEnd_2730400 467335859678740843714375 := by
  unfold tailWord_2730400
  simp only [CollatzResearch.WordTrace]
  refine ⟨49792934654117295019930327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66390579538823060026573769 49792934654117295019930327)
  ·
    refine ⟨74689401981175942529895491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49792934654117295019930327 74689401981175942529895491)
    ·
      refine ⟨112034102971763913794843237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74689401981175942529895491 112034102971763913794843237)
      ·
        refine ⟨21006394307205733836533107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112034102971763913794843237 21006394307205733836533107)
        ·
          refine ⟨31509591460808600754799661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21006394307205733836533107 31509591460808600754799661)
          ·
            refine ⟨11816096797803225283049873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31509591460808600754799661 11816096797803225283049873)
            ·
              refine ⟨8862072598352418962287405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11816096797803225283049873 8862072598352418962287405)
              ·
                refine ⟨3323277224382157110857777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8862072598352418962287405 3323277224382157110857777)
                ·
                  refine ⟨2492457918286617833143333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3323277224382157110857777 2492457918286617833143333)
                  ·
                    refine ⟨467335859678740843714375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2492457918286617833143333 467335859678740843714375)
                    ·
                      rfl

theorem cell23_2730400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 2, 4].length) (baseStart_2730400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730400 prefixEnd_2730400 := by exact prefixLift 2730400
  have htrace : WordTrace (prefixWord ++ tailWord_2730400) baseStart_2730400 baseEnd_2730400 := by
    simpa [prefixWord, tailWord_2730400, baseEnd_2730400] using wordTrace_append hprefix tailTrace_2730400
  have hstable : (prefixWord ++ tailWord_2730400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730400).length < 2 ^ (prefixWord ++ tailWord_2730400).sum := by decide
  have hdescent : baseEnd_2730400 < baseStart_2730400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730403 : List Nat := [1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 4]
def baseStart_2730403 : Nat := 118140960795 + 2730403 * 2 ^ 59
def prefixEnd_2730403 : Nat := 4983230072969 + 3 ^ 40 * 2730403 * 2
def baseEnd_2730403 : Nat := 1402009119478186019405611

theorem tailTrace_2730403 : CollatzResearch.WordTrace tailWord_2730403 prefixEnd_2730403 1402009119478186019405611 := by
  unfold tailWord_2730403
  simp only [CollatzResearch.WordTrace]
  refine ⟨99585978727223721552219863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66390652484815814368146575 99585978727223721552219863)
  ·
    refine ⟨149378968090835582328329795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99585978727223721552219863 149378968090835582328329795)
    ·
      refine ⟨224068452136253373492494693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149378968090835582328329795 224068452136253373492494693)
      ·
        refine ⟨42012834775547507529842755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 224068452136253373492494693 42012834775547507529842755)
        ·
          refine ⟨63019252163321261294764133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42012834775547507529842755 63019252163321261294764133)
          ·
            refine ⟨11816109780622736492768275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63019252163321261294764133 11816109780622736492768275)
            ·
              refine ⟨17724164670934104739152413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11816109780622736492768275 17724164670934104739152413)
              ·
                refine ⟨6646561751600289277182155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17724164670934104739152413 6646561751600289277182155)
                ·
                  refine ⟨9969842627400433915773233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6646561751600289277182155 9969842627400433915773233)
                  ·
                    refine ⟨7477381970550325436829925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9969842627400433915773233 7477381970550325436829925)
                    ·
                      refine ⟨1402009119478186019405611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7477381970550325436829925 1402009119478186019405611)
                      ·
                        rfl

theorem cell23_2730403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_2730403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730403 prefixEnd_2730403 := by exact prefixLift 2730403
  have htrace : WordTrace (prefixWord ++ tailWord_2730403) baseStart_2730403 baseEnd_2730403 := by
    simpa [prefixWord, tailWord_2730403, baseEnd_2730403] using wordTrace_append hprefix tailTrace_2730403
  have hstable : (prefixWord ++ tailWord_2730403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730403).length < 2 ^ (prefixWord ++ tailWord_2730403).sum := by decide
  have hdescent : baseEnd_2730403 < baseStart_2730403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730407 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 5, 2, 2]
def baseStart_2730407 : Nat := 118140960795 + 2730407 * 2 ^ 59
def prefixEnd_2730407 : Nat := 4983230072969 + 3 ^ 40 * 2730407 * 2
def baseEnd_2730407 : Nat := 1402011173400804003755593

theorem tailTrace_2730407 : CollatzResearch.WordTrace tailWord_2730407 prefixEnd_2730407 1402011173400804003755593 := by
  unfold tailWord_2730407
  simp only [CollatzResearch.WordTrace]
  refine ⟨99586124619209230235365475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66390749746139486823576983 99586124619209230235365475)
  ·
    refine ⟨149379186928813845353048213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99586124619209230235365475 149379186928813845353048213)
    ·
      refine ⟨7002149387288149000924135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 149379186928813845353048213 7002149387288149000924135)
      ·
        refine ⟨10503224080932223501386203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7002149387288149000924135 10503224080932223501386203)
        ·
          refine ⟨15754836121398335252079305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10503224080932223501386203 15754836121398335252079305)
          ·
            refine ⟨11816127091048751439059479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15754836121398335252079305 11816127091048751439059479)
            ·
              refine ⟨17724190636573127158589219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11816127091048751439059479 17724190636573127158589219)
              ·
                refine ⟨26586285954859690737883829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17724190636573127158589219 26586285954859690737883829)
                ·
                  refine ⟨2492464308268096006676609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26586285954859690737883829 2492464308268096006676609)
                  ·
                    refine ⟨1869348231201072005007457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2492464308268096006676609 1869348231201072005007457)
                    ·
                      refine ⟨1402011173400804003755593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1869348231201072005007457 1402011173400804003755593)
                      ·
                        rfl

theorem cell23_2730407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_2730407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730407 prefixEnd_2730407 := by exact prefixLift 2730407
  have htrace : WordTrace (prefixWord ++ tailWord_2730407) baseStart_2730407 baseEnd_2730407 := by
    simpa [prefixWord, tailWord_2730407, baseEnd_2730407] using wordTrace_append hprefix tailTrace_2730407
  have hstable : (prefixWord ++ tailWord_2730407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730407).length < 2 ^ (prefixWord ++ tailWord_2730407).sum := by decide
  have hdescent : baseEnd_2730407 < baseStart_2730407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730416 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 6]
def baseStart_2730416 : Nat := 118140960795 + 2730416 * 2 ^ 59
def prefixEnd_2730416 : Nat := 4983230072969 + 3 ^ 40 * 2730416 * 2
def baseEnd_2730416 : Nat := 1402015794726694468543051

theorem tailTrace_2730416 : CollatzResearch.WordTrace tailWord_2730416 prefixEnd_2730416 1402015794726694468543051 := by
  unfold tailWord_2730416
  simp only [CollatzResearch.WordTrace]
  refine ⟨49793226438088312386221551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66390968584117749848295401 49793226438088312386221551)
  ·
    refine ⟨74689839657132468579332327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49793226438088312386221551 74689839657132468579332327)
    ·
      refine ⟨112034759485698702868998491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74689839657132468579332327 112034759485698702868998491)
      ·
        refine ⟨168052139228548054303497737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112034759485698702868998491 168052139228548054303497737)
        ·
          refine ⟨126039104421411040727623303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168052139228548054303497737 126039104421411040727623303)
          ·
            refine ⟨189058656632116561091434955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126039104421411040727623303 189058656632116561091434955)
            ·
              refine ⟨283587984948174841637152433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189058656632116561091434955 283587984948174841637152433)
              ·
                refine ⟨212690988711131131227864325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283587984948174841637152433 212690988711131131227864325)
                ·
                  refine ⟨39879560383337087105224561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 212690988711131131227864325 39879560383337087105224561)
                  ·
                    refine ⟨29909670287502815328918421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39879560383337087105224561 29909670287502815328918421)
                    ·
                      refine ⟨1402015794726694468543051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29909670287502815328918421 1402015794726694468543051)
                      ·
                        rfl

theorem cell23_2730416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 6].length) (baseStart_2730416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730416 prefixEnd_2730416 := by exact prefixLift 2730416
  have htrace : WordTrace (prefixWord ++ tailWord_2730416) baseStart_2730416 baseEnd_2730416 := by
    simpa [prefixWord, tailWord_2730416, baseEnd_2730416] using wordTrace_append hprefix tailTrace_2730416
  have hstable : (prefixWord ++ tailWord_2730416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730416).length < 2 ^ (prefixWord ++ tailWord_2730416).sum := by decide
  have hdescent : baseEnd_2730416 < baseStart_2730416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730480 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 3, 4, 2]
def baseStart_2730480 : Nat := 118140960795 + 2730480 * 2 ^ 59
def prefixEnd_2730480 : Nat := 4983230072969 + 3 ^ 40 * 2730480 * 2
def baseEnd_2730480 : Nat := 1402048657488582218142757

theorem tailTrace_2730480 : CollatzResearch.WordTrace tailWord_2730480 prefixEnd_2730480 1402048657488582218142757 := by
  unfold tailWord_2730480
  simp only [CollatzResearch.WordTrace]
  refine ⟨49794393573972381851386447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66392524765296509135181929 49794393573972381851386447)
  ·
    refine ⟨74691590360958572777079671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49794393573972381851386447 74691590360958572777079671)
    ·
      refine ⟨112037385541437859165619507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74691590360958572777079671 112037385541437859165619507)
      ·
        refine ⟨168056078312156788748429261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112037385541437859165619507 168056078312156788748429261)
        ·
          refine ⟨63021029367058795780660973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168056078312156788748429261 63021029367058795780660973)
          ·
            refine ⟨23632886012647048417747865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63021029367058795780660973 23632886012647048417747865)
            ·
              refine ⟨17724664509485286313310899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23632886012647048417747865 17724664509485286313310899)
              ·
                refine ⟨26586996764227929469966349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17724664509485286313310899 26586996764227929469966349)
                ·
                  refine ⟨9970123786585473551237381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26586996764227929469966349 9970123786585473551237381)
                  ·
                    refine ⟨1869398209984776290857009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9970123786585473551237381 1869398209984776290857009)
                    ·
                      refine ⟨1402048657488582218142757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1869398209984776290857009 1402048657488582218142757)
                      ·
                        rfl

theorem cell23_2730480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 3, 4, 2].length) (baseStart_2730480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730480 prefixEnd_2730480 := by exact prefixLift 2730480
  have htrace : WordTrace (prefixWord ++ tailWord_2730480) baseStart_2730480 baseEnd_2730480 := by
    simpa [prefixWord, tailWord_2730480, baseEnd_2730480] using wordTrace_append hprefix tailTrace_2730480
  have hstable : (prefixWord ++ tailWord_2730480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730480).length < 2 ^ (prefixWord ++ tailWord_2730480).sum := by decide
  have hdescent : baseEnd_2730480 < baseStart_2730480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730483 : List Nat := [1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 5]
def baseStart_2730483 : Nat := 118140960795 + 2730483 * 2 ^ 59
def prefixEnd_2730483 : Nat := 4983230072969 + 3 ^ 40 * 2730483 * 2
def baseEnd_2730483 : Nat := 1402050197930545706405243

theorem tailTrace_2730483 : CollatzResearch.WordTrace tailWord_2730483 prefixEnd_2730483 1402050197930545706405243 := by
  unfold tailWord_2730483
  simp only [CollatzResearch.WordTrace]
  refine ⟨99588896566933895215132103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66392597711289263476754735 99588896566933895215132103)
  ·
    refine ⟨149383344850400842822698155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99588896566933895215132103 149383344850400842822698155)
    ·
      refine ⟨224075017275601264234047233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149383344850400842822698155 224075017275601264234047233)
      ·
        refine ⟨168056262956700948175535425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224075017275601264234047233 168056262956700948175535425)
        ·
          refine ⟨126042197217525711131651569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168056262956700948175535425 126042197217525711131651569)
          ·
            refine ⟨94531647913144283348738677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126042197217525711131651569 94531647913144283348738677)
            ·
              refine ⟨8862341991857276563944251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94531647913144283348738677 8862341991857276563944251)
              ·
                refine ⟨13293512987785914845916377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8862341991857276563944251 13293512987785914845916377)
                ·
                  refine ⟨9970134740839436134437283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13293512987785914845916377 9970134740839436134437283)
                  ·
                    refine ⟨14955202111259154201655925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9970134740839436134437283 14955202111259154201655925)
                    ·
                      refine ⟨1402050197930545706405243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14955202111259154201655925 1402050197930545706405243)
                      ·
                        rfl

theorem cell23_2730483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 5].length) (baseStart_2730483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730483 prefixEnd_2730483 := by exact prefixLift 2730483
  have htrace : WordTrace (prefixWord ++ tailWord_2730483) baseStart_2730483 baseEnd_2730483 := by
    simpa [prefixWord, tailWord_2730483, baseEnd_2730483] using wordTrace_append hprefix tailTrace_2730483
  have hstable : (prefixWord ++ tailWord_2730483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730483).length < 2 ^ (prefixWord ++ tailWord_2730483).sum := by decide
  have hdescent : baseEnd_2730483 < baseStart_2730483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730530 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 4, 3, 3]
def baseStart_2730530 : Nat := 118140960795 + 2730530 * 2 ^ 59
def prefixEnd_2730530 : Nat := 4983230072969 + 3 ^ 40 * 2730530 * 2
def baseEnd_2730530 : Nat := 1402074331521307022517527

theorem tailTrace_2730530 : CollatzResearch.WordTrace tailWord_2730530 prefixEnd_2730530 1402074331521307022517527 := by
  unfold tailWord_2730530
  simp only [CollatzResearch.WordTrace]
  refine ⟨24897652699440905560523261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66393740531842414828062029 24897652699440905560523261)
  ·
    refine ⟨9336619762290339585196223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24897652699440905560523261 9336619762290339585196223)
    ·
      refine ⟨14004929643435509377794335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9336619762290339585196223 14004929643435509377794335)
      ·
        refine ⟨21007394465153264066691503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14004929643435509377794335 21007394465153264066691503)
        ·
          refine ⟨31511091697729896100037255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21007394465153264066691503 31511091697729896100037255)
          ·
            refine ⟨47266637546594844150055883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31511091697729896100037255 47266637546594844150055883)
            ·
              refine ⟨70899956319892266225083825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47266637546594844150055883 70899956319892266225083825)
              ·
                refine ⟨53174967239919199668812869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70899956319892266225083825 53174967239919199668812869)
                ·
                  refine ⟨9970306357484849937902413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53174967239919199668812869 9970306357484849937902413)
                  ·
                    refine ⟨3738864884056818726713405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9970306357484849937902413 3738864884056818726713405)
                    ·
                      refine ⟨1402074331521307022517527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3738864884056818726713405 1402074331521307022517527)
                      ·
                        rfl

theorem cell23_2730530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_2730530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730530 prefixEnd_2730530 := by exact prefixLift 2730530
  have htrace : WordTrace (prefixWord ++ tailWord_2730530) baseStart_2730530 baseEnd_2730530 := by
    simpa [prefixWord, tailWord_2730530, baseEnd_2730530] using wordTrace_append hprefix tailTrace_2730530
  have hstable : (prefixWord ++ tailWord_2730530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730530).length < 2 ^ (prefixWord ++ tailWord_2730530).sum := by decide
  have hdescent : baseEnd_2730530 < baseStart_2730530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730533 : List Nat := [1, 3, 1, 2, 2, 1, 2, 3, 1, 7]
def baseStart_2730533 : Nat := 118140960795 + 2730533 * 2 ^ 59
def prefixEnd_2730533 : Nat := 4983230072969 + 3 ^ 40 * 2730533 * 2
def baseEnd_2730533 : Nat := 467358623987756836926671

theorem tailTrace_2730533 : CollatzResearch.WordTrace tailWord_2730533 prefixEnd_2730533 467358623987756836926671 := by
  unfold tailWord_2730533
  simp only [CollatzResearch.WordTrace]
  refine ⟨99590720216752753754452253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66393813477835169169634835 99590720216752753754452253)
  ·
    refine ⟨37346520081282282657919595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99590720216752753754452253 37346520081282282657919595)
    ·
      refine ⟨56019780121923423986879393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37346520081282282657919595 56019780121923423986879393)
      ·
        refine ⟨42014835091442567990159545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56019780121923423986879393 42014835091442567990159545)
        ·
          refine ⟨31511126318581925992619659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42014835091442567990159545 31511126318581925992619659)
          ·
            refine ⟨47266689477872888988929489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31511126318581925992619659 47266689477872888988929489)
            ·
              refine ⟨35450017108404666741697117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47266689477872888988929489 35450017108404666741697117)
              ·
                refine ⟨13293756415651750028136419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35450017108404666741697117 13293756415651750028136419)
                ·
                  refine ⟨19940634623477625042204629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13293756415651750028136419 19940634623477625042204629)
                  ·
                    refine ⟨467358623987756836926671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19940634623477625042204629 467358623987756836926671)
                    ·
                      rfl

theorem cell23_2730533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 7].length) (baseStart_2730533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730533 prefixEnd_2730533 := by exact prefixLift 2730533
  have htrace : WordTrace (prefixWord ++ tailWord_2730533) baseStart_2730533 baseEnd_2730533 := by
    simpa [prefixWord, tailWord_2730533, baseEnd_2730533] using wordTrace_append hprefix tailTrace_2730533
  have hstable : (prefixWord ++ tailWord_2730533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730533).length < 2 ^ (prefixWord ++ tailWord_2730533).sum := by decide
  have hdescent : baseEnd_2730533 < baseStart_2730533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730540 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 4, 5, 2]
def baseStart_2730540 : Nat := 118140960795 + 2730540 * 2 ^ 59
def prefixEnd_2730540 : Nat := 4983230072969 + 3 ^ 40 * 2730540 * 2
def baseEnd_2730540 : Nat := 1402079466327851983392481

theorem tailTrace_2730540 : CollatzResearch.WordTrace tailWord_2730540 prefixEnd_2730540 1402079466327851983392481 := by
  unfold tailWord_2730540
  simp only [CollatzResearch.WordTrace]
  refine ⟨49795487763863696974978537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66393983685151595966638049 49795487763863696974978537)
  ·
    refine ⟨37346615822897772731233903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49795487763863696974978537 37346615822897772731233903)
    ·
      refine ⟨56019923734346659096850855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37346615822897772731233903 56019923734346659096850855)
      ·
        refine ⟨84029885601519988645276283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56019923734346659096850855 84029885601519988645276283)
        ·
          refine ⟨126044828402279982967914425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84029885601519988645276283 126044828402279982967914425)
          ·
            refine ⟨94533621301709987225935819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126044828402279982967914425 94533621301709987225935819)
            ·
              refine ⟨141800431952564980838903729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94533621301709987225935819 141800431952564980838903729)
              ·
                refine ⟨106350323964423735629177797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141800431952564980838903729 106350323964423735629177797)
                ·
                  refine ⟨19940685743329450430470837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106350323964423735629177797 19940685743329450430470837)
                  ·
                    refine ⟨1869439288437135977856641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19940685743329450430470837 1869439288437135977856641)
                    ·
                      refine ⟨1402079466327851983392481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1869439288437135977856641 1402079466327851983392481)
                      ·
                        rfl

theorem cell23_2730540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 5, 2].length) (baseStart_2730540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730540 prefixEnd_2730540 := by exact prefixLift 2730540
  have htrace : WordTrace (prefixWord ++ tailWord_2730540) baseStart_2730540 baseEnd_2730540 := by
    simpa [prefixWord, tailWord_2730540, baseEnd_2730540] using wordTrace_append hprefix tailTrace_2730540
  have hstable : (prefixWord ++ tailWord_2730540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730540).length < 2 ^ (prefixWord ++ tailWord_2730540).sum := by decide
  have hdescent : baseEnd_2730540 < baseStart_2730540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730554 : List Nat := [3, 1, 1, 1, 3, 5, 2, 2, 5]
def baseStart_2730554 : Nat := 118140960795 + 2730554 * 2 ^ 59
def prefixEnd_2730554 : Nat := 4983230072969 + 3 ^ 40 * 2730554 * 2
def baseEnd_2730554 : Nat := 155787406117446103179713

theorem tailTrace_2730554 : CollatzResearch.WordTrace tailWord_2730554 prefixEnd_2730554 155787406117446103179713 := by
  unfold tailWord_2730554
  simp only [CollatzResearch.WordTrace]
  refine ⟨24897871537419168585241679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66394324099784449560644477 24897871537419168585241679)
  ·
    refine ⟨37346807306128752877862519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24897871537419168585241679 37346807306128752877862519)
    ·
      refine ⟨56020210959193129316793779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37346807306128752877862519 56020210959193129316793779)
      ·
        refine ⟨84030316438789693975190669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56020210959193129316793779 84030316438789693975190669)
        ·
          refine ⟨31511368664546135240696501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84030316438789693975190669 31511368664546135240696501)
          ·
            refine ⟨2954190812301200178815297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31511368664546135240696501 2954190812301200178815297)
            ·
              refine ⟨2215643109225900134111473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2954190812301200178815297 2215643109225900134111473)
              ·
                refine ⟨1661732331919425100583605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2215643109225900134111473 1661732331919425100583605)
                ·
                  refine ⟨155787406117446103179713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1661732331919425100583605 155787406117446103179713)
                  ·
                    rfl

theorem cell23_2730554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2, 5].length) (baseStart_2730554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730554 prefixEnd_2730554 := by exact prefixLift 2730554
  have htrace : WordTrace (prefixWord ++ tailWord_2730554) baseStart_2730554 baseEnd_2730554 := by
    simpa [prefixWord, tailWord_2730554, baseEnd_2730554] using wordTrace_append hprefix tailTrace_2730554
  have hstable : (prefixWord ++ tailWord_2730554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730554).length < 2 ^ (prefixWord ++ tailWord_2730554).sum := by decide
  have hdescent : baseEnd_2730554 < baseStart_2730554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730557 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 2, 5, 2]
def baseStart_2730557 : Nat := 118140960795 + 2730557 * 2 ^ 59
def prefixEnd_2730557 : Nat := 4983230072969 + 3 ^ 40 * 2730557 * 2
def baseEnd_2730557 : Nat := 1402088195498978416879903

theorem tailTrace_2730557 : CollatzResearch.WordTrace tailWord_2730557 prefixEnd_2730557 1402088195498978416879903 := by
  unfold tailWord_2730557
  simp only [CollatzResearch.WordTrace]
  refine ⟨99591595568665805853325925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66394397045777203902217283 99591595568665805853325925)
  ·
    refine ⟨18673424169124838597498611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99591595568665805853325925 18673424169124838597498611)
    ·
      refine ⟨28010136253687257896247917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18673424169124838597498611 28010136253687257896247917)
      ·
        refine ⟨10503801095132721711092969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28010136253687257896247917 10503801095132721711092969)
        ·
          refine ⟨7877850821349541283319727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10503801095132721711092969 7877850821349541283319727)
          ·
            refine ⟨11816776232024311924979591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7877850821349541283319727 11816776232024311924979591)
            ·
              refine ⟨17725164348036467887469387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11816776232024311924979591 17725164348036467887469387)
              ·
                refine ⟨26587746522054701831204081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17725164348036467887469387 26587746522054701831204081)
                ·
                  refine ⟨19940809891541026373403061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26587746522054701831204081 19940809891541026373403061)
                  ·
                    refine ⟨1869450927331971222506537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19940809891541026373403061 1869450927331971222506537)
                    ·
                      refine ⟨1402088195498978416879903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1869450927331971222506537 1402088195498978416879903)
                      ·
                        rfl

theorem cell23_2730557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_2730557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730557 prefixEnd_2730557 := by exact prefixLift 2730557
  have htrace : WordTrace (prefixWord ++ tailWord_2730557) baseStart_2730557 baseEnd_2730557 := by
    simpa [prefixWord, tailWord_2730557, baseEnd_2730557] using wordTrace_append hprefix tailTrace_2730557
  have hstable : (prefixWord ++ tailWord_2730557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730557).length < 2 ^ (prefixWord ++ tailWord_2730557).sum := by decide
  have hdescent : baseEnd_2730557 < baseStart_2730557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730623 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 2, 9]
def baseStart_2730623 : Nat := 118140960795 + 2730623 * 2 ^ 59
def prefixEnd_2730623 : Nat := 4983230072969 + 3 ^ 40 * 2730623 * 2
def baseEnd_2730623 : Nat := 467374028407391719551533

theorem tailTrace_2730623 : CollatzResearch.WordTrace tailWord_2730623 prefixEnd_2730623 467374028407391719551533 := by
  unfold tailWord_2730623
  simp only [CollatzResearch.WordTrace]
  refine ⟨99594002786426699125228523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66396001857617799416819015 99594002786426699125228523)
  ·
    refine ⟨149391004179640048687842785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99594002786426699125228523 149391004179640048687842785)
    ·
      refine ⟨112043253134730036515882089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149391004179640048687842785 112043253134730036515882089)
      ·
        refine ⟨84032439851047527386911567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112043253134730036515882089 84032439851047527386911567)
        ·
          refine ⟨126048659776571291080367351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84032439851047527386911567 126048659776571291080367351)
          ·
            refine ⟨189072989664856936620551027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126048659776571291080367351 189072989664856936620551027)
            ·
              refine ⟨283609484497285404930826541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189072989664856936620551027 283609484497285404930826541)
              ·
                refine ⟨106353556686482026849059953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 283609484497285404930826541 106353556686482026849059953)
                ·
                  refine ⟨79765167514861520136794965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106353556686482026849059953 79765167514861520136794965)
                  ·
                    refine ⟨467374028407391719551533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 79765167514861520136794965 467374028407391719551533)
                    ·
                      rfl

theorem cell23_2730623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 9].length) (baseStart_2730623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730623 prefixEnd_2730623 := by exact prefixLift 2730623
  have htrace : WordTrace (prefixWord ++ tailWord_2730623) baseStart_2730623 baseEnd_2730623 := by
    simpa [prefixWord, tailWord_2730623, baseEnd_2730623] using wordTrace_append hprefix tailTrace_2730623
  have hstable : (prefixWord ++ tailWord_2730623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730623).length < 2 ^ (prefixWord ++ tailWord_2730623).sum := by decide
  have hdescent : baseEnd_2730623 < baseStart_2730623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730647 : List Nat := [1, 1, 3, 3, 2, 1, 1, 3, 1, 5, 2]
def baseStart_2730647 : Nat := 118140960795 + 2730647 * 2 ^ 59
def prefixEnd_2730647 : Nat := 4983230072969 + 3 ^ 40 * 2730647 * 2
def baseEnd_2730647 : Nat := 1402134408757883064754489

theorem tailTrace_2730647 : CollatzResearch.WordTrace tailWord_2730647 prefixEnd_2730647 1402134408757883064754489 := by
  unfold tailWord_2730647
  simp only [CollatzResearch.WordTrace]
  refine ⟨99594878138339751224102195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66396585425559834149401463 99594878138339751224102195)
  ·
    refine ⟨149392317207509626836153293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99594878138339751224102195 149392317207509626836153293)
    ·
      refine ⟨56022118952816110063557485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149392317207509626836153293 56022118952816110063557485)
      ·
        refine ⟨21008294607306041273834057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56022118952816110063557485 21008294607306041273834057)
        ·
          refine ⟨15756220955479530955375543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21008294607306041273834057 15756220955479530955375543)
          ·
            refine ⟨23634331433219296433063315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15756220955479530955375543 23634331433219296433063315)
            ·
              refine ⟨35451497149828944649594973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23634331433219296433063315 35451497149828944649594973)
              ·
                refine ⟨13294311431185854243598115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35451497149828944649594973 13294311431185854243598115)
                ·
                  refine ⟨19941467146778781365397173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13294311431185854243598115 19941467146778781365397173)
                  ·
                    refine ⟨1869512545010510753005985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19941467146778781365397173 1869512545010510753005985)
                    ·
                      refine ⟨1402134408757883064754489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1869512545010510753005985 1402134408757883064754489)
                      ·
                        rfl

theorem cell23_2730647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_2730647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730647 prefixEnd_2730647 := by exact prefixLift 2730647
  have htrace : WordTrace (prefixWord ++ tailWord_2730647) baseStart_2730647 baseEnd_2730647 := by
    simpa [prefixWord, tailWord_2730647, baseEnd_2730647] using wordTrace_append hprefix tailTrace_2730647
  have hstable : (prefixWord ++ tailWord_2730647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730647).length < 2 ^ (prefixWord ++ tailWord_2730647).sum := by decide
  have hdescent : baseEnd_2730647 < baseStart_2730647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730678 : List Nat := [5, 1, 3, 1, 2, 2, 2, 1, 6]
def baseStart_2730678 : Nat := 118140960795 + 2730678 * 2 ^ 59
def prefixEnd_2730678 : Nat := 4983230072969 + 3 ^ 40 * 2730678 * 2
def baseEnd_2730678 : Nat := 155794480739796938162983

theorem tailTrace_2730678 : CollatzResearch.WordTrace tailWord_2730678 prefixEnd_2730678 155794480739796938162983 := by
  unfold tailWord_2730678
  simp only [CollatzResearch.WordTrace]
  refine ⟨6224750550076715219905043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66397339200818295678987125 6224750550076715219905043)
  ·
    refine ⟨9337125825115072829857565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6224750550076715219905043 9337125825115072829857565)
    ·
      refine ⟨3501422184418152311196587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9337125825115072829857565 3501422184418152311196587)
      ·
        refine ⟨5252133276627228466794881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3501422184418152311196587 5252133276627228466794881)
        ·
          refine ⟨3939099957470421350096161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5252133276627228466794881 3939099957470421350096161)
          ·
            refine ⟨2954324968102816012572121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3939099957470421350096161 2954324968102816012572121)
            ·
              refine ⟨2215743726077112009429091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2954324968102816012572121 2215743726077112009429091)
              ·
                refine ⟨3323615589115668014143637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2215743726077112009429091 3323615589115668014143637)
                ·
                  refine ⟨155794480739796938162983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3323615589115668014143637 155794480739796938162983)
                  ·
                    rfl

theorem cell23_2730678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_2730678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730678 prefixEnd_2730678 := by exact prefixLift 2730678
  have htrace : WordTrace (prefixWord ++ tailWord_2730678) baseStart_2730678 baseEnd_2730678 := by
    simpa [prefixWord, tailWord_2730678, baseEnd_2730678] using wordTrace_append hprefix tailTrace_2730678
  have hstable : (prefixWord ++ tailWord_2730678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730678).length < 2 ^ (prefixWord ++ tailWord_2730678).sum := by decide
  have hdescent : baseEnd_2730678 < baseStart_2730678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730680 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 1, 8, 3]
def baseStart_2730680 : Nat := 118140960795 + 2730680 * 2 ^ 59
def prefixEnd_2730680 : Nat := 4983230072969 + 3 ^ 40 * 2730680 * 2
def baseEnd_2730680 : Nat := 1402151353619481435641837

theorem tailTrace_2730680 : CollatzResearch.WordTrace tailWord_2730680 prefixEnd_2730680 1402151353619481435641837 := by
  unfold tailWord_2730680
  simp only [CollatzResearch.WordTrace]
  refine ⟨49798040873610098930026747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66397387831480131906702329 49798040873610098930026747)
  ·
    refine ⟨74697061310415148395040121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49798040873610098930026747 74697061310415148395040121)
    ·
      refine ⟨56022795982811361296280091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74697061310415148395040121 56022795982811361296280091)
      ·
        refine ⟨84034193974217041944420137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56022795982811361296280091 84034193974217041944420137)
        ·
          refine ⟨63025645480662781458315103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84034193974217041944420137 63025645480662781458315103)
          ·
            refine ⟨94538468220994172187472655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63025645480662781458315103 94538468220994172187472655)
            ·
              refine ⟨141807702331491258281208983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94538468220994172187472655 141807702331491258281208983)
              ·
                refine ⟨212711553497236887421813475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141807702331491258281208983 212711553497236887421813475)
                ·
                  refine ⟨319067330245855331132720213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212711553497236887421813475 319067330245855331132720213)
                  ·
                    refine ⟨3739070276318617161711565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 319067330245855331132720213 3739070276318617161711565)
                    ·
                      refine ⟨1402151353619481435641837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3739070276318617161711565 1402151353619481435641837)
                      ·
                        rfl

theorem cell23_2730680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 8, 3].length) (baseStart_2730680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730680 prefixEnd_2730680 := by exact prefixLift 2730680
  have htrace : WordTrace (prefixWord ++ tailWord_2730680) baseStart_2730680 baseEnd_2730680 := by
    simpa [prefixWord, tailWord_2730680, baseEnd_2730680] using wordTrace_append hprefix tailTrace_2730680
  have hstable : (prefixWord ++ tailWord_2730680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730680).length < 2 ^ (prefixWord ++ tailWord_2730680).sum := by decide
  have hdescent : baseEnd_2730680 < baseStart_2730680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730744 : List Nat := [2, 1, 2, 1, 1, 2, 3, 5, 2, 1, 3]
def baseStart_2730744 : Nat := 118140960795 + 2730744 * 2 ^ 59
def prefixEnd_2730744 : Nat := 4983230072969 + 3 ^ 40 * 2730744 * 2
def baseEnd_2730744 : Nat := 1402184216381369185241543

theorem tailTrace_2730744 : CollatzResearch.WordTrace tailWord_2730744 prefixEnd_2730744 1402184216381369185241543 := by
  unfold tailWord_2730744
  simp only [CollatzResearch.WordTrace]
  refine ⟨49799208009494168395191643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66398944012658891193588857 49799208009494168395191643)
  ·
    refine ⟨74698812014241252592787465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49799208009494168395191643 74698812014241252592787465)
    ·
      refine ⟨56024109010680939444590599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74698812014241252592787465 56024109010680939444590599)
      ·
        refine ⟨84036163516021409166885899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56024109010680939444590599 84036163516021409166885899)
        ·
          refine ⟨126054245274032113750328849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84036163516021409166885899 126054245274032113750328849)
          ·
            refine ⟨94540683955524085312746637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126054245274032113750328849 94540683955524085312746637)
            ·
              refine ⟨35452756483321531992279989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94540683955524085312746637 35452756483321531992279989)
              ·
                refine ⟨3323695920311393624276249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35452756483321531992279989 3323695920311393624276249)
                ·
                  refine ⟨2492771940233545218207187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3323695920311393624276249 2492771940233545218207187)
                  ·
                    refine ⟨3739157910350317827310781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2492771940233545218207187 3739157910350317827310781)
                    ·
                      refine ⟨1402184216381369185241543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3739157910350317827310781 1402184216381369185241543)
                      ·
                        rfl

theorem cell23_2730744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 2, 1, 3].length) (baseStart_2730744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730744 prefixEnd_2730744 := by exact prefixLift 2730744
  have htrace : WordTrace (prefixWord ++ tailWord_2730744) baseStart_2730744 baseEnd_2730744 := by
    simpa [prefixWord, tailWord_2730744, baseEnd_2730744] using wordTrace_append hprefix tailTrace_2730744
  have hstable : (prefixWord ++ tailWord_2730744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730744).length < 2 ^ (prefixWord ++ tailWord_2730744).sum := by decide
  have hdescent : baseEnd_2730744 < baseStart_2730744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730800 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 9]
def baseStart_2730800 : Nat := 118140960795 + 2730800 * 2 ^ 59
def prefixEnd_2730800 : Nat := 4983230072969 + 3 ^ 40 * 2730800 * 2
def baseEnd_2730800 : Nat := 1402212971298020966141285

theorem tailTrace_2730800 : CollatzResearch.WordTrace tailWord_2730800 prefixEnd_2730800 1402212971298020966141285 := by
  unfold tailWord_2730800
  simp only [CollatzResearch.WordTrace]
  refine ⟨49800229253392729177210927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66400305671190305569614569 49800229253392729177210927)
  ·
    refine ⟨74700343880089093765816391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49800229253392729177210927 74700343880089093765816391)
    ·
      refine ⟨112050515820133640648724587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74700343880089093765816391 112050515820133640648724587)
      ·
        refine ⟨168075773730200460973086881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112050515820133640648724587 168075773730200460973086881)
        ·
          refine ⟨126056830297650345729815161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168075773730200460973086881 126056830297650345729815161)
          ·
            refine ⟨94542622723237759297361371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126056830297650345729815161 94542622723237759297361371)
            ·
              refine ⟨141813934084856638946042057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94542622723237759297361371 141813934084856638946042057)
              ·
                refine ⟨106360450563642479209531543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141813934084856638946042057 106360450563642479209531543)
                ·
                  refine ⟨159540675845463718814297315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106360450563642479209531543 159540675845463718814297315)
                  ·
                    refine ⟨239311013768195578221445973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 159540675845463718814297315 239311013768195578221445973)
                    ·
                      refine ⟨1402212971298020966141285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 239311013768195578221445973 1402212971298020966141285)
                      ·
                        rfl

theorem cell23_2730800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 9].length) (baseStart_2730800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730800 prefixEnd_2730800 := by exact prefixLift 2730800
  have htrace : WordTrace (prefixWord ++ tailWord_2730800) baseStart_2730800 baseEnd_2730800 := by
    simpa [prefixWord, tailWord_2730800, baseEnd_2730800] using wordTrace_append hprefix tailTrace_2730800
  have hstable : (prefixWord ++ tailWord_2730800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730800).length < 2 ^ (prefixWord ++ tailWord_2730800).sum := by decide
  have hdescent : baseEnd_2730800 < baseStart_2730800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730841 : List Nat := [1, 2, 1, 2, 2, 5, 3, 2, 5]
def baseStart_2730841 : Nat := 118140960795 + 2730841 * 2 ^ 59
def prefixEnd_2730841 : Nat := 4983230072969 + 3 ^ 40 * 2730841 * 2
def baseEnd_2730841 : Nat := 155803780444983922858733

theorem tailTrace_2730841 : CollatzResearch.WordTrace tailWord_2730841 prefixEnd_2730841 155803780444983922858733 := by
  unfold tailWord_2730841
  simp only [CollatzResearch.WordTrace]
  refine ⟨99601953899636922356664377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66401302599757948237776251 99601953899636922356664377)
  ·
    refine ⟨74701465424727691767498283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99601953899636922356664377 74701465424727691767498283)
    ·
      refine ⟨112052198137091537651247425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74701465424727691767498283 112052198137091537651247425)
      ·
        refine ⟨84039148602818653238435569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112052198137091537651247425 84039148602818653238435569)
        ·
          refine ⟨63029361452113989928826677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84039148602818653238435569 63029361452113989928826677)
          ·
            refine ⟨5909002636135686555827501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63029361452113989928826677 5909002636135686555827501)
            ·
              refine ⟨2215875988550882458435313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5909002636135686555827501 2215875988550882458435313)
              ·
                refine ⟨1661906991413161843826485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2215875988550882458435313 1661906991413161843826485)
                ·
                  refine ⟨155803780444983922858733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1661906991413161843826485 155803780444983922858733)
                  ·
                    rfl

theorem cell23_2730841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2, 5].length) (baseStart_2730841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730841 prefixEnd_2730841 := by exact prefixLift 2730841
  have htrace : WordTrace (prefixWord ++ tailWord_2730841) baseStart_2730841 baseEnd_2730841 := by
    simpa [prefixWord, tailWord_2730841, baseEnd_2730841] using wordTrace_append hprefix tailTrace_2730841
  have hstable : (prefixWord ++ tailWord_2730841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730841).length < 2 ^ (prefixWord ++ tailWord_2730841).sum := by decide
  have hdescent : baseEnd_2730841 < baseStart_2730841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730847 : List Nat := [1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 5]
def baseStart_2730847 : Nat := 118140960795 + 2730847 * 2 ^ 59
def prefixEnd_2730847 : Nat := 4983230072969 + 3 ^ 40 * 2730847 * 2
def baseEnd_2730847 : Nat := 1402237104888782282253569

theorem tailTrace_2730847 : CollatzResearch.WordTrace tailWord_2730847 prefixEnd_2730847 1402237104888782282253569 := by
  unfold tailWord_2730847
  simp only [CollatzResearch.WordTrace]
  refine ⟨99602172737615185381382795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66401448491743456920921863 99602172737615185381382795)
  ·
    refine ⟨149403259106422778072074193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99602172737615185381382795 149403259106422778072074193)
    ·
      refine ⟨112052444329817083554055645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149403259106422778072074193 112052444329817083554055645)
      ·
        refine ⟨42019666623681406332770867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112052444329817083554055645 42019666623681406332770867)
        ·
          refine ⟨63029499935522109499156301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42019666623681406332770867 63029499935522109499156301)
          ·
            refine ⟨23636062475820791062183613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63029499935522109499156301 23636062475820791062183613)
            ·
              refine ⟨8863523428432796648318855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23636062475820791062183613 8863523428432796648318855)
              ·
                refine ⟨13295285142649194972478283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8863523428432796648318855 13295285142649194972478283)
                ·
                  refine ⟨19942927713973792458717425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13295285142649194972478283 19942927713973792458717425)
                  ·
                    refine ⟨14957195785480344344038069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19942927713973792458717425 14957195785480344344038069)
                    ·
                      refine ⟨1402237104888782282253569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14957195785480344344038069 1402237104888782282253569)
                      ·
                        rfl

theorem cell23_2730847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_2730847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730847 prefixEnd_2730847 := by exact prefixLift 2730847
  have htrace : WordTrace (prefixWord ++ tailWord_2730847) baseStart_2730847 baseEnd_2730847 := by
    simpa [prefixWord, tailWord_2730847, baseEnd_2730847] using wordTrace_append hprefix tailTrace_2730847
  have hstable : (prefixWord ++ tailWord_2730847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730847).length < 2 ^ (prefixWord ++ tailWord_2730847).sum := by decide
  have hdescent : baseEnd_2730847 < baseStart_2730847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730874 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2]
def baseStart_2730874 : Nat := 118140960795 + 2730874 * 2 ^ 59
def prefixEnd_2730874 : Nat := 4983230072969 + 3 ^ 40 * 2730874 * 2
def baseEnd_2730874 : Nat := 1402250968866453676615945

theorem tailTrace_2730874 : CollatzResearch.WordTrace tailWord_2730874 prefixEnd_2730874 1402250968866453676615945 := by
  unfold tailWord_2730874
  simp only [CollatzResearch.WordTrace]
  refine ⟨24900789377129342248153919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66402105005678245995077117 24900789377129342248153919)
  ·
    refine ⟨37351184065694013372230879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24900789377129342248153919 37351184065694013372230879)
    ·
      refine ⟨56026776098541020058346319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37351184065694013372230879 56026776098541020058346319)
      ·
        refine ⟨84040164147811530087519479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56026776098541020058346319 84040164147811530087519479)
        ·
          refine ⟨126060246221717295131279219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84040164147811530087519479 126060246221717295131279219)
          ·
            refine ⟨189090369332575942696918829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126060246221717295131279219 189090369332575942696918829)
            ·
              refine ⟨70908888499715978511344561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189090369332575942696918829 70908888499715978511344561)
              ·
                refine ⟨53181666374786983883508421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70908888499715978511344561 53181666374786983883508421)
                ·
                  refine ⟨9971562445272559478157829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53181666374786983883508421 9971562445272559478157829)
                  ·
                    refine ⟨1869667958488604902154593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9971562445272559478157829 1869667958488604902154593)
                    ·
                      refine ⟨1402250968866453676615945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1869667958488604902154593 1402250968866453676615945)
                      ·
                        rfl

theorem cell23_2730874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2].length) (baseStart_2730874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730874 prefixEnd_2730874 := by exact prefixLift 2730874
  have htrace : WordTrace (prefixWord ++ tailWord_2730874) baseStart_2730874 baseEnd_2730874 := by
    simpa [prefixWord, tailWord_2730874, baseEnd_2730874] using wordTrace_append hprefix tailTrace_2730874
  have hstable : (prefixWord ++ tailWord_2730874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730874).length < 2 ^ (prefixWord ++ tailWord_2730874).sum := by decide
  have hdescent : baseEnd_2730874 < baseStart_2730874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730908 : List Nat := [2, 2, 3, 3, 2, 1, 1, 1, 2, 4, 2]
def baseStart_2730908 : Nat := 118140960795 + 2730908 * 2 ^ 59
def prefixEnd_2730908 : Nat := 4983230072969 + 3 ^ 40 * 2730908 * 2
def baseEnd_2730908 : Nat := 1402268427208706543590789

theorem tailTrace_2730908 : CollatzResearch.WordTrace tailWord_2730908 prefixEnd_2730908 1402268427208706543590789 := by
  unfold tailWord_2730908
  simp only [CollatzResearch.WordTrace]
  refine ⟨49802198795197096399676689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66402931726929461866235585 49802198795197096399676689)
  ·
    refine ⟨37351649096397822299757517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49802198795197096399676689 37351649096397822299757517)
    ·
      refine ⟨14006868411149183362409069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37351649096397822299757517 14006868411149183362409069)
      ·
        refine ⟨5252575654180943760903401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14006868411149183362409069 5252575654180943760903401)
        ·
          refine ⟨3939431740635707820677551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5252575654180943760903401 3939431740635707820677551)
          ·
            refine ⟨5909147610953561731016327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3939431740635707820677551 5909147610953561731016327)
            ·
              refine ⟨8863721416430342596524491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5909147610953561731016327 8863721416430342596524491)
              ·
                refine ⟨13295582124645513894786737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8863721416430342596524491 13295582124645513894786737)
                ·
                  refine ⟨9971686593484135421090053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13295582124645513894786737 9971686593484135421090053)
                  ·
                    refine ⟨1869691236278275391454385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9971686593484135421090053 1869691236278275391454385)
                    ·
                      refine ⟨1402268427208706543590789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1869691236278275391454385 1402268427208706543590789)
                      ·
                        rfl

theorem cell23_2730908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_2730908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730908 prefixEnd_2730908 := by exact prefixLift 2730908
  have htrace : WordTrace (prefixWord ++ tailWord_2730908) baseStart_2730908 baseEnd_2730908 := by
    simpa [prefixWord, tailWord_2730908, baseEnd_2730908] using wordTrace_append hprefix tailTrace_2730908
  have hstable : (prefixWord ++ tailWord_2730908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730908).length < 2 ^ (prefixWord ++ tailWord_2730908).sum := by decide
  have hdescent : baseEnd_2730908 < baseStart_2730908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730925 : List Nat := [1, 5, 2, 3, 1, 2, 1, 1, 2, 1, 4]
def baseStart_2730925 : Nat := 118140960795 + 2730925 * 2 ^ 59
def prefixEnd_2730925 : Nat := 4983230072969 + 3 ^ 40 * 2730925 * 2
def baseEnd_2730925 : Nat := 1402277156379832977078211

theorem tailTrace_2730925 : CollatzResearch.WordTrace tailWord_2730925 prefixEnd_2730925 1402277156379832977078211 := by
  unfold tailWord_2730925
  simp only [CollatzResearch.WordTrace]
  refine ⟨99605017631332604702722229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66403345087555069801814819 99605017631332604702722229)
  ·
    refine ⟨9337970402937431690880209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99605017631332604702722229 9337970402937431690880209)
    ·
      refine ⟨7003477802203073768160157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9337970402937431690880209 7003477802203073768160157)
      ·
        refine ⟨2626304175826152663060059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7003477802203073768160157 2626304175826152663060059)
        ·
          refine ⟨3939456263739228994590089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2626304175826152663060059 3939456263739228994590089)
          ·
            refine ⟨2954592197804421745942567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3939456263739228994590089 2954592197804421745942567)
            ·
              refine ⟨4431888296706632618913851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2954592197804421745942567 4431888296706632618913851)
              ·
                refine ⟨6647832445059948928370777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4431888296706632618913851 6647832445059948928370777)
                ·
                  refine ⟨4985874333794961696278083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6647832445059948928370777 4985874333794961696278083)
                  ·
                    refine ⟨7478811500692442544417125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4985874333794961696278083 7478811500692442544417125)
                    ·
                      refine ⟨1402277156379832977078211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7478811500692442544417125 1402277156379832977078211)
                      ·
                        rfl

theorem cell23_2730925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_2730925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730925 prefixEnd_2730925 := by exact prefixLift 2730925
  have htrace : WordTrace (prefixWord ++ tailWord_2730925) baseStart_2730925 baseEnd_2730925 := by
    simpa [prefixWord, tailWord_2730925, baseEnd_2730925] using wordTrace_append hprefix tailTrace_2730925
  have hstable : (prefixWord ++ tailWord_2730925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730925).length < 2 ^ (prefixWord ++ tailWord_2730925).sum := by decide
  have hdescent : baseEnd_2730925 < baseStart_2730925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730951 : List Nat := [1, 1, 4, 1, 1, 2, 2, 4, 2, 3, 2]
def baseStart_2730951 : Nat := 118140960795 + 2730951 * 2 ^ 59
def prefixEnd_2730951 : Nat := 4983230072969 + 3 ^ 40 * 2730951 * 2
def baseEnd_2730951 : Nat := 1402290506876849875353091

theorem tailTrace_2730951 : CollatzResearch.WordTrace tailWord_2730951 prefixEnd_2730951 1402290506876849875353091 := by
  unfold tailWord_2730951
  simp only [CollatzResearch.WordTrace]
  refine ⟨99605965929238411143168707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66403977286158940762112471 99605965929238411143168707)
  ·
    refine ⟨149408948893857616714753061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99605965929238411143168707 149408948893857616714753061)
    ·
      refine ⟨28014177917598303134016199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149408948893857616714753061 28014177917598303134016199)
      ·
        refine ⟨42021266876397454701024299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28014177917598303134016199 42021266876397454701024299)
        ·
          refine ⟨63031900314596182051536449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42021266876397454701024299 63031900314596182051536449)
          ·
            refine ⟨47273925235947136538652337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63031900314596182051536449 47273925235947136538652337)
            ·
              refine ⟨35455443926960352403989253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47273925235947136538652337 35455443926960352403989253)
              ·
                refine ⟨6647895736305066075747985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35455443926960352403989253 6647895736305066075747985)
                ·
                  refine ⟨4985921802228799556810989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6647895736305066075747985 4985921802228799556810989)
                  ·
                    refine ⟨1869720675835799833804121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4985921802228799556810989 1869720675835799833804121)
                    ·
                      refine ⟨1402290506876849875353091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1869720675835799833804121 1402290506876849875353091)
                      ·
                        rfl

theorem cell23_2730951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 3, 2].length) (baseStart_2730951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730951 prefixEnd_2730951 := by exact prefixLift 2730951
  have htrace : WordTrace (prefixWord ++ tailWord_2730951) baseStart_2730951 baseEnd_2730951 := by
    simpa [prefixWord, tailWord_2730951, baseEnd_2730951] using wordTrace_append hprefix tailTrace_2730951
  have hstable : (prefixWord ++ tailWord_2730951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730951).length < 2 ^ (prefixWord ++ tailWord_2730951).sum := by decide
  have hdescent : baseEnd_2730951 < baseStart_2730951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730958 : List Nat := [4, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3]
def baseStart_2730958 : Nat := 118140960795 + 2730958 * 2 ^ 59
def prefixEnd_2730958 : Nat := 4983230072969 + 3 ^ 40 * 2730958 * 2
def baseEnd_2730958 : Nat := 1402294101241431347965559

theorem tailTrace_2730958 : CollatzResearch.WordTrace tailWord_2730958 prefixEnd_2730958 1402294101241431347965559 := by
  unfold tailWord_2730958
  simp only [CollatzResearch.WordTrace]
  refine ⟨12450777655026631417334191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66404147493475367559115685 12450777655026631417334191)
  ·
    refine ⟨18676166482539947126001287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12450777655026631417334191 18676166482539947126001287)
    ·
      refine ⟨28014249723809920689001931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18676166482539947126001287 28014249723809920689001931)
      ·
        refine ⟨42021374585714881033502897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28014249723809920689001931 42021374585714881033502897)
        ·
          refine ⟨31516030939286160775127173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42021374585714881033502897 31516030939286160775127173)
          ·
            refine ⟨5909255801116155145336345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31516030939286160775127173 5909255801116155145336345)
            ·
              refine ⟨4431941850837116359002259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5909255801116155145336345 4431941850837116359002259)
              ·
                refine ⟨6647912776255674538503389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4431941850837116359002259 6647912776255674538503389)
                ·
                  refine ⟨2492967291095877951938771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6647912776255674538503389 2492967291095877951938771)
                  ·
                    refine ⟨3739450936643816927908157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2492967291095877951938771 3739450936643816927908157)
                    ·
                      refine ⟨1402294101241431347965559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3739450936643816927908157 1402294101241431347965559)
                      ·
                        rfl

theorem cell23_2730958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_2730958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730958 prefixEnd_2730958 := by exact prefixLift 2730958
  have htrace : WordTrace (prefixWord ++ tailWord_2730958) baseStart_2730958 baseEnd_2730958 := by
    simpa [prefixWord, tailWord_2730958, baseEnd_2730958] using wordTrace_append hprefix tailTrace_2730958
  have hstable : (prefixWord ++ tailWord_2730958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730958).length < 2 ^ (prefixWord ++ tailWord_2730958).sum := by decide
  have hdescent : baseEnd_2730958 < baseStart_2730958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730978 : List Nat := [3, 3, 3, 1, 1, 1, 1, 4, 1, 5]
def baseStart_2730978 : Nat := 118140960795 + 2730978 * 2 ^ 59
def prefixEnd_2730978 : Nat := 4983230072969 + 3 ^ 40 * 2730978 * 2
def baseEnd_2730978 : Nat := 467434790284840423238489

theorem tailTrace_2730978 : CollatzResearch.WordTrace tailWord_2730978 prefixEnd_2730978 467434790284840423238489 := by
  unfold tailWord_2730978
  simp only [CollatzResearch.WordTrace]
  refine ⟨24901737675035148688600397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66404633800093729836267725 24901737675035148688600397)
  ·
    refine ⟨9338151628138180758225149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24901737675035148688600397 9338151628138180758225149)
    ·
      refine ⟨3501806860551817784334431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9338151628138180758225149 3501806860551817784334431)
      ·
        refine ⟨5252710290827726676501647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3501806860551817784334431 5252710290827726676501647)
        ·
          refine ⟨7879065436241590014752471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5252710290827726676501647 7879065436241590014752471)
          ·
            refine ⟨11818598154362385022128707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7879065436241590014752471 11818598154362385022128707)
            ·
              refine ⟨17727897231543577533193061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11818598154362385022128707 17727897231543577533193061)
              ·
                refine ⟨3323980730914420787473699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17727897231543577533193061 3323980730914420787473699)
                ·
                  refine ⟨4985971096371631181210549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3323980730914420787473699 4985971096371631181210549)
                  ·
                    refine ⟨467434790284840423238489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4985971096371631181210549 467434790284840423238489)
                    ·
                      rfl

theorem cell23_2730978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_2730978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730978 prefixEnd_2730978 := by exact prefixLift 2730978
  have htrace : WordTrace (prefixWord ++ tailWord_2730978) baseStart_2730978 baseEnd_2730978 := by
    simpa [prefixWord, tailWord_2730978, baseEnd_2730978] using wordTrace_append hprefix tailTrace_2730978
  have hstable : (prefixWord ++ tailWord_2730978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730978).length < 2 ^ (prefixWord ++ tailWord_2730978).sum := by decide
  have hdescent : baseEnd_2730978 < baseStart_2730978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730998 : List Nat := [5, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4]
def baseStart_2730998 : Nat := 118140960795 + 2730998 * 2 ^ 59
def prefixEnd_2730998 : Nat := 4983230072969 + 3 ^ 40 * 2730998 * 2
def baseEnd_2730998 : Nat := 1402314640467611191465375

theorem tailTrace_2730998 : CollatzResearch.WordTrace tailWord_2730998 prefixEnd_2730998 1402314640467611191465375 := by
  unfold tailWord_2730998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6225480010004258635633103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66405120106712092113419765 6225480010004258635633103)
  ·
    refine ⟨9338220015006387953449655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6225480010004258635633103 9338220015006387953449655)
    ·
      refine ⟨14007330022509581930174483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9338220015006387953449655 14007330022509581930174483)
      ·
        refine ⟨21010995033764372895261725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14007330022509581930174483 21010995033764372895261725)
        ·
          refine ⟨7879123137661639835723147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21010995033764372895261725 7879123137661639835723147)
          ·
            refine ⟨11818684706492459753584721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7879123137661639835723147 11818684706492459753584721)
            ·
              refine ⟨8864013529869344815188541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11818684706492459753584721 8864013529869344815188541)
              ·
                refine ⟨3324005073701004305695703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8864013529869344815188541 3324005073701004305695703)
                ·
                  refine ⟨4986007610551506458543555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3324005073701004305695703 4986007610551506458543555)
                  ·
                    refine ⟨7479011415827259687815333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4986007610551506458543555 7479011415827259687815333)
                    ·
                      refine ⟨1402314640467611191465375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7479011415827259687815333 1402314640467611191465375)
                      ·
                        rfl

theorem cell23_2730998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_2730998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2730998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2730998 prefixEnd_2730998 := by exact prefixLift 2730998
  have htrace : WordTrace (prefixWord ++ tailWord_2730998) baseStart_2730998 baseEnd_2730998 := by
    simpa [prefixWord, tailWord_2730998, baseEnd_2730998] using wordTrace_append hprefix tailTrace_2730998
  have hstable : (prefixWord ++ tailWord_2730998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730998).length < 2 ^ (prefixWord ++ tailWord_2730998).sum := by decide
  have hdescent : baseEnd_2730998 < baseStart_2730998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731001 : List Nat := [1, 2, 1, 3, 1, 3, 1, 5, 1, 2, 3]
def baseStart_2731001 : Nat := 118140960795 + 2731001 * 2 ^ 59
def prefixEnd_2731001 : Nat := 4983230072969 + 3 ^ 40 * 2731001 * 2
def baseEnd_2731001 : Nat := 1402316180909574679727861

theorem tailTrace_2731001 : CollatzResearch.WordTrace tailWord_2731001 prefixEnd_2731001 1402316180909574679727861 := by
  unfold tailWord_2731001
  simp only [CollatzResearch.WordTrace]
  refine ⟨99607789579057269682488857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66405193052704846454992571 99607789579057269682488857)
  ·
    refine ⟨74705842184292952261866643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99607789579057269682488857 74705842184292952261866643)
    ·
      refine ⟨112058763276439428392799965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74705842184292952261866643 112058763276439428392799965)
      ·
        refine ⟨42022036228664785647299987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112058763276439428392799965 42022036228664785647299987)
        ·
          refine ⟨63033054342997178470949981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42022036228664785647299987 63033054342997178470949981)
          ·
            refine ⟨23637395378623941926606243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63033054342997178470949981 23637395378623941926606243)
            ·
              refine ⟨35456093067935912889909365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23637395378623941926606243 35456093067935912889909365)
              ·
                refine ⟨3324008725118991833429003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35456093067935912889909365 3324008725118991833429003)
                ·
                  refine ⟨4986013087678487750143505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3324008725118991833429003 4986013087678487750143505)
                  ·
                    refine ⟨3739509815758865812607629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4986013087678487750143505 3739509815758865812607629)
                    ·
                      refine ⟨1402316180909574679727861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3739509815758865812607629 1402316180909574679727861)
                      ·
                        rfl

theorem cell23_2731001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_2731001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731001 prefixEnd_2731001 := by exact prefixLift 2731001
  have htrace : WordTrace (prefixWord ++ tailWord_2731001) baseStart_2731001 baseEnd_2731001 := by
    simpa [prefixWord, tailWord_2731001, baseEnd_2731001] using wordTrace_append hprefix tailTrace_2731001
  have hstable : (prefixWord ++ tailWord_2731001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731001).length < 2 ^ (prefixWord ++ tailWord_2731001).sum := by decide
  have hdescent : baseEnd_2731001 < baseStart_2731001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731004 : List Nat := [2, 2, 2, 1, 2, 5, 9]
def baseStart_2731004 : Nat := 118140960795 + 2731004 * 2 ^ 59
def prefixEnd_2731004 : Nat := 4983230072969 + 3 ^ 40 * 2731004 * 2
def baseEnd_2731004 : Nat := 17312564461130100839387

theorem tailTrace_2731004 : CollatzResearch.WordTrace tailWord_2731004 prefixEnd_2731004 17312564461130100839387 := by
  unfold tailWord_2731004
  simp only [CollatzResearch.WordTrace]
  refine ⟨49803949499023200597424033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66405265998697600796565377 49803949499023200597424033)
  ·
    refine ⟨37352962124267400448068025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49803949499023200597424033 37352962124267400448068025)
    ·
      refine ⟨28014721593200550336051019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37352962124267400448068025 28014721593200550336051019)
      ·
        refine ⟨42022082389800825504076529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28014721593200550336051019 42022082389800825504076529)
        ·
          refine ⟨31516561792350619128057397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42022082389800825504076529 31516561792350619128057397)
          ·
            refine ⟨2954677668032870543255381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31516561792350619128057397 2954677668032870543255381)
            ·
              refine ⟨17312564461130100839387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2954677668032870543255381 17312564461130100839387)
              ·
                rfl

theorem cell23_2731004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 9].length) (baseStart_2731004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731004 prefixEnd_2731004 := by exact prefixLift 2731004
  have htrace : WordTrace (prefixWord ++ tailWord_2731004) baseStart_2731004 baseEnd_2731004 := by
    simpa [prefixWord, tailWord_2731004, baseEnd_2731004] using wordTrace_append hprefix tailTrace_2731004
  have hstable : (prefixWord ++ tailWord_2731004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731004).length < 2 ^ (prefixWord ++ tailWord_2731004).sum := by decide
  have hdescent : baseEnd_2731004 < baseStart_2731004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731065 : List Nat := [1, 2, 1, 5, 2, 2, 2, 2, 2, 1, 3]
def baseStart_2731065 : Nat := 118140960795 + 2731065 * 2 ^ 59
def prefixEnd_2731065 : Nat := 4983230072969 + 3 ^ 40 * 2731065 * 2
def baseEnd_2731065 : Nat := 1402349043671462429327567

theorem tailTrace_2731065 : CollatzResearch.WordTrace tailWord_2731065 prefixEnd_2731065 1402349043671462429327567 := by
  unfold tailWord_2731065
  simp only [CollatzResearch.WordTrace]
  refine ⟨99610123850825408612818649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66406749233883605741879099 99610123850825408612818649)
  ·
    refine ⟨74707592888119056459613987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99610123850825408612818649 74707592888119056459613987)
    ·
      refine ⟨112061389332178584689420981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74707592888119056459613987 112061389332178584689420981)
      ·
        refine ⟨10505755249891742314633217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112061389332178584689420981 10505755249891742314633217)
        ·
          refine ⟨7879316437418806735974913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10505755249891742314633217 7879316437418806735974913)
          ·
            refine ⟨5909487328064105051981185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7879316437418806735974913 5909487328064105051981185)
            ·
              refine ⟨4432115496048078788985889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5909487328064105051981185 4432115496048078788985889)
              ·
                refine ⟨3324086622036059091739417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4432115496048078788985889 3324086622036059091739417)
                ·
                  refine ⟨2493064966527044318804563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3324086622036059091739417 2493064966527044318804563)
                  ·
                    refine ⟨3739597449790566478206845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2493064966527044318804563 3739597449790566478206845)
                    ·
                      refine ⟨1402349043671462429327567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3739597449790566478206845 1402349043671462429327567)
                      ·
                        rfl

theorem cell23_2731065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_2731065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731065 prefixEnd_2731065 := by exact prefixLift 2731065
  have htrace : WordTrace (prefixWord ++ tailWord_2731065) baseStart_2731065 baseEnd_2731065 := by
    simpa [prefixWord, tailWord_2731065, baseEnd_2731065] using wordTrace_append hprefix tailTrace_2731065
  have hstable : (prefixWord ++ tailWord_2731065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731065).length < 2 ^ (prefixWord ++ tailWord_2731065).sum := by decide
  have hdescent : baseEnd_2731065 < baseStart_2731065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731071 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 5, 4, 2]
def baseStart_2731071 : Nat := 118140960795 + 2731071 * 2 ^ 59
def prefixEnd_2731071 : Nat := 4983230072969 + 3 ^ 40 * 2731071 * 2
def baseEnd_2731071 : Nat := 1402352124555389405852539

theorem tailTrace_2731071 : CollatzResearch.WordTrace tailWord_2731071 prefixEnd_2731071 1402352124555389405852539 := by
  unfold tailWord_2731071
  simp only [CollatzResearch.WordTrace]
  refine ⟨99610342688803671637537067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66406895125869114425024711 99610342688803671637537067)
  ·
    refine ⟨149415514033205507456305601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99610342688803671637537067 149415514033205507456305601)
    ·
      refine ⟨112061635524904130592229201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149415514033205507456305601 112061635524904130592229201)
      ·
        refine ⟨84046226643678097944171901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112061635524904130592229201 84046226643678097944171901)
        ·
          refine ⟨31517334991379286729064463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84046226643678097944171901 31517334991379286729064463)
          ·
            refine ⟨47276002487068930093596695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31517334991379286729064463 47276002487068930093596695)
            ·
              refine ⟨70914003730603395140395043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47276002487068930093596695 70914003730603395140395043)
              ·
                refine ⟨106371005595905092710592565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70914003730603395140395043 106371005595905092710592565)
                ·
                  refine ⟨9972281774616102441618053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106371005595905092710592565 9972281774616102441618053)
                  ·
                    refine ⟨1869802832740519207803385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9972281774616102441618053 1869802832740519207803385)
                    ·
                      refine ⟨1402352124555389405852539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1869802832740519207803385 1402352124555389405852539)
                      ·
                        rfl

theorem cell23_2731071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 4, 2].length) (baseStart_2731071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731071 prefixEnd_2731071 := by exact prefixLift 2731071
  have htrace : WordTrace (prefixWord ++ tailWord_2731071) baseStart_2731071 baseEnd_2731071 := by
    simpa [prefixWord, tailWord_2731071, baseEnd_2731071] using wordTrace_append hprefix tailTrace_2731071
  have hstable : (prefixWord ++ tailWord_2731071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731071).length < 2 ^ (prefixWord ++ tailWord_2731071).sum := by decide
  have hdescent : baseEnd_2731071 < baseStart_2731071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731131 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 1, 7, 2]
def baseStart_2731131 : Nat := 118140960795 + 2731131 * 2 ^ 59
def prefixEnd_2731131 : Nat := 4983230072969 + 3 ^ 40 * 2731131 * 2
def baseEnd_2731131 : Nat := 1402382933394659171102263

theorem tailTrace_2731131 : CollatzResearch.WordTrace tailWord_2731131 prefixEnd_2731131 1402382933394659171102263 := by
  unfold tailWord_2731131
  simp only [CollatzResearch.WordTrace]
  refine ⟨99612531068586301884721247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66408354045724201256480831 99612531068586301884721247)
  ·
    refine ⟨149418796602879452827081871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99612531068586301884721247 149418796602879452827081871)
    ·
      refine ⟨224128194904319179240622807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149418796602879452827081871 224128194904319179240622807)
      ·
        refine ⟨336192292356478768860934211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224128194904319179240622807 336192292356478768860934211)
        ·
          refine ⟨504288438534718153291401317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336192292356478768860934211 504288438534718153291401317)
          ·
            refine ⟨94554082225259653742137747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 504288438534718153291401317 94554082225259653742137747)
            ·
              refine ⟨141831123337889480613206621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94554082225259653742137747 141831123337889480613206621)
              ·
                refine ⟨53186671251708555229952483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141831123337889480613206621 53186671251708555229952483)
                ·
                  refine ⟨79780006877562832844928725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53186671251708555229952483 79780006877562832844928725)
                  ·
                    refine ⟨1869843911192878894803017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 79780006877562832844928725 1869843911192878894803017)
                    ·
                      refine ⟨1402382933394659171102263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1869843911192878894803017 1402382933394659171102263)
                      ·
                        rfl

theorem cell23_2731131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 7, 2].length) (baseStart_2731131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731131 prefixEnd_2731131 := by exact prefixLift 2731131
  have htrace : WordTrace (prefixWord ++ tailWord_2731131) baseStart_2731131 baseEnd_2731131 := by
    simpa [prefixWord, tailWord_2731131, baseEnd_2731131] using wordTrace_append hprefix tailTrace_2731131
  have hstable : (prefixWord ++ tailWord_2731131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731131).length < 2 ^ (prefixWord ++ tailWord_2731131).sum := by decide
  have hdescent : baseEnd_2731131 < baseStart_2731131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731171 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 5, 4]
def baseStart_2731171 : Nat := 118140960795 + 2731171 * 2 ^ 59
def prefixEnd_2731171 : Nat := 4983230072969 + 3 ^ 40 * 2731171 * 2
def baseEnd_2731171 : Nat := 467467824206946338200693

theorem tailTrace_2731171 : CollatzResearch.WordTrace tailWord_2731171 prefixEnd_2731171 467467824206946338200693 := by
  unfold tailWord_2731171
  simp only [CollatzResearch.WordTrace]
  refine ⟨99613989988441388716177367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66409326658960925810784911 99613989988441388716177367)
  ·
    refine ⟨149420984982662083074266051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99613989988441388716177367 149420984982662083074266051)
    ·
      refine ⟨224131477473993124611399077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149420984982662083074266051 224131477473993124611399077)
      ·
        refine ⟨42024652026373710864637327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 224131477473993124611399077 42024652026373710864637327)
        ·
          refine ⟨63036978039560566296955991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42024652026373710864637327 63036978039560566296955991)
          ·
            refine ⟨94555467059340849445433987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63036978039560566296955991 94555467059340849445433987)
            ·
              refine ⟨141833200589011274168150981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94555467059340849445433987 141833200589011274168150981)
              ·
                refine ⟨26593725110439613906528309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141833200589011274168150981 26593725110439613906528309)
                ·
                  refine ⟨2493161729103713803737029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26593725110439613906528309 2493161729103713803737029)
                  ·
                    refine ⟨467467824206946338200693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2493161729103713803737029 467467824206946338200693)
                    ·
                      rfl

theorem cell23_2731171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5, 4].length) (baseStart_2731171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731171 prefixEnd_2731171 := by exact prefixLift 2731171
  have htrace : WordTrace (prefixWord ++ tailWord_2731171) baseStart_2731171 baseEnd_2731171 := by
    simpa [prefixWord, tailWord_2731171, baseEnd_2731171] using wordTrace_append hprefix tailTrace_2731171
  have hstable : (prefixWord ++ tailWord_2731171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731171).length < 2 ^ (prefixWord ++ tailWord_2731171).sum := by decide
  have hdescent : baseEnd_2731171 < baseStart_2731171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731190 : List Nat := [5, 1, 3, 2, 2, 1, 2, 1, 2, 2, 2]
def baseStart_2731190 : Nat := 118140960795 + 2731190 * 2 ^ 59
def prefixEnd_2731190 : Nat := 4983230072969 + 3 ^ 40 * 2731190 * 2
def baseEnd_2731190 : Nat := 1402413228753274440264493

theorem tailTrace_2731190 : CollatzResearch.WordTrace tailWord_2731190 prefixEnd_2731190 1402413228753274440264493 := by
  unfold tailWord_2731190
  simp only [CollatzResearch.WordTrace]
  refine ⟨6225917685960784685069939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66409788650248369974079349 6225917685960784685069939)
  ·
    refine ⟨9338876528941177027604909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6225917685960784685069939 9338876528941177027604909)
    ·
      refine ⟨3502078698352941385351841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9338876528941177027604909 3502078698352941385351841)
      ·
        refine ⟨2626559023764706039013881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3502078698352941385351841 2626559023764706039013881)
        ·
          refine ⟨1969919267823529529260411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2626559023764706039013881 1969919267823529529260411)
          ·
            refine ⟨2954878901735294293890617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1969919267823529529260411 2954878901735294293890617)
            ·
              refine ⟨2216159176301470720417963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2954878901735294293890617 2216159176301470720417963)
              ·
                refine ⟨3324238764452206080626945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2216159176301470720417963 3324238764452206080626945)
                ·
                  refine ⟨2493179073339154560470209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3324238764452206080626945 2493179073339154560470209)
                  ·
                    refine ⟨1869884305004365920352657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2493179073339154560470209 1869884305004365920352657)
                    ·
                      refine ⟨1402413228753274440264493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1869884305004365920352657 1402413228753274440264493)
                      ·
                        rfl

theorem cell23_2731190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_2731190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731190 prefixEnd_2731190 := by exact prefixLift 2731190
  have htrace : WordTrace (prefixWord ++ tailWord_2731190) baseStart_2731190 baseEnd_2731190 := by
    simpa [prefixWord, tailWord_2731190, baseEnd_2731190] using wordTrace_append hprefix tailTrace_2731190
  have hstable : (prefixWord ++ tailWord_2731190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731190).length < 2 ^ (prefixWord ++ tailWord_2731190).sum := by decide
  have hdescent : baseEnd_2731190 < baseStart_2731190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731262 : List Nat := [4, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3]
def baseStart_2731262 : Nat := 118140960795 + 2731262 * 2 ^ 59
def prefixEnd_2731262 : Nat := 4983230072969 + 3 ^ 40 * 2731262 * 2
def baseEnd_2731262 : Nat := 1402450199360398158564161

theorem tailTrace_2731262 : CollatzResearch.WordTrace tailWord_2731262 prefixEnd_2731262 1402450199360398158564161 := by
  unfold tailWord_2731262
  simp only [CollatzResearch.WordTrace]
  refine ⟨12452163628888963907217505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66411539354074474171826693 12452163628888963907217505)
  ·
    refine ⟨9339122721666722930413129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12452163628888963907217505 9339122721666722930413129)
    ·
      refine ⟨7004342041250042197809847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9339122721666722930413129 7004342041250042197809847)
      ·
        refine ⟨10506513061875063296714771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7004342041250042197809847 10506513061875063296714771)
        ·
          refine ⟨15759769592812594945072157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10506513061875063296714771 15759769592812594945072157)
          ·
            refine ⟨5909913597304723104402059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15759769592812594945072157 5909913597304723104402059)
            ·
              refine ⟨8864870395957084656603089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5909913597304723104402059 8864870395957084656603089)
              ·
                refine ⟨6648652796967813492452317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8864870395957084656603089 6648652796967813492452317)
                ·
                  refine ⟨2493244798862930059669619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6648652796967813492452317 2493244798862930059669619)
                  ·
                    refine ⟨3739867198294395089504429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2493244798862930059669619 3739867198294395089504429)
                    ·
                      refine ⟨1402450199360398158564161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3739867198294395089504429 1402450199360398158564161)
                      ·
                        rfl

theorem cell23_2731262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_2731262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731262 prefixEnd_2731262 := by exact prefixLift 2731262
  have htrace : WordTrace (prefixWord ++ tailWord_2731262) baseStart_2731262 baseEnd_2731262 := by
    simpa [prefixWord, tailWord_2731262, baseEnd_2731262] using wordTrace_append hprefix tailTrace_2731262
  have hstable : (prefixWord ++ tailWord_2731262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731262).length < 2 ^ (prefixWord ++ tailWord_2731262).sum := by decide
  have hdescent : baseEnd_2731262 < baseStart_2731262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731278 : List Nat := [4, 1, 1, 2, 1, 3, 2, 2, 1, 6]
def baseStart_2731278 : Nat := 118140960795 + 2731278 * 2 ^ 59
def prefixEnd_2731278 : Nat := 4983230072969 + 3 ^ 40 * 2731278 * 2
def baseEnd_2731278 : Nat := 467486138350290031988029

theorem tailTrace_2731278 : CollatzResearch.WordTrace tailWord_2731278 prefixEnd_2731278 467486138350290031988029 := by
  unfold tailWord_2731278
  simp only [CollatzResearch.WordTrace]
  refine ⟨12452236574881718248790311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66411928399369163993548325 12452236574881718248790311)
  ·
    refine ⟨18678354862322577373185467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12452236574881718248790311 18678354862322577373185467)
    ·
      refine ⟨28017532293483866059778201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18678354862322577373185467 28017532293483866059778201)
      ·
        refine ⟨21013149220112899544833651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28017532293483866059778201 21013149220112899544833651)
        ·
          refine ⟨31519723830169349317250477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21013149220112899544833651 31519723830169349317250477)
          ·
            refine ⟨11819896436313505993968929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31519723830169349317250477 11819896436313505993968929)
            ·
              refine ⟨8864922327235129495476697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11819896436313505993968929 8864922327235129495476697)
              ·
                refine ⟨6648691745426347121607523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8864922327235129495476697 6648691745426347121607523)
                ·
                  refine ⟨9973037618139520682411285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6648691745426347121607523 9973037618139520682411285)
                  ·
                    refine ⟨467486138350290031988029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9973037618139520682411285 467486138350290031988029)
                    ·
                      rfl

theorem cell23_2731278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_2731278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731278 prefixEnd_2731278 := by exact prefixLift 2731278
  have htrace : WordTrace (prefixWord ++ tailWord_2731278) baseStart_2731278 baseEnd_2731278 := by
    simpa [prefixWord, tailWord_2731278, baseEnd_2731278] using wordTrace_append hprefix tailTrace_2731278
  have hstable : (prefixWord ++ tailWord_2731278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731278).length < 2 ^ (prefixWord ++ tailWord_2731278).sum := by decide
  have hdescent : baseEnd_2731278 < baseStart_2731278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731285 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 7, 2, 2]
def baseStart_2731285 : Nat := 118140960795 + 2731285 * 2 ^ 59
def prefixEnd_2731285 : Nat := 4983230072969 + 3 ^ 40 * 2731285 * 2
def baseEnd_2731285 : Nat := 1402462009415451568576555

theorem tailTrace_2731285 : CollatzResearch.WordTrace tailWord_2731285 prefixEnd_2731285 1402462009415451568576555 := by
  unfold tailWord_2731285
  simp only [CollatzResearch.WordTrace]
  refine ⟨99618147910028386185827309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66412098606685590790551539 99618147910028386185827309)
  ·
    refine ⟨37356805466260644819685241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99618147910028386185827309 37356805466260644819685241)
    ·
      refine ⟨28017604099695483614763931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37356805466260644819685241 28017604099695483614763931)
      ·
        refine ⟨42026406149543225422145897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28017604099695483614763931 42026406149543225422145897)
        ·
          refine ⟨31519804612157419066609423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42026406149543225422145897 31519804612157419066609423)
          ·
            refine ⟨47279706918236128599914135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31519804612157419066609423 47279706918236128599914135)
            ·
              refine ⟨70919560377354192899871203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47279706918236128599914135 70919560377354192899871203)
              ·
                refine ⟨106379340566031289349806805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70919560377354192899871203 106379340566031289349806805)
                ·
                  refine ⟨2493265794516358344136097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 106379340566031289349806805 2493265794516358344136097)
                  ·
                    refine ⟨1869949345887268758102073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2493265794516358344136097 1869949345887268758102073)
                    ·
                      refine ⟨1402462009415451568576555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1869949345887268758102073 1402462009415451568576555)
                      ·
                        rfl

theorem cell23_2731285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7, 2, 2].length) (baseStart_2731285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731285 prefixEnd_2731285 := by exact prefixLift 2731285
  have htrace : WordTrace (prefixWord ++ tailWord_2731285) baseStart_2731285 baseEnd_2731285 := by
    simpa [prefixWord, tailWord_2731285, baseEnd_2731285] using wordTrace_append hprefix tailTrace_2731285
  have hstable : (prefixWord ++ tailWord_2731285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731285).length < 2 ^ (prefixWord ++ tailWord_2731285).sum := by decide
  have hdescent : baseEnd_2731285 < baseStart_2731285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731295 : List Nat := [1, 1, 2, 4, 4, 1, 1, 1, 4, 4]
def baseStart_2731295 : Nat := 118140960795 + 2731295 * 2 ^ 59
def prefixEnd_2731295 : Nat := 4983230072969 + 3 ^ 40 * 2731295 * 2
def baseEnd_2731295 : Nat := 467489048073998843150503

theorem tailTrace_2731295 : CollatzResearch.WordTrace tailWord_2731295 prefixEnd_2731295 467489048073998843150503 := by
  unfold tailWord_2731295
  simp only [CollatzResearch.WordTrace]
  refine ⟨99618512639992157893691339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66412341759994771929127559 99618512639992157893691339)
  ·
    refine ⟨149427768959988236840537009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99618512639992157893691339 149427768959988236840537009)
    ·
      refine ⟨112070826719991177630402757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149427768959988236840537009 112070826719991177630402757)
      ·
        refine ⟨21013280009998345805700517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112070826719991177630402757 21013280009998345805700517)
        ·
          refine ⟨3939990001874689838568847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21013280009998345805700517 3939990001874689838568847)
          ·
            refine ⟨5909985002812034757853271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3939990001874689838568847 5909985002812034757853271)
            ·
              refine ⟨8864977504218052136779907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5909985002812034757853271 8864977504218052136779907)
              ·
                refine ⟨13297466256327078205169861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8864977504218052136779907 13297466256327078205169861)
                ·
                  refine ⟨2493274923061327163469349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13297466256327078205169861 2493274923061327163469349)
                  ·
                    refine ⟨467489048073998843150503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2493274923061327163469349 467489048073998843150503)
                    ·
                      rfl

theorem cell23_2731295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4, 4].length) (baseStart_2731295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731295 prefixEnd_2731295 := by exact prefixLift 2731295
  have htrace : WordTrace (prefixWord ++ tailWord_2731295) baseStart_2731295 baseEnd_2731295 := by
    simpa [prefixWord, tailWord_2731295, baseEnd_2731295] using wordTrace_append hprefix tailTrace_2731295
  have hstable : (prefixWord ++ tailWord_2731295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731295).length < 2 ^ (prefixWord ++ tailWord_2731295).sum := by decide
  have hdescent : baseEnd_2731295 < baseStart_2731295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731315 : List Nat := [1, 1, 1, 2, 5, 4, 1, 1, 1, 2, 4]
def baseStart_2731315 : Nat := 118140960795 + 2731315 * 2 ^ 59
def prefixEnd_2731315 : Nat := 4983230072969 + 3 ^ 40 * 2731315 * 2
def baseEnd_2731315 : Nat := 1402477413835086451201417

theorem tailTrace_2731315 : CollatzResearch.WordTrace tailWord_2731315 prefixEnd_2731315 1402477413835086451201417 := by
  unfold tailWord_2731315
  simp only [CollatzResearch.WordTrace]
  refine ⟨99619242099919701309419399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66412828066613134206279599 99619242099919701309419399)
  ·
    refine ⟨149428863149879551964129099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99619242099919701309419399 149428863149879551964129099)
    ·
      refine ⟨224143294724819327946193649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149428863149879551964129099 224143294724819327946193649)
      ·
        refine ⟨168107471043614495959645237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224143294724819327946193649 168107471043614495959645237)
        ·
          refine ⟨15760075410338858996216741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 168107471043614495959645237 15760075410338858996216741)
          ·
            refine ⟨2955014139438536061790639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15760075410338858996216741 2955014139438536061790639)
            ·
              refine ⟨4432521209157804092685959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2955014139438536061790639 4432521209157804092685959)
              ·
                refine ⟨6648781813736706139028939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4432521209157804092685959 6648781813736706139028939)
                ·
                  refine ⟨9973172720605059208543409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6648781813736706139028939 9973172720605059208543409)
                  ·
                    refine ⟨7479879540453794406407557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9973172720605059208543409 7479879540453794406407557)
                    ·
                      refine ⟨1402477413835086451201417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7479879540453794406407557 1402477413835086451201417)
                      ·
                        rfl

theorem cell23_2731315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 2, 4].length) (baseStart_2731315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731315 prefixEnd_2731315 := by exact prefixLift 2731315
  have htrace : WordTrace (prefixWord ++ tailWord_2731315) baseStart_2731315 baseEnd_2731315 := by
    simpa [prefixWord, tailWord_2731315, baseEnd_2731315] using wordTrace_append hprefix tailTrace_2731315
  have hstable : (prefixWord ++ tailWord_2731315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731315).length < 2 ^ (prefixWord ++ tailWord_2731315).sum := by decide
  have hdescent : baseEnd_2731315 < baseStart_2731315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731325 : List Nat := [1, 4, 1, 5, 1, 1, 1, 9]
def baseStart_2731325 : Nat := 118140960795 + 2731325 * 2 ^ 59
def prefixEnd_2731325 : Nat := 4983230072969 + 3 ^ 40 * 2731325 * 2
def baseEnd_2731325 : Nat := 51943798097838200447273

theorem tailTrace_2731325 : CollatzResearch.WordTrace tailWord_2731325 prefixEnd_2731325 51943798097838200447273 := by
  unfold tailWord_2731325
  simp only [CollatzResearch.WordTrace]
  refine ⟨99619606829883473017283429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66413071219922315344855619 99619606829883473017283429)
  ·
    refine ⟨18678676280603151190740643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99619606829883473017283429 18678676280603151190740643)
    ·
      refine ⟨28018014420904726786110965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18678676280603151190740643 28018014420904726786110965)
      ·
        refine ⟨2626688851959818136197903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28018014420904726786110965 2626688851959818136197903)
        ·
          refine ⟨3940033277939727204296855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2626688851959818136197903 3940033277939727204296855)
          ·
            refine ⟨5910049916909590806445283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3940033277939727204296855 5910049916909590806445283)
            ·
              refine ⟨8865074875364386209667925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5910049916909590806445283 8865074875364386209667925)
              ·
                refine ⟨51943798097838200447273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8865074875364386209667925 51943798097838200447273)
                ·
                  rfl

theorem cell23_2731325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 9].length) (baseStart_2731325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731325 prefixEnd_2731325 := by exact prefixLift 2731325
  have htrace : WordTrace (prefixWord ++ tailWord_2731325) baseStart_2731325 baseEnd_2731325 := by
    simpa [prefixWord, tailWord_2731325, baseEnd_2731325] using wordTrace_append hprefix tailTrace_2731325
  have hstable : (prefixWord ++ tailWord_2731325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731325).length < 2 ^ (prefixWord ++ tailWord_2731325).sum := by decide
  have hdescent : baseEnd_2731325 < baseStart_2731325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731335 : List Nat := [1, 1, 4, 1, 2, 3, 1, 2, 4, 1, 3]
def baseStart_2731335 : Nat := 118140960795 + 2731335 * 2 ^ 59
def prefixEnd_2731335 : Nat := 4983230072969 + 3 ^ 40 * 2731335 * 2
def baseEnd_2731335 : Nat := 1402487683448176372951325

theorem tailTrace_2731335 : CollatzResearch.WordTrace tailWord_2731335 prefixEnd_2731335 1402487683448176372951325 := by
  unfold tailWord_2731335
  simp only [CollatzResearch.WordTrace]
  refine ⟨99619971559847244725147459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66413314373231496483431639 99619971559847244725147459)
  ·
    refine ⟨149429957339770867087721189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99619971559847244725147459 149429957339770867087721189)
    ·
      refine ⟨28018117001207037578947723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149429957339770867087721189 28018117001207037578947723)
      ·
        refine ⟨42027175501810556368421585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28018117001207037578947723 42027175501810556368421585)
        ·
          refine ⟨31520381626357917276316189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42027175501810556368421585 31520381626357917276316189)
          ·
            refine ⟨11820143109884218978618571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31520381626357917276316189 11820143109884218978618571)
            ·
              refine ⟨17730214664826328467927857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11820143109884218978618571 17730214664826328467927857)
              ·
                refine ⟨13297660998619746350945893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17730214664826328467927857 13297660998619746350945893)
                ·
                  refine ⟨2493311437241202440802355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13297660998619746350945893 2493311437241202440802355)
                  ·
                    refine ⟨3739967155861803661203533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2493311437241202440802355 3739967155861803661203533)
                    ·
                      refine ⟨1402487683448176372951325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3739967155861803661203533 1402487683448176372951325)
                      ·
                        rfl

theorem cell23_2731335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_2731335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731335 prefixEnd_2731335 := by exact prefixLift 2731335
  have htrace : WordTrace (prefixWord ++ tailWord_2731335) baseStart_2731335 baseEnd_2731335 := by
    simpa [prefixWord, tailWord_2731335, baseEnd_2731335] using wordTrace_append hprefix tailTrace_2731335
  have hstable : (prefixWord ++ tailWord_2731335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731335).length < 2 ^ (prefixWord ++ tailWord_2731335).sum := by decide
  have hdescent : baseEnd_2731335 < baseStart_2731335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731348 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_2731348 : Nat := 118140960795 + 2731348 * 2 ^ 59
def prefixEnd_2731348 : Nat := 4983230072969 + 3 ^ 40 * 2731348 * 2
def baseEnd_2731348 : Nat := 1402494358696684822088765

theorem tailTrace_2731348 : CollatzResearch.WordTrace tailWord_2731348 prefixEnd_2731348 1402494358696684822088765 := by
  unfold tailWord_2731348
  simp only [CollatzResearch.WordTrace]
  refine ⟨49810222854400073972685349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66413630472533431963580465 49810222854400073972685349)
  ·
    refine ⟨9339416785200013869878503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49810222854400073972685349 9339416785200013869878503)
    ·
      refine ⟨14009125177800020804817755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9339416785200013869878503 14009125177800020804817755)
      ·
        refine ⟨21013687766700031207226633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14009125177800020804817755 21013687766700031207226633)
        ·
          refine ⟨15760265825025023405419975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21013687766700031207226633 15760265825025023405419975)
          ·
            refine ⟨23640398737537535108129963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15760265825025023405419975 23640398737537535108129963)
            ·
              refine ⟨35460598106306302662194945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23640398737537535108129963 35460598106306302662194945)
              ·
                refine ⟨26595448579729726996646209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35460598106306302662194945 26595448579729726996646209)
                ·
                  refine ⟨19946586434797295247484657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26595448579729726996646209 19946586434797295247484657)
                  ·
                    refine ⟨14959939826097971435613493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19946586434797295247484657 14959939826097971435613493)
                    ·
                      refine ⟨1402494358696684822088765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14959939826097971435613493 1402494358696684822088765)
                      ·
                        rfl

theorem cell23_2731348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_2731348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731348 prefixEnd_2731348 := by exact prefixLift 2731348
  have htrace : WordTrace (prefixWord ++ tailWord_2731348) baseStart_2731348 baseEnd_2731348 := by
    simpa [prefixWord, tailWord_2731348, baseEnd_2731348] using wordTrace_append hprefix tailTrace_2731348
  have hstable : (prefixWord ++ tailWord_2731348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731348).length < 2 ^ (prefixWord ++ tailWord_2731348).sum := by decide
  have hdescent : baseEnd_2731348 < baseStart_2731348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731362 : List Nat := [3, 3, 2, 1, 1, 1, 2, 2, 3, 3, 2]
def baseStart_2731362 : Nat := 118140960795 + 2731362 * 2 ^ 59
def prefixEnd_2731362 : Nat := 4983230072969 + 3 ^ 40 * 2731362 * 2
def baseEnd_2731362 : Nat := 1402501547425847767313701

theorem tailTrace_2731362 : CollatzResearch.WordTrace tailWord_2731362 prefixEnd_2731362 1402501547425847767313701 := by
  unfold tailWord_2731362
  simp only [CollatzResearch.WordTrace]
  refine ⟨24905239082687357084095085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66413970887166285557586893 24905239082687357084095085)
  ·
    refine ⟨9339464656007758906535657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24905239082687357084095085 9339464656007758906535657)
    ·
      refine ⟨7004598492005819179901743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9339464656007758906535657 7004598492005819179901743)
      ·
        refine ⟨10506897738008728769852615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7004598492005819179901743 10506897738008728769852615)
        ·
          refine ⟨15760346607013093154778923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10506897738008728769852615 15760346607013093154778923)
          ·
            refine ⟨23640519910519639732168385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15760346607013093154778923 23640519910519639732168385)
            ·
              refine ⟨17730389932889729799126289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23640519910519639732168385 17730389932889729799126289)
              ·
                refine ⟨13297792449667297349344717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17730389932889729799126289 13297792449667297349344717)
                ·
                  refine ⟨4986672168625236506004269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13297792449667297349344717 4986672168625236506004269)
                  ·
                    refine ⟨1870002063234463689751601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4986672168625236506004269 1870002063234463689751601)
                    ·
                      refine ⟨1402501547425847767313701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1870002063234463689751601 1402501547425847767313701)
                      ·
                        rfl

theorem cell23_2731362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_2731362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731362 prefixEnd_2731362 := by exact prefixLift 2731362
  have htrace : WordTrace (prefixWord ++ tailWord_2731362) baseStart_2731362 baseEnd_2731362 := by
    simpa [prefixWord, tailWord_2731362, baseEnd_2731362] using wordTrace_append hprefix tailTrace_2731362
  have hstable : (prefixWord ++ tailWord_2731362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731362).length < 2 ^ (prefixWord ++ tailWord_2731362).sum := by decide
  have hdescent : baseEnd_2731362 < baseStart_2731362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731375 : List Nat := [1, 1, 2, 1, 3, 1, 4, 3, 1, 4, 2]
def baseStart_2731375 : Nat := 118140960795 + 2731375 * 2 ^ 59
def prefixEnd_2731375 : Nat := 4983230072969 + 3 ^ 40 * 2731375 * 2
def baseEnd_2731375 : Nat := 1402508222674356216451141

theorem tailTrace_2731375 : CollatzResearch.WordTrace tailWord_2731375 prefixEnd_2731375 1402508222674356216451141 := by
  unfold tailWord_2731375
  simp only [CollatzResearch.WordTrace]
  refine ⟨99621430479702331556603579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66414286986468221037735719 99621430479702331556603579)
  ·
    refine ⟨149432145719553497334905369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99621430479702331556603579 149432145719553497334905369)
    ·
      refine ⟨112074109289665123001179027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149432145719553497334905369 112074109289665123001179027)
      ·
        refine ⟨168111163934497684501768541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112074109289665123001179027 168111163934497684501768541)
        ·
          refine ⟨63041686475436631688163203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168111163934497684501768541 63041686475436631688163203)
          ·
            refine ⟨94562529713154947532244805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63041686475436631688163203 94562529713154947532244805)
            ·
              refine ⟨17730474321216552662295901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94562529713154947532244805 17730474321216552662295901)
              ·
                refine ⟨6648927870456207248360963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17730474321216552662295901 6648927870456207248360963)
                ·
                  refine ⟨9973391805684310872541445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6648927870456207248360963 9973391805684310872541445)
                  ·
                    refine ⟨1870010963565808288601521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9973391805684310872541445 1870010963565808288601521)
                    ·
                      refine ⟨1402508222674356216451141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1870010963565808288601521 1402508222674356216451141)
                      ·
                        rfl

theorem cell23_2731375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 4, 2].length) (baseStart_2731375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731375 prefixEnd_2731375 := by exact prefixLift 2731375
  have htrace : WordTrace (prefixWord ++ tailWord_2731375) baseStart_2731375 baseEnd_2731375 := by
    simpa [prefixWord, tailWord_2731375, baseEnd_2731375] using wordTrace_append hprefix tailTrace_2731375
  have hstable : (prefixWord ++ tailWord_2731375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731375).length < 2 ^ (prefixWord ++ tailWord_2731375).sum := by decide
  have hdescent : baseEnd_2731375 < baseStart_2731375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731378 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 4, 1, 5]
def baseStart_2731378 : Nat := 118140960795 + 2731378 * 2 ^ 59
def prefixEnd_2731378 : Nat := 4983230072969 + 3 ^ 40 * 2731378 * 2
def baseEnd_2731378 : Nat := 1402509763116319704713627

theorem tailTrace_2731378 : CollatzResearch.WordTrace tailWord_2731378 prefixEnd_2731378 1402509763116319704713627 := by
  unfold tailWord_2731378
  simp only [CollatzResearch.WordTrace]
  refine ⟨24905384974672865767240697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66414359932460975379308525 24905384974672865767240697)
  ·
    refine ⟨18679038731004649325430523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24905384974672865767240697 18679038731004649325430523)
    ·
      refine ⟨28018558096506973988145785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18679038731004649325430523 28018558096506973988145785)
      ·
        refine ⟨21013918572380230491109339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28018558096506973988145785 21013918572380230491109339)
        ·
          refine ⟨31520877858570345736664009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21013918572380230491109339 31520877858570345736664009)
          ·
            refine ⟨23640658393927759302498007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31520877858570345736664009 23640658393927759302498007)
            ·
              refine ⟨35460987590891638953747011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23640658393927759302498007 35460987590891638953747011)
              ·
                refine ⟨53191481386337458430620517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35460987590891638953747011 53191481386337458430620517)
                ·
                  refine ⟨9973402759938273455741347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53191481386337458430620517 9973402759938273455741347)
                  ·
                    refine ⟨14960104139907410183612021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9973402759938273455741347 14960104139907410183612021)
                    ·
                      refine ⟨1402509763116319704713627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14960104139907410183612021 1402509763116319704713627)
                      ·
                        rfl

theorem cell23_2731378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_2731378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731378 prefixEnd_2731378 := by exact prefixLift 2731378
  have htrace : WordTrace (prefixWord ++ tailWord_2731378) baseStart_2731378 baseEnd_2731378 := by
    simpa [prefixWord, tailWord_2731378, baseEnd_2731378] using wordTrace_append hprefix tailTrace_2731378
  have hstable : (prefixWord ++ tailWord_2731378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731378).length < 2 ^ (prefixWord ++ tailWord_2731378).sum := by decide
  have hdescent : baseEnd_2731378 < baseStart_2731378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731428 : List Nat := [2, 3, 1, 2, 1, 1, 1, 4, 1, 7]
def baseStart_2731428 : Nat := 118140960795 + 2731428 * 2 ^ 59
def prefixEnd_2731428 : Nat := 4983230072969 + 3 ^ 40 * 2731428 * 2
def baseEnd_2731428 : Nat := 467511812383014836362799

theorem tailTrace_2731428 : CollatzResearch.WordTrace tailWord_2731428 prefixEnd_2731428 467511812383014836362799 := by
  unfold tailWord_2731428
  simp only [CollatzResearch.WordTrace]
  refine ⟨49811681774255160804141469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66415575699006881072188625 49811681774255160804141469)
  ·
    refine ⟨18679380665345685301553051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49811681774255160804141469 18679380665345685301553051)
    ·
      refine ⟨28019070998018527952329577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18679380665345685301553051 28019070998018527952329577)
      ·
        refine ⟨21014303248513895964247183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28019070998018527952329577 21014303248513895964247183)
        ·
          refine ⟨31521454872770843946370775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21014303248513895964247183 31521454872770843946370775)
          ·
            refine ⟨47282182309156265919556163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31521454872770843946370775 47282182309156265919556163)
            ·
              refine ⟨70923273463734398879334245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47282182309156265919556163 70923273463734398879334245)
              ·
                refine ⟨13298113774450199789875171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70923273463734398879334245 13298113774450199789875171)
                ·
                  refine ⟨19947170661675299684812757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13298113774450199789875171 19947170661675299684812757)
                  ·
                    refine ⟨467511812383014836362799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19947170661675299684812757 467511812383014836362799)
                    ·
                      rfl

theorem cell23_2731428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_2731428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731428 prefixEnd_2731428 := by exact prefixLift 2731428
  have htrace : WordTrace (prefixWord ++ tailWord_2731428) baseStart_2731428 baseEnd_2731428 := by
    simpa [prefixWord, tailWord_2731428, baseEnd_2731428] using wordTrace_append hprefix tailTrace_2731428
  have hstable : (prefixWord ++ tailWord_2731428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731428).length < 2 ^ (prefixWord ++ tailWord_2731428).sum := by decide
  have hdescent : baseEnd_2731428 < baseStart_2731428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731432 : List Nat := [2, 1, 6, 1, 2, 1, 1, 2, 7]
def baseStart_2731432 : Nat := 118140960795 + 2731432 * 2 ^ 59
def prefixEnd_2731432 : Nat := 4983230072969 + 3 ^ 40 * 2731432 * 2
def baseEnd_2731432 : Nat := 155837499007962499270931

theorem tailTrace_2731432 : CollatzResearch.WordTrace tailWord_2731432 prefixEnd_2731432 155837499007962499270931 := by
  unfold tailWord_2731432
  simp only [CollatzResearch.WordTrace]
  refine ⟨49811754720247915145714275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66415672960330553527619033 49811754720247915145714275)
  ·
    refine ⟨74717632080371872718571413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49811754720247915145714275 74717632080371872718571413)
    ·
      refine ⟨3502389003767431533683035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 74717632080371872718571413 3502389003767431533683035)
      ·
        refine ⟨5253583505651147300524553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3502389003767431533683035 5253583505651147300524553)
        ·
          refine ⟨3940187629238360475393415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5253583505651147300524553 3940187629238360475393415)
          ·
            refine ⟨5910281443857540713090123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3940187629238360475393415 5910281443857540713090123)
            ·
              refine ⟨8865422165786311069635185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5910281443857540713090123 8865422165786311069635185)
              ·
                refine ⟨6649066624339733302226389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8865422165786311069635185 6649066624339733302226389)
                ·
                  refine ⟨155837499007962499270931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6649066624339733302226389 155837499007962499270931)
                  ·
                    rfl

theorem cell23_2731432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 7].length) (baseStart_2731432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731432 prefixEnd_2731432 := by exact prefixLift 2731432
  have htrace : WordTrace (prefixWord ++ tailWord_2731432) baseStart_2731432 baseEnd_2731432 := by
    simpa [prefixWord, tailWord_2731432, baseEnd_2731432] using wordTrace_append hprefix tailTrace_2731432
  have hstable : (prefixWord ++ tailWord_2731432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731432).length < 2 ^ (prefixWord ++ tailWord_2731432).sum := by decide
  have hdescent : baseEnd_2731432 < baseStart_2731432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731445 : List Nat := [1, 3, 3, 2, 2, 2, 1, 1, 1, 7]
def baseStart_2731445 : Nat := 118140960795 + 2731445 * 2 ^ 59
def prefixEnd_2731445 : Nat := 4983230072969 + 3 ^ 40 * 2731445 * 2
def baseEnd_2731445 : Nat := 467514722106723647525273

theorem tailTrace_2731445 : CollatzResearch.WordTrace tailWord_2731445 prefixEnd_2731445 467514722106723647525273 := by
  unfold tailWord_2731445
  simp only [CollatzResearch.WordTrace]
  refine ⟨99623983589448733511651789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66415989059632489007767859 99623983589448733511651789)
  ·
    refine ⟨37358993846043275066869421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99623983589448733511651789 37358993846043275066869421)
    ·
      refine ⟨14009622692266228150076033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37358993846043275066869421 14009622692266228150076033)
      ·
        refine ⟨10507217019199671112557025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14009622692266228150076033 10507217019199671112557025)
        ·
          refine ⟨7880412764399753334417769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10507217019199671112557025 7880412764399753334417769)
          ·
            refine ⟨5910309573299815000813327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7880412764399753334417769 5910309573299815000813327)
            ·
              refine ⟨8865464359949722501219991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5910309573299815000813327 8865464359949722501219991)
              ·
                refine ⟨13298196539924583751829987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8865464359949722501219991 13298196539924583751829987)
                ·
                  refine ⟨19947294809886875627744981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13298196539924583751829987 19947294809886875627744981)
                  ·
                    refine ⟨467514722106723647525273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19947294809886875627744981 467514722106723647525273)
                    ·
                      rfl

theorem cell23_2731445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_2731445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731445 prefixEnd_2731445 := by exact prefixLift 2731445
  have htrace : WordTrace (prefixWord ++ tailWord_2731445) baseStart_2731445 baseEnd_2731445 := by
    simpa [prefixWord, tailWord_2731445, baseEnd_2731445] using wordTrace_append hprefix tailTrace_2731445
  have hstable : (prefixWord ++ tailWord_2731445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731445).length < 2 ^ (prefixWord ++ tailWord_2731445).sum := by decide
  have hdescent : baseEnd_2731445 < baseStart_2731445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731482 : List Nat := [3, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2]
def baseStart_2731482 : Nat := 118140960795 + 2731482 * 2 ^ 59
def prefixEnd_2731482 : Nat := 4983230072969 + 3 ^ 40 * 2731482 * 2
def baseEnd_2731482 : Nat := 1402563165104387297813149

theorem tailTrace_2731482 : CollatzResearch.WordTrace tailWord_2731482 prefixEnd_2731482 1402563165104387297813149 := by
  unfold tailWord_2731482
  simp only [CollatzResearch.WordTrace]
  refine ⟨24906333272578672207687175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66416888726876459220499133 24906333272578672207687175)
  ·
    refine ⟨37359499908868008311530763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24906333272578672207687175 37359499908868008311530763)
    ·
      refine ⟨56039249863302012467296145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37359499908868008311530763 56039249863302012467296145)
      ·
        refine ⟨42029437397476509350472109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56039249863302012467296145 42029437397476509350472109)
        ·
          refine ⟨15761039024053691006427041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42029437397476509350472109 15761039024053691006427041)
          ·
            refine ⟨11820779268040268254820281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15761039024053691006427041 11820779268040268254820281)
            ·
              refine ⟨8865584451030201191115211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11820779268040268254820281 8865584451030201191115211)
              ·
                refine ⟨13298376676545301786672817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8865584451030201191115211 13298376676545301786672817)
                ·
                  refine ⟨9973782507408976340004613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13298376676545301786672817 9973782507408976340004613)
                  ·
                    refine ⟨1870084220139183063750865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9973782507408976340004613 1870084220139183063750865)
                    ·
                      refine ⟨1402563165104387297813149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1870084220139183063750865 1402563165104387297813149)
                      ·
                        rfl

theorem cell23_2731482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2].length) (baseStart_2731482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731482 prefixEnd_2731482 := by exact prefixLift 2731482
  have htrace : WordTrace (prefixWord ++ tailWord_2731482) baseStart_2731482 baseEnd_2731482 := by
    simpa [prefixWord, tailWord_2731482, baseEnd_2731482] using wordTrace_append hprefix tailTrace_2731482
  have hstable : (prefixWord ++ tailWord_2731482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731482).length < 2 ^ (prefixWord ++ tailWord_2731482).sum := by decide
  have hdescent : baseEnd_2731482 < baseStart_2731482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731502 : List Nat := [4, 1, 2, 1, 2, 1, 2, 3, 2, 2, 3]
def baseStart_2731502 : Nat := 118140960795 + 2731502 * 2 ^ 59
def prefixEnd_2731502 : Nat := 4983230072969 + 3 ^ 40 * 2731502 * 2
def baseEnd_2731502 : Nat := 1402573434717477219563057

theorem tailTrace_2731502 : CollatzResearch.WordTrace tailWord_2731502 prefixEnd_2731502 1402573434717477219563057 := by
  unfold tailWord_2731502
  simp only [CollatzResearch.WordTrace]
  refine ⟨12453257818780279030809595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66417375033494821497651173 12453257818780279030809595)
  ·
    refine ⟨18679886728170418546214393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12453257818780279030809595 18679886728170418546214393)
    ·
      refine ⟨14009915046127813909660795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18679886728170418546214393 14009915046127813909660795)
      ·
        refine ⟨21014872569191720864491193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14009915046127813909660795 21014872569191720864491193)
        ·
          refine ⟨15761154426893790648368395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21014872569191720864491193 15761154426893790648368395)
          ·
            refine ⟨23641731640340685972552593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15761154426893790648368395 23641731640340685972552593)
            ·
              refine ⟨17731298730255514479414445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23641731640340685972552593 17731298730255514479414445)
              ·
                refine ⟨6649237023845817929780417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17731298730255514479414445 6649237023845817929780417)
                ·
                  refine ⟨4986927767884363447335313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6649237023845817929780417 4986927767884363447335313)
                  ·
                    refine ⟨3740195825913272585501485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4986927767884363447335313 3740195825913272585501485)
                    ·
                      refine ⟨1402573434717477219563057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3740195825913272585501485 1402573434717477219563057)
                      ·
                        rfl

theorem cell23_2731502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_2731502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731502 prefixEnd_2731502 := by exact prefixLift 2731502
  have htrace : WordTrace (prefixWord ++ tailWord_2731502) baseStart_2731502 baseEnd_2731502 := by
    simpa [prefixWord, tailWord_2731502, baseEnd_2731502] using wordTrace_append hprefix tailTrace_2731502
  have hstable : (prefixWord ++ tailWord_2731502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731502).length < 2 ^ (prefixWord ++ tailWord_2731502).sum := by decide
  have hdescent : baseEnd_2731502 < baseStart_2731502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731522 : List Nat := [3, 4, 1, 2, 1, 1, 2, 1, 8]
def baseStart_2731522 : Nat := 118140960795 + 2731522 * 2 ^ 59
def prefixEnd_2731522 : Nat := 4983230072969 + 3 ^ 40 * 2731522 * 2
def baseEnd_2731522 : Nat := 155842633814507460145885

theorem tailTrace_2731522 : CollatzResearch.WordTrace tailWord_2731522 prefixEnd_2731522 155842633814507460145885 := by
  unfold tailWord_2731522
  simp only [CollatzResearch.WordTrace]
  refine ⟨24906698002542443915551205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66417861340113183774803213 24906698002542443915551205)
  ·
    refine ⟨4670005875476708234165851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24906698002542443915551205 4670005875476708234165851)
    ·
      refine ⟨7005008813215062351248777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4670005875476708234165851 7005008813215062351248777)
      ·
        refine ⟨5253756609911296763436583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7005008813215062351248777 5253756609911296763436583)
        ·
          refine ⟨7880634914866945145154875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5253756609911296763436583 7880634914866945145154875)
          ·
            refine ⟨11820952372300417717732313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7880634914866945145154875 11820952372300417717732313)
            ·
              refine ⟨8865714279225313288299235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11820952372300417717732313 8865714279225313288299235)
              ·
                refine ⟨13298571418837969932448853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8865714279225313288299235 13298571418837969932448853)
                ·
                  refine ⟨155842633814507460145885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13298571418837969932448853 155842633814507460145885)
                  ·
                    rfl

theorem cell23_2731522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_2731522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731522 prefixEnd_2731522 := by exact prefixLift 2731522
  have htrace : WordTrace (prefixWord ++ tailWord_2731522) baseStart_2731522 baseEnd_2731522 := by
    simpa [prefixWord, tailWord_2731522, baseEnd_2731522] using wordTrace_append hprefix tailTrace_2731522
  have hstable : (prefixWord ++ tailWord_2731522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731522).length < 2 ^ (prefixWord ++ tailWord_2731522).sum := by decide
  have hdescent : baseEnd_2731522 < baseStart_2731522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731552 : List Nat := [2, 1, 1, 6, 1, 2, 1, 1, 3, 5]
def baseStart_2731552 : Nat := 118140960795 + 2731552 * 2 ^ 59
def prefixEnd_2731552 : Nat := 4983230072969 + 3 ^ 40 * 2731552 * 2
def baseEnd_2731552 : Nat := 467533036250067341312609

theorem tailTrace_2731552 : CollatzResearch.WordTrace tailWord_2731552 prefixEnd_2731552 467533036250067341312609 := by
  unfold tailWord_2731552
  simp only [CollatzResearch.WordTrace]
  refine ⟨49813943100030545392898455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66418590800040727190531273 49813943100030545392898455)
  ·
    refine ⟨74720914650045818089347683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49813943100030545392898455 74720914650045818089347683)
    ·
      refine ⟨112081371975068727134021525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74720914650045818089347683 112081371975068727134021525)
      ·
        refine ⟨5253814311331346584407259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 112081371975068727134021525 5253814311331346584407259)
        ·
          refine ⟨7880721466997019876610889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5253814311331346584407259 7880721466997019876610889)
          ·
            refine ⟨5910541100247764907458167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7880721466997019876610889 5910541100247764907458167)
            ·
              refine ⟨8865811650371647361187251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5910541100247764907458167 8865811650371647361187251)
              ·
                refine ⟨13298717475557471041780877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8865811650371647361187251 13298717475557471041780877)
                ·
                  refine ⟨4987019053334051640667829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13298717475557471041780877 4987019053334051640667829)
                  ·
                    refine ⟨467533036250067341312609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4987019053334051640667829 467533036250067341312609)
                    ·
                      rfl

theorem cell23_2731552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 3, 5].length) (baseStart_2731552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731552 prefixEnd_2731552 := by exact prefixLift 2731552
  have htrace : WordTrace (prefixWord ++ tailWord_2731552) baseStart_2731552 baseEnd_2731552 := by
    simpa [prefixWord, tailWord_2731552, baseEnd_2731552] using wordTrace_append hprefix tailTrace_2731552
  have hstable : (prefixWord ++ tailWord_2731552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731552).length < 2 ^ (prefixWord ++ tailWord_2731552).sum := by decide
  have hdescent : baseEnd_2731552 < baseStart_2731552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731583 : List Nat := [1, 1, 2, 2, 3, 5, 2, 2, 1, 1, 3]
def baseStart_2731583 : Nat := 118140960795 + 2731583 * 2 ^ 59
def prefixEnd_2731583 : Nat := 4983230072969 + 3 ^ 40 * 2731583 * 2
def baseEnd_2731583 : Nat := 1402615026650491402650185

theorem tailTrace_2731583 : CollatzResearch.WordTrace tailWord_2731583 prefixEnd_2731583 1402615026650491402650185 := by
  unfold tailWord_2731583
  simp only [CollatzResearch.WordTrace]
  refine ⟨99629016862948783080175403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66419344575299188720116935 99629016862948783080175403)
  ·
    refine ⟨149443525294423174620263105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99629016862948783080175403 149443525294423174620263105)
    ·
      refine ⟨112082643970817380965197329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149443525294423174620263105 112082643970817380965197329)
      ·
        refine ⟨84061982978113035723897997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112082643970817380965197329 84061982978113035723897997)
        ·
          refine ⟨31523243616792388396461749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84061982978113035723897997 31523243616792388396461749)
          ·
            refine ⟨2955304089074286412168289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31523243616792388396461749 2955304089074286412168289)
            ·
              refine ⟨2216478066805714809126217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2955304089074286412168289 2216478066805714809126217)
              ·
                refine ⟨1662358550104286106844663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2216478066805714809126217 1662358550104286106844663)
                ·
                  refine ⟨2493537825156429160266995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1662358550104286106844663 2493537825156429160266995)
                  ·
                    refine ⟨3740306737734643740400493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2493537825156429160266995 3740306737734643740400493)
                    ·
                      refine ⟨1402615026650491402650185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3740306737734643740400493 1402615026650491402650185)
                      ·
                        rfl

theorem cell23_2731583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2, 1, 1, 3].length) (baseStart_2731583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731583 prefixEnd_2731583 := by exact prefixLift 2731583
  have htrace : WordTrace (prefixWord ++ tailWord_2731583) baseStart_2731583 baseEnd_2731583 := by
    simpa [prefixWord, tailWord_2731583, baseEnd_2731583] using wordTrace_append hprefix tailTrace_2731583
  have hstable : (prefixWord ++ tailWord_2731583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731583).length < 2 ^ (prefixWord ++ tailWord_2731583).sum := by decide
  have hdescent : baseEnd_2731583 < baseStart_2731583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731589 : List Nat := [1, 3, 1, 1, 1, 4, 2, 3, 3, 2, 2]
def baseStart_2731589 : Nat := 118140960795 + 2731589 * 2 ^ 59
def prefixEnd_2731589 : Nat := 4983230072969 + 3 ^ 40 * 2731589 * 2
def baseEnd_2731589 : Nat := 1402618107534418379175157

theorem tailTrace_2731589 : CollatzResearch.WordTrace tailWord_2731589 prefixEnd_2731589 1402618107534418379175157 := by
  unfold tailWord_2731589
  simp only [CollatzResearch.WordTrace]
  refine ⟨99629235700927046104893821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66419490467284697403262547 99629235700927046104893821)
  ·
    refine ⟨37360963387847642289335183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99629235700927046104893821 37360963387847642289335183)
    ·
      refine ⟨56041445081771463434002775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37360963387847642289335183 56041445081771463434002775)
      ·
        refine ⟨84062167622657195151004163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56041445081771463434002775 84062167622657195151004163)
        ·
          refine ⟨126093251433985792726506245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84062167622657195151004163 126093251433985792726506245)
          ·
            refine ⟨23642484643872336136219921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126093251433985792726506245 23642484643872336136219921)
            ·
              refine ⟨17731863482904252102164941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23642484643872336136219921 17731863482904252102164941)
              ·
                refine ⟨6649448806089094538311853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17731863482904252102164941 6649448806089094538311853)
                ·
                  refine ⟨2493543302283410451866945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6649448806089094538311853 2493543302283410451866945)
                  ·
                    refine ⟨1870157476712557838900209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2493543302283410451866945 1870157476712557838900209)
                    ·
                      refine ⟨1402618107534418379175157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1870157476712557838900209 1402618107534418379175157)
                      ·
                        rfl

theorem cell23_2731589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3, 2, 2].length) (baseStart_2731589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731589 prefixEnd_2731589 := by exact prefixLift 2731589
  have htrace : WordTrace (prefixWord ++ tailWord_2731589) baseStart_2731589 baseEnd_2731589 := by
    simpa [prefixWord, tailWord_2731589, baseEnd_2731589] using wordTrace_append hprefix tailTrace_2731589
  have hstable : (prefixWord ++ tailWord_2731589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731589).length < 2 ^ (prefixWord ++ tailWord_2731589).sum := by decide
  have hdescent : baseEnd_2731589 < baseStart_2731589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731602 : List Nat := [3, 2, 2, 1, 2, 2, 1, 3, 1, 2, 4]
def baseStart_2731602 : Nat := 118140960795 + 2731602 * 2 ^ 59
def prefixEnd_2731602 : Nat := 4983230072969 + 3 ^ 40 * 2731602 * 2
def baseEnd_2731602 : Nat := 1402624782782926828312597

theorem tailTrace_2731602 : CollatzResearch.WordTrace tailWord_2731602 prefixEnd_2731602 1402624782782926828312597 := by
  unfold tailWord_2731602
  simp only [CollatzResearch.WordTrace]
  refine ⟨24907427462469987331279265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66419806566586632883411373 24907427462469987331279265)
  ·
    refine ⟨18680570596852490498459449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24907427462469987331279265 18680570596852490498459449)
    ·
      refine ⟨14010427947639367873844587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18680570596852490498459449 14010427947639367873844587)
      ·
        refine ⟨21015641921459051810766881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14010427947639367873844587 21015641921459051810766881)
        ·
          refine ⟨15761731441094288858075161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21015641921459051810766881 15761731441094288858075161)
          ·
            refine ⟨11821298580820716643556371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15761731441094288858075161 11821298580820716643556371)
            ·
              refine ⟨17731947871231074965334557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11821298580820716643556371 17731947871231074965334557)
              ·
                refine ⟨6649480451711653112000459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17731947871231074965334557 6649480451711653112000459)
                ·
                  refine ⟨9974220677567479668000689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6649480451711653112000459 9974220677567479668000689)
                  ·
                    refine ⟨7480665508175609751000517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9974220677567479668000689 7480665508175609751000517)
                    ·
                      refine ⟨1402624782782926828312597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7480665508175609751000517 1402624782782926828312597)
                      ·
                        rfl

theorem cell23_2731602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_2731602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731602 prefixEnd_2731602 := by exact prefixLift 2731602
  have htrace : WordTrace (prefixWord ++ tailWord_2731602) baseStart_2731602 baseEnd_2731602 := by
    simpa [prefixWord, tailWord_2731602, baseEnd_2731602] using wordTrace_append hprefix tailTrace_2731602
  have hstable : (prefixWord ++ tailWord_2731602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731602).length < 2 ^ (prefixWord ++ tailWord_2731602).sum := by decide
  have hdescent : baseEnd_2731602 < baseStart_2731602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731626 : List Nat := [3, 1, 3, 2, 1, 2, 4, 1, 1, 2, 3]
def baseStart_2731626 : Nat := 118140960795 + 2731626 * 2 ^ 59
def prefixEnd_2731626 : Nat := 4983230072969 + 3 ^ 40 * 2731626 * 2
def baseEnd_2731626 : Nat := 1402637106318634734412487

theorem tailTrace_2731626 : CollatzResearch.WordTrace tailWord_2731626 prefixEnd_2731626 1402637106318634734412487 := by
  unfold tailWord_2731626
  simp only [CollatzResearch.WordTrace]
  refine ⟨24907646300448250355997683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66420390134528667615993821 24907646300448250355997683)
  ·
    refine ⟨37361469450672375533996525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24907646300448250355997683 37361469450672375533996525)
    ·
      refine ⟨14010551044002140825248697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37361469450672375533996525 14010551044002140825248697)
      ·
        refine ⟨10507913283001605618936523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14010551044002140825248697 10507913283001605618936523)
        ·
          refine ⟨15761869924502408428404785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10507913283001605618936523 15761869924502408428404785)
          ·
            refine ⟨11821402443376806321303589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15761869924502408428404785 11821402443376806321303589)
            ·
              refine ⟨2216512958133151185244423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11821402443376806321303589 2216512958133151185244423)
              ·
                refine ⟨3324769437199726777866635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2216512958133151185244423 3324769437199726777866635)
                ·
                  refine ⟨4987154155799590166799953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3324769437199726777866635 4987154155799590166799953)
                  ·
                    refine ⟨3740365616849692625099965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4987154155799590166799953 3740365616849692625099965)
                    ·
                      refine ⟨1402637106318634734412487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3740365616849692625099965 1402637106318634734412487)
                      ·
                        rfl

theorem cell23_2731626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_2731626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731626 prefixEnd_2731626 := by exact prefixLift 2731626
  have htrace : WordTrace (prefixWord ++ tailWord_2731626) baseStart_2731626 baseEnd_2731626 := by
    simpa [prefixWord, tailWord_2731626, baseEnd_2731626] using wordTrace_append hprefix tailTrace_2731626
  have hstable : (prefixWord ++ tailWord_2731626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731626).length < 2 ^ (prefixWord ++ tailWord_2731626).sum := by decide
  have hdescent : baseEnd_2731626 < baseStart_2731626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731685 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 9]
def baseStart_2731685 : Nat := 118140960795 + 2731685 * 2 ^ 59
def prefixEnd_2731685 : Nat := 4983230072969 + 3 ^ 40 * 2731685 * 2
def baseEnd_2731685 : Nat := 155851933519694444841635

theorem tailTrace_2731685 : CollatzResearch.WordTrace tailWord_2731685 prefixEnd_2731685 155851933519694444841635 := by
  unfold tailWord_2731685
  simp only [CollatzResearch.WordTrace]
  refine ⟨99632737108579254500388509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66421824739052836333592339 99632737108579254500388509)
  ·
    refine ⟨37362276415717220437645691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99632737108579254500388509 37362276415717220437645691)
    ·
      refine ⟨56043414623575830656468537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37362276415717220437645691 56043414623575830656468537)
      ·
        refine ⟨42032560967681872992351403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56043414623575830656468537 42032560967681872992351403)
        ·
          refine ⟨63048841451522809488527105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42032560967681872992351403 63048841451522809488527105)
          ·
            refine ⟨47286631088642107116395329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63048841451522809488527105 47286631088642107116395329)
            ·
              refine ⟨35464973316481580337296497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47286631088642107116395329 35464973316481580337296497)
              ·
                refine ⟨26598729987361185252972373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35464973316481580337296497 26598729987361185252972373)
                ·
                  refine ⟨155851933519694444841635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26598729987361185252972373 155851933519694444841635)
                  ·
                    rfl

theorem cell23_2731685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 9].length) (baseStart_2731685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731685 prefixEnd_2731685 := by exact prefixLift 2731685
  have htrace : WordTrace (prefixWord ++ tailWord_2731685) baseStart_2731685 baseEnd_2731685 := by
    simpa [prefixWord, tailWord_2731685, baseEnd_2731685] using wordTrace_append hprefix tailTrace_2731685
  have hstable : (prefixWord ++ tailWord_2731685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731685).length < 2 ^ (prefixWord ++ tailWord_2731685).sum := by decide
  have hdescent : baseEnd_2731685 < baseStart_2731685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731695 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 7]
def baseStart_2731695 : Nat := 118140960795 + 2731695 * 2 ^ 59
def prefixEnd_2731695 : Nat := 4983230072969 + 3 ^ 40 * 2731695 * 2
def baseEnd_2731695 : Nat := 1402672536483794964449669

theorem tailTrace_2731695 : CollatzResearch.WordTrace tailWord_2731695 prefixEnd_2731695 1402672536483794964449669 := by
  unfold tailWord_2731695
  simp only [CollatzResearch.WordTrace]
  refine ⟨99633101838543026208252539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66422067892362017472168359 99633101838543026208252539)
  ·
    refine ⟨149449652757814539312378809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99633101838543026208252539 149449652757814539312378809)
    ·
      refine ⟨112087239568360904484284107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149449652757814539312378809 112087239568360904484284107)
      ·
        refine ⟨168130859352541356726426161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112087239568360904484284107 168130859352541356726426161)
        ·
          refine ⟨126098144514406017544819621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168130859352541356726426161 126098144514406017544819621)
          ·
            refine ⟨23643402096451128289653679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126098144514406017544819621 23643402096451128289653679)
            ·
              refine ⟨35465103144676692434480519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23643402096451128289653679 35465103144676692434480519)
              ·
                refine ⟨53197654717015038651720779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35465103144676692434480519 53197654717015038651720779)
                ·
                  refine ⟨79796482075522557977581169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53197654717015038651720779 79796482075522557977581169)
                  ·
                    refine ⟨59847361556641918483185877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79796482075522557977581169 59847361556641918483185877)
                    ·
                      refine ⟨1402672536483794964449669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59847361556641918483185877 1402672536483794964449669)
                      ·
                        rfl

theorem cell23_2731695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 7].length) (baseStart_2731695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731695 prefixEnd_2731695 := by exact prefixLift 2731695
  have htrace : WordTrace (prefixWord ++ tailWord_2731695) baseStart_2731695 baseEnd_2731695 := by
    simpa [prefixWord, tailWord_2731695, baseEnd_2731695] using wordTrace_append hprefix tailTrace_2731695
  have hstable : (prefixWord ++ tailWord_2731695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731695).length < 2 ^ (prefixWord ++ tailWord_2731695).sum := by decide
  have hdescent : baseEnd_2731695 < baseStart_2731695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731712 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 3]
def baseStart_2731712 : Nat := 118140960795 + 2731712 * 2 ^ 59
def prefixEnd_2731712 : Nat := 4983230072969 + 3 ^ 40 * 2731712 * 2
def baseEnd_2731712 : Nat := 1402681265654921397937091

theorem tailTrace_2731712 : CollatzResearch.WordTrace tailWord_2731712 prefixEnd_2731712 1402681265654921397937091 := by
  unfold tailWord_2731712
  simp only [CollatzResearch.WordTrace]
  refine ⟨49816860939740719055810695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66422481252987625407747593 49816860939740719055810695)
  ·
    refine ⟨74725291409611078583716043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49816860939740719055810695 74725291409611078583716043)
    ·
      refine ⟨112087937114416617875574065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74725291409611078583716043 112087937114416617875574065)
      ·
        refine ⟨84065952835812463406680549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112087937114416617875574065 84065952835812463406680549)
        ·
          refine ⟨15762366156714836888752603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84065952835812463406680549 15762366156714836888752603)
          ·
            refine ⟨23643549235072255333128905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15762366156714836888752603 23643549235072255333128905)
            ·
              refine ⟨17732661926304191499846679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23643549235072255333128905 17732661926304191499846679)
              ·
                refine ⟨26598992889456287249770019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17732661926304191499846679 26598992889456287249770019)
                ·
                  refine ⟨39898489334184430874655029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26598992889456287249770019 39898489334184430874655029)
                  ·
                    refine ⟨3740483375079790394498909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39898489334184430874655029 3740483375079790394498909)
                    ·
                      refine ⟨1402681265654921397937091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3740483375079790394498909 1402681265654921397937091)
                      ·
                        rfl

theorem cell23_2731712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 3].length) (baseStart_2731712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731712 prefixEnd_2731712 := by exact prefixLift 2731712
  have htrace : WordTrace (prefixWord ++ tailWord_2731712) baseStart_2731712 baseEnd_2731712 := by
    simpa [prefixWord, tailWord_2731712, baseEnd_2731712] using wordTrace_append hprefix tailTrace_2731712
  have hstable : (prefixWord ++ tailWord_2731712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731712).length < 2 ^ (prefixWord ++ tailWord_2731712).sum := by decide
  have hdescent : baseEnd_2731712 < baseStart_2731712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731783 : List Nat := [1, 1, 4, 4, 3, 1, 1, 1, 2, 5]
def baseStart_2731783 : Nat := 118140960795 + 2731783 * 2 ^ 59
def prefixEnd_2731783 : Nat := 4983230072969 + 3 ^ 40 * 2731783 * 2
def baseEnd_2731783 : Nat := 467572574260463540049755

theorem tailTrace_2731783 : CollatzResearch.WordTrace tailWord_2731783 prefixEnd_2731783 467572574260463540049755 := by
  unfold tailWord_2731783
  simp only [CollatzResearch.WordTrace]
  refine ⟨99636311462224217237456003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66424207641482811491637335 99636311462224217237456003)
  ·
    refine ⟨149454467193336325856184005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99636311462224217237456003 149454467193336325856184005)
    ·
      refine ⟨28022712598750561098034501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149454467193336325856184005 28022712598750561098034501)
      ·
        refine ⟨5254258612265730205881469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28022712598750561098034501 5254258612265730205881469)
        ·
          refine ⟨1970346979599648827205551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5254258612265730205881469 1970346979599648827205551)
          ·
            refine ⟨2955520469399473240808327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1970346979599648827205551 2955520469399473240808327)
            ·
              refine ⟨4433280704099209861212491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2955520469399473240808327 4433280704099209861212491)
              ·
                refine ⟨6649921056148814791818737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4433280704099209861212491 6649921056148814791818737)
                ·
                  refine ⟨4987440792111611093864053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6649921056148814791818737 4987440792111611093864053)
                  ·
                    refine ⟨467572574260463540049755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4987440792111611093864053 467572574260463540049755)
                    ·
                      rfl

theorem cell23_2731783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_2731783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731783 prefixEnd_2731783 := by exact prefixLift 2731783
  have htrace : WordTrace (prefixWord ++ tailWord_2731783) baseStart_2731783 baseEnd_2731783 := by
    simpa [prefixWord, tailWord_2731783, baseEnd_2731783] using wordTrace_append hprefix tailTrace_2731783
  have hstable : (prefixWord ++ tailWord_2731783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731783).length < 2 ^ (prefixWord ++ tailWord_2731783).sum := by decide
  have hdescent : baseEnd_2731783 < baseStart_2731783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731786 : List Nat := [3, 1, 2, 2, 1, 5, 1, 1, 2, 1, 4]
def baseStart_2731786 : Nat := 118140960795 + 2731786 * 2 ^ 59
def prefixEnd_2731786 : Nat := 4983230072969 + 3 ^ 40 * 2731786 * 2
def baseEnd_2731786 : Nat := 1402719263223354108411751

theorem tailTrace_2731786 : CollatzResearch.WordTrace tailWord_2731786 prefixEnd_2731786 1402719263223354108411751 := by
  unfold tailWord_2731786
  simp only [CollatzResearch.WordTrace]
  refine ⟨24909105220303337187453803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66424280587475565833210141 24909105220303337187453803)
  ·
    refine ⟨37363657830455005781180705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24909105220303337187453803 37363657830455005781180705)
    ·
      refine ⟨28022743372841254335885529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37363657830455005781180705 28022743372841254335885529)
      ·
        refine ⟨21017057529630940751914147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28022743372841254335885529 21017057529630940751914147)
        ·
          refine ⟨31525586294446411127871221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21017057529630940751914147 31525586294446411127871221)
          ·
            refine ⟨2955523715104351043237927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31525586294446411127871221 2955523715104351043237927)
            ·
              refine ⟨4433285572656526564856891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2955523715104351043237927 4433285572656526564856891)
              ·
                refine ⟨6649928358984789847285337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4433285572656526564856891 6649928358984789847285337)
                ·
                  refine ⟨4987446269238592385464003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6649928358984789847285337 4987446269238592385464003)
                  ·
                    refine ⟨7481169403857888578196005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4987446269238592385464003 7481169403857888578196005)
                    ·
                      refine ⟨1402719263223354108411751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7481169403857888578196005 1402719263223354108411751)
                      ·
                        rfl

theorem cell23_2731786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_2731786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731786 prefixEnd_2731786 := by exact prefixLift 2731786
  have htrace : WordTrace (prefixWord ++ tailWord_2731786) baseStart_2731786 baseEnd_2731786 := by
    simpa [prefixWord, tailWord_2731786, baseEnd_2731786] using wordTrace_append hprefix tailTrace_2731786
  have hstable : (prefixWord ++ tailWord_2731786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731786).length < 2 ^ (prefixWord ++ tailWord_2731786).sum := by decide
  have hdescent : baseEnd_2731786 < baseStart_2731786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731809 : List Nat := [1, 2, 3, 2, 1, 3, 3, 2, 6]
def baseStart_2731809 : Nat := 118140960795 + 2731809 * 2 ^ 59
def prefixEnd_2731809 : Nat := 4983230072969 + 3 ^ 40 * 2731809 * 2
def baseEnd_2731809 : Nat := 155859008142045279824905

theorem tailTrace_2731809 : CollatzResearch.WordTrace tailWord_2731809 prefixEnd_2731809 155859008142045279824905 := by
  unfold tailWord_2731809
  simp only [CollatzResearch.WordTrace]
  refine ⟨99637259760130023677902481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66424839840086682451934987 99637259760130023677902481)
  ·
    refine ⟨74727944820097517758426861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99637259760130023677902481 74727944820097517758426861)
    ·
      refine ⟨28022979307536569159410073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74727944820097517758426861 28022979307536569159410073)
      ·
        refine ⟨21017234480652426869557555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28022979307536569159410073 21017234480652426869557555)
        ·
          refine ⟨31525851720978640304336333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21017234480652426869557555 31525851720978640304336333)
          ·
            refine ⟨11822194395366990114126125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31525851720978640304336333 11822194395366990114126125)
            ·
              refine ⟨4433322898262621292797297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11822194395366990114126125 4433322898262621292797297)
              ·
                refine ⟨3324992173696965969597973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4433322898262621292797297 3324992173696965969597973)
                ·
                  refine ⟨155859008142045279824905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3324992173696965969597973 155859008142045279824905)
                  ·
                    rfl

theorem cell23_2731809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 6].length) (baseStart_2731809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731809 prefixEnd_2731809 := by exact prefixLift 2731809
  have htrace : WordTrace (prefixWord ++ tailWord_2731809) baseStart_2731809 baseEnd_2731809 := by
    simpa [prefixWord, tailWord_2731809, baseEnd_2731809] using wordTrace_append hprefix tailTrace_2731809
  have hstable : (prefixWord ++ tailWord_2731809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731809).length < 2 ^ (prefixWord ++ tailWord_2731809).sum := by decide
  have hdescent : baseEnd_2731809 < baseStart_2731809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731826 : List Nat := [3, 2, 1, 1, 3, 3, 3, 1, 6]
def baseStart_2731826 : Nat := 118140960795 + 2731826 * 2 ^ 59
def prefixEnd_2731826 : Nat := 4983230072969 + 3 ^ 40 * 2731826 * 2
def baseEnd_2731826 : Nat := 155859978049948216879063

theorem tailTrace_2731826 : CollatzResearch.WordTrace tailWord_2731826 prefixEnd_2731826 155859978049948216879063 := by
  unfold tailWord_2731826
  simp only [CollatzResearch.WordTrace]
  refine ⟨24909469950267108895317833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66425253200712290387514221 24909469950267108895317833)
  ·
    refine ⟨18682102462700331671488375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24909469950267108895317833 18682102462700331671488375)
    ·
      refine ⟨28023153694050497507232563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18682102462700331671488375 28023153694050497507232563)
      ·
        refine ⟨42034730541075746260848845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28023153694050497507232563 42034730541075746260848845)
        ·
          refine ⟨15763023952903404847818317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42034730541075746260848845 15763023952903404847818317)
          ·
            refine ⟨5911133982338776817931869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15763023952903404847818317 5911133982338776817931869)
            ·
              refine ⟨2216675243377041306724451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5911133982338776817931869 2216675243377041306724451)
              ·
                refine ⟨3325012865065561960086677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2216675243377041306724451 3325012865065561960086677)
                ·
                  refine ⟨155859978049948216879063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3325012865065561960086677 155859978049948216879063)
                  ·
                    rfl

theorem cell23_2731826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 6].length) (baseStart_2731826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731826 prefixEnd_2731826 := by exact prefixLift 2731826
  have htrace : WordTrace (prefixWord ++ tailWord_2731826) baseStart_2731826 baseEnd_2731826 := by
    simpa [prefixWord, tailWord_2731826, baseEnd_2731826] using wordTrace_append hprefix tailTrace_2731826
  have hstable : (prefixWord ++ tailWord_2731826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731826).length < 2 ^ (prefixWord ++ tailWord_2731826).sum := by decide
  have hdescent : baseEnd_2731826 < baseStart_2731826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731836 : List Nat := [2, 2, 2, 2, 1, 1, 4, 2, 3, 1, 3]
def baseStart_2731836 : Nat := 118140960795 + 2731836 * 2 ^ 59
def prefixEnd_2731836 : Nat := 4983230072969 + 3 ^ 40 * 2731836 * 2
def baseEnd_2731836 : Nat := 1402744937256078912786521

theorem tailTrace_2731836 : CollatzResearch.WordTrace tailWord_2731836 prefixEnd_2731836 1402744937256078912786521 := by
  unfold tailWord_2731836
  simp only [CollatzResearch.WordTrace]
  refine ⟨49819122265516103644567681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66425496354021471526090241 49819122265516103644567681)
  ·
    refine ⟨37364341699137077733425761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49819122265516103644567681 37364341699137077733425761)
    ·
      refine ⟨28023256274352808300069321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37364341699137077733425761 28023256274352808300069321)
      ·
        refine ⟨21017442205764606225051991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28023256274352808300069321 21017442205764606225051991)
        ·
          refine ⟨31526163308646909337577987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21017442205764606225051991 31526163308646909337577987)
          ·
            refine ⟨47289244962970364006366981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31526163308646909337577987 47289244962970364006366981)
            ·
              refine ⟨8866733430556943251193809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47289244962970364006366981 8866733430556943251193809)
              ·
                refine ⟨6650050072917707438395357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8866733430556943251193809 6650050072917707438395357)
                ·
                  refine ⟨2493768777344140289398259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6650050072917707438395357 2493768777344140289398259)
                  ·
                    refine ⟨3740653166016210434097389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2493768777344140289398259 3740653166016210434097389)
                    ·
                      refine ⟨1402744937256078912786521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3740653166016210434097389 1402744937256078912786521)
                      ·
                        rfl

theorem cell23_2731836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_2731836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731836 prefixEnd_2731836 := by exact prefixLift 2731836
  have htrace : WordTrace (prefixWord ++ tailWord_2731836) baseStart_2731836 baseEnd_2731836 := by
    simpa [prefixWord, tailWord_2731836, baseEnd_2731836] using wordTrace_append hprefix tailTrace_2731836
  have hstable : (prefixWord ++ tailWord_2731836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731836).length < 2 ^ (prefixWord ++ tailWord_2731836).sum := by decide
  have hdescent : baseEnd_2731836 < baseStart_2731836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731863 : List Nat := [1, 1, 3, 2, 5, 1, 1, 2, 2, 3, 2]
def baseStart_2731863 : Nat := 118140960795 + 2731863 * 2 ^ 59
def prefixEnd_2731863 : Nat := 4983230072969 + 3 ^ 40 * 2731863 * 2
def baseEnd_2731863 : Nat := 1402758801233750307148897

theorem tailTrace_2731863 : CollatzResearch.WordTrace tailWord_2731863 prefixEnd_2731863 1402758801233750307148897 := by
  unfold tailWord_2731863
  simp only [CollatzResearch.WordTrace]
  refine ⟨99639229301934390900368243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66426152867956260600245495 99639229301934390900368243)
  ·
    refine ⟨149458843952901586350552365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99639229301934390900368243 149458843952901586350552365)
    ·
      refine ⟨56047066482338094881457137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149458843952901586350552365 56047066482338094881457137)
      ·
        refine ⟨42035299861753571161092853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56047066482338094881457137 42035299861753571161092853)
        ·
          refine ⟨3940809362039397296352455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42035299861753571161092853 3940809362039397296352455)
          ·
            refine ⟨5911214043059095944528683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3940809362039397296352455 5911214043059095944528683)
            ·
              refine ⟨8866821064588643916793025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5911214043059095944528683 8866821064588643916793025)
              ·
                refine ⟨6650115798441482937594769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8866821064588643916793025 6650115798441482937594769)
                ·
                  refine ⟨4987586848831112203196077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6650115798441482937594769 4987586848831112203196077)
                  ·
                    refine ⟨1870345068311667076198529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4987586848831112203196077 1870345068311667076198529)
                    ·
                      refine ⟨1402758801233750307148897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1870345068311667076198529 1402758801233750307148897)
                      ·
                        rfl

theorem cell23_2731863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 3, 2].length) (baseStart_2731863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731863 prefixEnd_2731863 := by exact prefixLift 2731863
  have htrace : WordTrace (prefixWord ++ tailWord_2731863) baseStart_2731863 baseEnd_2731863 := by
    simpa [prefixWord, tailWord_2731863, baseEnd_2731863] using wordTrace_append hprefix tailTrace_2731863
  have hstable : (prefixWord ++ tailWord_2731863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731863).length < 2 ^ (prefixWord ++ tailWord_2731863).sum := by decide
  have hdescent : baseEnd_2731863 < baseStart_2731863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731879 : List Nat := [1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 5]
def baseStart_2731879 : Nat := 118140960795 + 2731879 * 2 ^ 59
def prefixEnd_2731879 : Nat := 4983230072969 + 3 ^ 40 * 2731879 * 2
def baseEnd_2731879 : Nat := 1402767016924222244548823

theorem tailTrace_2731879 : CollatzResearch.WordTrace tailWord_2731879 prefixEnd_2731879 1402767016924222244548823 := by
  unfold tailWord_2731879
  simp only [CollatzResearch.WordTrace]
  refine ⟨99639812869876425632950691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66426541913250950421967127 99639812869876425632950691)
  ·
    refine ⟨149459719304814638449426037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99639812869876425632950691 149459719304814638449426037)
    ·
      refine ⟨14011848684826372354633691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149459719304814638449426037 14011848684826372354633691)
      ·
        refine ⟨21017773027239558531950537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14011848684826372354633691 21017773027239558531950537)
        ·
          refine ⟨15763329770429668898962903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21017773027239558531950537 15763329770429668898962903)
          ·
            refine ⟨23644994655644503348444355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15763329770429668898962903 23644994655644503348444355)
            ·
              refine ⟨35467491983466755022666533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23644994655644503348444355 35467491983466755022666533)
              ·
                refine ⟨6650154746900016566749975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35467491983466755022666533 6650154746900016566749975)
                ·
                  refine ⟨9975232120350024850124963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6650154746900016566749975 9975232120350024850124963)
                  ·
                    refine ⟨14962848180525037275187445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9975232120350024850124963 14962848180525037275187445)
                    ·
                      refine ⟨1402767016924222244548823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14962848180525037275187445 1402767016924222244548823)
                      ·
                        rfl

theorem cell23_2731879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_2731879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731879 prefixEnd_2731879 := by exact prefixLift 2731879
  have htrace : WordTrace (prefixWord ++ tailWord_2731879) baseStart_2731879 baseEnd_2731879 := by
    simpa [prefixWord, tailWord_2731879, baseEnd_2731879] using wordTrace_append hprefix tailTrace_2731879
  have hstable : (prefixWord ++ tailWord_2731879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731879).length < 2 ^ (prefixWord ++ tailWord_2731879).sum := by decide
  have hdescent : baseEnd_2731879 < baseStart_2731879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731889 : List Nat := [1, 2, 2, 2, 1, 3, 2, 3, 1, 2, 4]
def baseStart_2731889 : Nat := 118140960795 + 2731889 * 2 ^ 59
def prefixEnd_2731889 : Nat := 4983230072969 + 3 ^ 40 * 2731889 * 2
def baseEnd_2731889 : Nat := 1402772151730767205423777

theorem tailTrace_2731889 : CollatzResearch.WordTrace tailWord_2731889 prefixEnd_2731889 1402772151730767205423777 := by
  unfold tailWord_2731889
  simp only [CollatzResearch.WordTrace]
  refine ⟨99640177599840197340814721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66426785066560131560543147 99640177599840197340814721)
  ·
    refine ⟨74730133199880148005611041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99640177599840197340814721 74730133199880148005611041)
    ·
      refine ⟨56047599899910111004208281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74730133199880148005611041 56047599899910111004208281)
      ·
        refine ⟨42035699924932583253156211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56047599899910111004208281 42035699924932583253156211)
        ·
          refine ⟨63053549887398874879734317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42035699924932583253156211 63053549887398874879734317)
          ·
            refine ⟨23645081207774578079900369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63053549887398874879734317 23645081207774578079900369)
            ·
              refine ⟨17733810905830933559925277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23645081207774578079900369 17733810905830933559925277)
              ·
                refine ⟨6650179089686600084971979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17733810905830933559925277 6650179089686600084971979)
                ·
                  refine ⟨9975268634529900127457969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6650179089686600084971979 9975268634529900127457969)
                  ·
                    refine ⟨7481451475897425095593477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9975268634529900127457969 7481451475897425095593477)
                    ·
                      refine ⟨1402772151730767205423777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7481451475897425095593477 1402772151730767205423777)
                      ·
                        rfl

theorem cell23_2731889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_2731889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731889 prefixEnd_2731889 := by exact prefixLift 2731889
  have htrace : WordTrace (prefixWord ++ tailWord_2731889) baseStart_2731889 baseEnd_2731889 := by
    simpa [prefixWord, tailWord_2731889, baseEnd_2731889] using wordTrace_append hprefix tailTrace_2731889
  have hstable : (prefixWord ++ tailWord_2731889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731889).length < 2 ^ (prefixWord ++ tailWord_2731889).sum := by decide
  have hdescent : baseEnd_2731889 < baseStart_2731889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731893 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 5, 2, 2]
def baseStart_2731893 : Nat := 118140960795 + 2731893 * 2 ^ 59
def prefixEnd_2731893 : Nat := 4983230072969 + 3 ^ 40 * 2731893 * 2
def baseEnd_2731893 : Nat := 1402774205653385189773759

theorem tailTrace_2731893 : CollatzResearch.WordTrace tailWord_2731893 prefixEnd_2731893 1402774205653385189773759 := by
  unfold tailWord_2731893
  simp only [CollatzResearch.WordTrace]
  refine ⟨99640323491825706023960333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66426882327883804015973555 99640323491825706023960333)
  ·
    refine ⟨37365121309434639758985125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99640323491825706023960333 37365121309434639758985125)
    ·
      refine ⟨7005960245518994954809711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37365121309434639758985125 7005960245518994954809711)
      ·
        refine ⟨10508940368278492432214567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7005960245518994954809711 10508940368278492432214567)
        ·
          refine ⟨15763410552417738648321851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10508940368278492432214567 15763410552417738648321851)
          ·
            refine ⟨23645115828626607972482777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15763410552417738648321851 23645115828626607972482777)
            ·
              refine ⟨17733836871469955979362083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23645115828626607972482777 17733836871469955979362083)
              ·
                refine ⟨26600755307204933969043125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17733836871469955979362083 26600755307204933969043125)
                ·
                  refine ⟨2493820810050462559597793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26600755307204933969043125 2493820810050462559597793)
                  ·
                    refine ⟨1870365607537846919698345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2493820810050462559597793 1870365607537846919698345)
                    ·
                      refine ⟨1402774205653385189773759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1870365607537846919698345 1402774205653385189773759)
                      ·
                        rfl

theorem cell23_2731893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_2731893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731893 prefixEnd_2731893 := by exact prefixLift 2731893
  have htrace : WordTrace (prefixWord ++ tailWord_2731893) baseStart_2731893 baseEnd_2731893 := by
    simpa [prefixWord, tailWord_2731893, baseEnd_2731893] using wordTrace_append hprefix tailTrace_2731893
  have hstable : (prefixWord ++ tailWord_2731893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731893).length < 2 ^ (prefixWord ++ tailWord_2731893).sum := by decide
  have hdescent : baseEnd_2731893 < baseStart_2731893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731913 : List Nat := [1, 2, 1, 1, 5, 1, 5, 1, 1, 2, 3]
def baseStart_2731913 : Nat := 118140960795 + 2731913 * 2 ^ 59
def prefixEnd_2731913 : Nat := 4983230072969 + 3 ^ 40 * 2731913 * 2
def baseEnd_2731913 : Nat := 1402784475266475111523667

theorem tailTrace_2731913 : CollatzResearch.WordTrace tailWord_2731913 prefixEnd_2731913 1402784475266475111523667 := by
  unfold tailWord_2731913
  simp only [CollatzResearch.WordTrace]
  refine ⟨99641052951753249439688393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66427368634502166293125595 99641052951753249439688393)
  ·
    refine ⟨74730789713814937079766295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99641052951753249439688393 74730789713814937079766295)
    ·
      refine ⟨112096184570722405619649443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74730789713814937079766295 112096184570722405619649443)
      ·
        refine ⟨168144276856083608429474165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112096184570722405619649443 168144276856083608429474165)
        ·
          refine ⟨15763525955257838290263203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 168144276856083608429474165 15763525955257838290263203)
          ·
            refine ⟨23645288932886757435394805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15763525955257838290263203 23645288932886757435394805)
            ·
              refine ⟨2216745837458133509568263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23645288932886757435394805 2216745837458133509568263)
              ·
                refine ⟨3325118756187200264352395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2216745837458133509568263 3325118756187200264352395)
                ·
                  refine ⟨4987678134280800396528593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3325118756187200264352395 4987678134280800396528593)
                  ·
                    refine ⟨3740758600710600297396445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4987678134280800396528593 3740758600710600297396445)
                    ·
                      refine ⟨1402784475266475111523667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3740758600710600297396445 1402784475266475111523667)
                      ·
                        rfl

theorem cell23_2731913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 1, 2, 3].length) (baseStart_2731913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731913 prefixEnd_2731913 := by exact prefixLift 2731913
  have htrace : WordTrace (prefixWord ++ tailWord_2731913) baseStart_2731913 baseEnd_2731913 := by
    simpa [prefixWord, tailWord_2731913, baseEnd_2731913] using wordTrace_append hprefix tailTrace_2731913
  have hstable : (prefixWord ++ tailWord_2731913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731913).length < 2 ^ (prefixWord ++ tailWord_2731913).sum := by decide
  have hdescent : baseEnd_2731913 < baseStart_2731913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731927 : List Nat := [1, 1, 3, 3, 1, 3, 4, 2, 1, 2, 2]
def baseStart_2731927 : Nat := 118140960795 + 2731927 * 2 ^ 59
def prefixEnd_2731927 : Nat := 4983230072969 + 3 ^ 40 * 2731927 * 2
def baseEnd_2731927 : Nat := 1402791663995638056748603

theorem tailTrace_2731927 : CollatzResearch.WordTrace tailWord_2731927 prefixEnd_2731927 1402791663995638056748603 := by
  unfold tailWord_2731927
  simp only [CollatzResearch.WordTrace]
  refine ⟨99641563573702529830698035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66427709049135019887132023 99641563573702529830698035)
  ·
    refine ⟨149462345360553794746047053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99641563573702529830698035 149462345360553794746047053)
    ·
      refine ⟨56048379510207673029767645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149462345360553794746047053 56048379510207673029767645)
      ·
        refine ⟨21018142316327877386162867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56048379510207673029767645 21018142316327877386162867)
        ·
          refine ⟨31527213474491816079244301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21018142316327877386162867 31527213474491816079244301)
          ·
            refine ⟨11822705052934431029716613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31527213474491816079244301 11822705052934431029716613)
            ·
              refine ⟨2216757197425205818071865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11822705052934431029716613 2216757197425205818071865)
              ·
                refine ⟨1662567898068904363553899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2216757197425205818071865 1662567898068904363553899)
                ·
                  refine ⟨2493851847103356545330849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1662567898068904363553899 2493851847103356545330849)
                  ·
                    refine ⟨1870388885327517408998137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2493851847103356545330849 1870388885327517408998137)
                    ·
                      refine ⟨1402791663995638056748603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1870388885327517408998137 1402791663995638056748603)
                      ·
                        rfl

theorem cell23_2731927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_2731927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731927 prefixEnd_2731927 := by exact prefixLift 2731927
  have htrace : WordTrace (prefixWord ++ tailWord_2731927) baseStart_2731927 baseEnd_2731927 := by
    simpa [prefixWord, tailWord_2731927, baseEnd_2731927] using wordTrace_append hprefix tailTrace_2731927
  have hstable : (prefixWord ++ tailWord_2731927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731927).length < 2 ^ (prefixWord ++ tailWord_2731927).sum := by decide
  have hdescent : baseEnd_2731927 < baseStart_2731927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731943 : List Nat := [1, 1, 6, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_2731943 : Nat := 118140960795 + 2731943 * 2 ^ 59
def prefixEnd_2731943 : Nat := 4983230072969 + 3 ^ 40 * 2731943 * 2
def baseEnd_2731943 : Nat := 1402799879686109994148529

theorem tailTrace_2731943 : CollatzResearch.WordTrace tailWord_2731943 prefixEnd_2731943 1402799879686109994148529 := by
  unfold tailWord_2731943
  simp only [CollatzResearch.WordTrace]
  refine ⟨99642147141644564563280483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66428098094429709708853655 99642147141644564563280483)
  ·
    refine ⟨149463220712466846844920725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99642147141644564563280483 149463220712466846844920725)
    ·
      refine ⟨7006088470896883445855659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 149463220712466846844920725 7006088470896883445855659)
      ·
        refine ⟨10509132706345325168783489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7006088470896883445855659 10509132706345325168783489)
        ·
          refine ⟨7881849529758993876587617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10509132706345325168783489 7881849529758993876587617)
          ·
            refine ⟨5911387147319245407440713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7881849529758993876587617 5911387147319245407440713)
            ·
              refine ⟨4433540360489434055580535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5911387147319245407440713 4433540360489434055580535)
              ·
                refine ⟨6650310540734151083370803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4433540360489434055580535 6650310540734151083370803)
                ·
                  refine ⟨9975465811101226625056205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6650310540734151083370803 9975465811101226625056205)
                  ·
                    refine ⟨3740799679162959984396077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9975465811101226625056205 3740799679162959984396077)
                    ·
                      refine ⟨1402799879686109994148529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3740799679162959984396077 1402799879686109994148529)
                      ·
                        rfl

theorem cell23_2731943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_2731943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731943 prefixEnd_2731943 := by exact prefixLift 2731943
  have htrace : WordTrace (prefixWord ++ tailWord_2731943) baseStart_2731943 baseEnd_2731943 := by
    simpa [prefixWord, tailWord_2731943, baseEnd_2731943] using wordTrace_append hprefix tailTrace_2731943
  have hstable : (prefixWord ++ tailWord_2731943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731943).length < 2 ^ (prefixWord ++ tailWord_2731943).sum := by decide
  have hdescent : baseEnd_2731943 < baseStart_2731943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731953 : List Nat := [1, 2, 2, 4, 2, 1, 2, 1, 3, 3, 2]
def baseStart_2731953 : Nat := 118140960795 + 2731953 * 2 ^ 59
def prefixEnd_2731953 : Nat := 4983230072969 + 3 ^ 40 * 2731953 * 2
def baseEnd_2731953 : Nat := 1402805014492654955023483

theorem tailTrace_2731953 : CollatzResearch.WordTrace tailWord_2731953 prefixEnd_2731953 1402805014492654955023483 := by
  unfold tailWord_2731953
  simp only [CollatzResearch.WordTrace]
  refine ⟨99642511871608336271144513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66428341247738890847429675 99642511871608336271144513)
  ·
    refine ⟨74731883903706252203358385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99642511871608336271144513 74731883903706252203358385)
    ·
      refine ⟨56048912927779689152518789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74731883903706252203358385 56048912927779689152518789)
      ·
        refine ⟨10509171173958691716097273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56048912927779689152518789 10509171173958691716097273)
        ·
          refine ⟨7881878380469018787072955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10509171173958691716097273 7881878380469018787072955)
          ·
            refine ⟨11822817570703528180609433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7881878380469018787072955 11822817570703528180609433)
            ·
              refine ⟨8867113178027646135457075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11822817570703528180609433 8867113178027646135457075)
              ·
                refine ⟨13300669767041469203185613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8867113178027646135457075 13300669767041469203185613)
                ·
                  refine ⟨4987751162640550951194605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13300669767041469203185613 4987751162640550951194605)
                  ·
                    refine ⟨1870406685990206606697977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4987751162640550951194605 1870406685990206606697977)
                    ·
                      refine ⟨1402805014492654955023483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1870406685990206606697977 1402805014492654955023483)
                      ·
                        rfl

theorem cell23_2731953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_2731953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731953 prefixEnd_2731953 := by exact prefixLift 2731953
  have htrace : WordTrace (prefixWord ++ tailWord_2731953) baseStart_2731953 baseEnd_2731953 := by
    simpa [prefixWord, tailWord_2731953, baseEnd_2731953] using wordTrace_append hprefix tailTrace_2731953
  have hstable : (prefixWord ++ tailWord_2731953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731953).length < 2 ^ (prefixWord ++ tailWord_2731953).sum := by decide
  have hdescent : baseEnd_2731953 < baseStart_2731953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731964 : List Nat := [2, 2, 2, 5, 2, 1, 2, 1, 1, 2, 3]
def baseStart_2731964 : Nat := 118140960795 + 2731964 * 2 ^ 59
def prefixEnd_2731964 : Nat := 4983230072969 + 3 ^ 40 * 2731964 * 2
def baseEnd_2731964 : Nat := 1402810662779854411985933

theorem tailTrace_2731964 : CollatzResearch.WordTrace tailWord_2731964 prefixEnd_2731964 1402810662779854411985933 := by
  unfold tailWord_2731964
  simp only [CollatzResearch.WordTrace]
  refine ⟨49821456537284242574897473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66428608716378990099863297 49821456537284242574897473)
  ·
    refine ⟨37366092402963181931173105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49821456537284242574897473 37366092402963181931173105)
    ·
      refine ⟨28024569302222386448379829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37366092402963181931173105 28024569302222386448379829)
      ·
        refine ⟨2627303372083348729535609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28024569302222386448379829 2627303372083348729535609)
        ·
          refine ⟨1970477529062511547151707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2627303372083348729535609 1970477529062511547151707)
          ·
            refine ⟨2955716293593767320727561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1970477529062511547151707 2955716293593767320727561)
            ·
              refine ⟨2216787220195325490545671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2955716293593767320727561 2216787220195325490545671)
              ·
                refine ⟨3325180830292988235818507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2216787220195325490545671 3325180830292988235818507)
                ·
                  refine ⟨4987771245439482353727761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3325180830292988235818507 4987771245439482353727761)
                  ·
                    refine ⟨3740828434079611765295821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4987771245439482353727761 3740828434079611765295821)
                    ·
                      refine ⟨1402810662779854411985933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3740828434079611765295821 1402810662779854411985933)
                      ·
                        rfl

theorem cell23_2731964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_2731964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731964 prefixEnd_2731964 := by exact prefixLift 2731964
  have htrace : WordTrace (prefixWord ++ tailWord_2731964) baseStart_2731964 baseEnd_2731964 := by
    simpa [prefixWord, tailWord_2731964, baseEnd_2731964] using wordTrace_append hprefix tailTrace_2731964
  have hstable : (prefixWord ++ tailWord_2731964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731964).length < 2 ^ (prefixWord ++ tailWord_2731964).sum := by decide
  have hdescent : baseEnd_2731964 < baseStart_2731964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731979 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 4]
def baseStart_2731979 : Nat := 118140960795 + 2731979 * 2 ^ 59
def prefixEnd_2731979 : Nat := 4983230072969 + 3 ^ 40 * 2731979 * 2
def baseEnd_2731979 : Nat := 1402818364989671853298363

theorem tailTrace_2731979 : CollatzResearch.WordTrace tailWord_2731979 prefixEnd_2731979 1402818364989671853298363 := by
  unfold tailWord_2731979
  simp only [CollatzResearch.WordTrace]
  refine ⟨99643460169514142711590991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66428973446342761807727327 99643460169514142711590991)
  ·
    refine ⟨149465190254271214067386487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99643460169514142711590991 149465190254271214067386487)
    ·
      refine ⟨224197785381406821101079731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149465190254271214067386487 224197785381406821101079731)
      ·
        refine ⟨336296678072110231651619597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224197785381406821101079731 336296678072110231651619597)
        ·
          refine ⟨126111254277041336869357349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 336296678072110231651619597 126111254277041336869357349)
          ·
            refine ⟨23645860176945250663004503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126111254277041336869357349 23645860176945250663004503)
            ·
              refine ⟨35468790265417875994506755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23645860176945250663004503 35468790265417875994506755)
              ·
                refine ⟨53203185398126813991760133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35468790265417875994506755 53203185398126813991760133)
                ·
                  refine ⟨9975597262148777623455025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53203185398126813991760133 9975597262148777623455025)
                  ·
                    refine ⟨7481697946611583217591269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9975597262148777623455025 7481697946611583217591269)
                    ·
                      refine ⟨1402818364989671853298363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7481697946611583217591269 1402818364989671853298363)
                      ·
                        rfl

theorem cell23_2731979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 4].length) (baseStart_2731979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731979 prefixEnd_2731979 := by exact prefixLift 2731979
  have htrace : WordTrace (prefixWord ++ tailWord_2731979) baseStart_2731979 baseEnd_2731979 := by
    simpa [prefixWord, tailWord_2731979, baseEnd_2731979] using wordTrace_append hprefix tailTrace_2731979
  have hstable : (prefixWord ++ tailWord_2731979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731979).length < 2 ^ (prefixWord ++ tailWord_2731979).sum := by decide
  have hdescent : baseEnd_2731979 < baseStart_2731979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731983 : List Nat := [1, 1, 2, 1, 1, 5, 3, 1, 4, 2, 2]
def baseStart_2731983 : Nat := 118140960795 + 2731983 * 2 ^ 59
def prefixEnd_2731983 : Nat := 4983230072969 + 3 ^ 40 * 2731983 * 2
def baseEnd_2731983 : Nat := 1402820418912289837648345

theorem tailTrace_2731983 : CollatzResearch.WordTrace tailWord_2731983 prefixEnd_2731983 1402820418912289837648345 := by
  unfold tailWord_2731983
  simp only [CollatzResearch.WordTrace]
  refine ⟨99643606061499651394736603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66429070707666434263157735 99643606061499651394736603)
  ·
    refine ⟨149465409092249477092104905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99643606061499651394736603 149465409092249477092104905)
    ·
      refine ⟨112099056819187107819078679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149465409092249477092104905 112099056819187107819078679)
      ·
        refine ⟨168148585228780661728618019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112099056819187107819078679 168148585228780661728618019)
        ·
          refine ⟨252222877843170992592927029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168148585228780661728618019 252222877843170992592927029)
          ·
            refine ⟨23645894797797280555586909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 252222877843170992592927029 23645894797797280555586909)
            ·
              refine ⟨8867210549173980208345091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23645894797797280555586909 8867210549173980208345091)
              ·
                refine ⟨13300815823760970312517637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8867210549173980208345091 13300815823760970312517637)
                ·
                  refine ⟨2493902966955181933597057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13300815823760970312517637 2493902966955181933597057)
                  ·
                    refine ⟨1870427225216386450197793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2493902966955181933597057 1870427225216386450197793)
                    ·
                      refine ⟨1402820418912289837648345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1870427225216386450197793 1402820418912289837648345)
                      ·
                        rfl

theorem cell23_2731983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4, 2, 2].length) (baseStart_2731983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2731983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2731983 prefixEnd_2731983 := by exact prefixLift 2731983
  have htrace : WordTrace (prefixWord ++ tailWord_2731983) baseStart_2731983 baseEnd_2731983 := by
    simpa [prefixWord, tailWord_2731983, baseEnd_2731983] using wordTrace_append hprefix tailTrace_2731983
  have hstable : (prefixWord ++ tailWord_2731983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731983).length < 2 ^ (prefixWord ++ tailWord_2731983).sum := by decide
  have hdescent : baseEnd_2731983 < baseStart_2731983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732019 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 6, 5]
def baseStart_2732019 : Nat := 118140960795 + 2732019 * 2 ^ 59
def prefixEnd_2732019 : Nat := 4983230072969 + 3 ^ 40 * 2732019 * 2
def baseEnd_2732019 : Nat := 467612968071950565599393

theorem tailTrace_2732019 : CollatzResearch.WordTrace tailWord_2732019 prefixEnd_2732019 467612968071950565599393 := by
  unfold tailWord_2732019
  simp only [CollatzResearch.WordTrace]
  refine ⟨99644919089369229543047111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66429946059579486362031407 99644919089369229543047111)
  ·
    refine ⟨149467378634053844314570667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99644919089369229543047111 149467378634053844314570667)
    ·
      refine ⟨224201067951080766471856001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149467378634053844314570667 224201067951080766471856001)
      ·
        refine ⟨168150800963310574853892001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224201067951080766471856001 168150800963310574853892001)
        ·
          refine ⟨126113100722482931140419001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168150800963310574853892001 126113100722482931140419001)
          ·
            refine ⟨94584825541862198355314251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126113100722482931140419001 94584825541862198355314251)
            ·
              refine ⟨141877238312793297532971377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94584825541862198355314251 141877238312793297532971377)
              ·
                refine ⟨106407928734594973149728533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141877238312793297532971377 106407928734594973149728533)
                ·
                  refine ⟨4987871659434139366393525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 106407928734594973149728533 4987871659434139366393525)
                  ·
                    refine ⟨467612968071950565599393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4987871659434139366393525 467612968071950565599393)
                    ·
                      rfl

theorem cell23_2732019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 5].length) (baseStart_2732019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732019 prefixEnd_2732019 := by exact prefixLift 2732019
  have htrace : WordTrace (prefixWord ++ tailWord_2732019) baseStart_2732019 baseEnd_2732019 := by
    simpa [prefixWord, tailWord_2732019, baseEnd_2732019] using wordTrace_append hprefix tailTrace_2732019
  have hstable : (prefixWord ++ tailWord_2732019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732019).length < 2 ^ (prefixWord ++ tailWord_2732019).sum := by decide
  have hdescent : baseEnd_2732019 < baseStart_2732019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732026 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2]
def baseStart_2732026 : Nat := 118140960795 + 2732026 * 2 ^ 59
def prefixEnd_2732026 : Nat := 4983230072969 + 3 ^ 40 * 2732026 * 2
def baseEnd_2732026 : Nat := 1402842498580433169410647

theorem tailTrace_2732026 : CollatzResearch.WordTrace tailWord_2732026 prefixEnd_2732026 1402842498580433169410647 := by
  unfold tailWord_2732026
  simp only [CollatzResearch.WordTrace]
  refine ⟨24911293600085967434637983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66430116266895913159034621 24911293600085967434637983)
  ·
    refine ⟨37366940400128951151956975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24911293600085967434637983 37366940400128951151956975)
    ·
      refine ⟨56050410600193426727935463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37366940400128951151956975 56050410600193426727935463)
      ·
        refine ⟨84075615900290140091903195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56050410600193426727935463 84075615900290140091903195)
        ·
          refine ⟨126113423850435210137854793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84075615900290140091903195 126113423850435210137854793)
          ·
            refine ⟨94585067887826407603391095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126113423850435210137854793 94585067887826407603391095)
            ·
              refine ⟨141877601831739611405086643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94585067887826407603391095 141877601831739611405086643)
              ·
                refine ⟨212816402747609417107629965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141877601831739611405086643 212816402747609417107629965)
                ·
                  refine ⟨79806151030353531415361237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 212816402747609417107629965 79806151030353531415361237)
                  ·
                    refine ⟨1870456664773910892547529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 79806151030353531415361237 1870456664773910892547529)
                    ·
                      refine ⟨1402842498580433169410647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1870456664773910892547529 1402842498580433169410647)
                      ·
                        rfl

theorem cell23_2732026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2].length) (baseStart_2732026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732026 prefixEnd_2732026 := by exact prefixLift 2732026
  have htrace : WordTrace (prefixWord ++ tailWord_2732026) baseStart_2732026 baseEnd_2732026 := by
    simpa [prefixWord, tailWord_2732026, baseEnd_2732026] using wordTrace_append hprefix tailTrace_2732026
  have hstable : (prefixWord ++ tailWord_2732026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732026).length < 2 ^ (prefixWord ++ tailWord_2732026).sum := by decide
  have hdescent : baseEnd_2732026 < baseStart_2732026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732046 : List Nat := [4, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5]
def baseStart_2732046 : Nat := 118140960795 + 2732046 * 2 ^ 59
def prefixEnd_2732046 : Nat := 4983230072969 + 3 ^ 40 * 2732046 * 2
def baseEnd_2732046 : Nat := 1402852768193523091160555

theorem tailTrace_2732046 : CollatzResearch.WordTrace tailWord_2732046 prefixEnd_2732046 1402852768193523091160555 := by
  unfold tailWord_2732046
  simp only [CollatzResearch.WordTrace]
  refine ⟨12455737982533926644284999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66430602573514275436186661 12455737982533926644284999)
  ·
    refine ⟨18683606973800889966427499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12455737982533926644284999 18683606973800889966427499)
    ·
      refine ⟨28025410460701334949641249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18683606973800889966427499 28025410460701334949641249)
      ·
        refine ⟨21019057845526001212230937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28025410460701334949641249 21019057845526001212230937)
        ·
          refine ⟨15764293384144500909173203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21019057845526001212230937 15764293384144500909173203)
          ·
            refine ⟨23646440076216751363759805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15764293384144500909173203 23646440076216751363759805)
            ·
              refine ⟨8867415028581281761409927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23646440076216751363759805 8867415028581281761409927)
              ·
                refine ⟨13301122542871922642114891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8867415028581281761409927 13301122542871922642114891)
                ·
                  refine ⟨19951683814307883963172337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13301122542871922642114891 19951683814307883963172337)
                  ·
                    refine ⟨14963762860730912972379253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19951683814307883963172337 14963762860730912972379253)
                    ·
                      refine ⟨1402852768193523091160555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14963762860730912972379253 1402852768193523091160555)
                      ·
                        rfl

theorem cell23_2732046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_2732046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732046 prefixEnd_2732046 := by exact prefixLift 2732046
  have htrace : WordTrace (prefixWord ++ tailWord_2732046) baseStart_2732046 baseEnd_2732046 := by
    simpa [prefixWord, tailWord_2732046, baseEnd_2732046] using wordTrace_append hprefix tailTrace_2732046
  have hstable : (prefixWord ++ tailWord_2732046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732046).length < 2 ^ (prefixWord ++ tailWord_2732046).sum := by decide
  have hdescent : baseEnd_2732046 < baseStart_2732046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732056 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 4, 1, 4]
def baseStart_2732056 : Nat := 118140960795 + 2732056 * 2 ^ 59
def prefixEnd_2732056 : Nat := 4983230072969 + 3 ^ 40 * 2732056 * 2
def baseEnd_2732056 : Nat := 1402857903000068052035509

theorem tailTrace_2732056 : CollatzResearch.WordTrace tailWord_2732056 prefixEnd_2732056 1402857903000068052035509 := by
  unfold tailWord_2732056
  simp only [CollatzResearch.WordTrace]
  refine ⟨49823134295117592431072011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66430845726823456574762681 49823134295117592431072011)
  ·
    refine ⟨74734701442676388646608017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49823134295117592431072011 74734701442676388646608017)
    ·
      refine ⟨56051026082007291484956013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74734701442676388646608017 56051026082007291484956013)
      ·
        refine ⟨21019134780752734306858505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56051026082007291484956013 21019134780752734306858505)
        ·
          refine ⟨15764351085564550730143879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21019134780752734306858505 15764351085564550730143879)
          ·
            refine ⟨23646526628346826095215819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15764351085564550730143879 23646526628346826095215819)
            ·
              refine ⟨35469789942520239142823729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23646526628346826095215819 35469789942520239142823729)
              ·
                refine ⟨26602342456890179357117797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35469789942520239142823729 26602342456890179357117797)
                ·
                  refine ⟨4987939210666908629459587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26602342456890179357117797 4987939210666908629459587)
                  ·
                    refine ⟨7481908816000362944189381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4987939210666908629459587 7481908816000362944189381)
                    ·
                      refine ⟨1402857903000068052035509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7481908816000362944189381 1402857903000068052035509)
                      ·
                        rfl

theorem cell23_2732056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_2732056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732056 prefixEnd_2732056 := by exact prefixLift 2732056
  have htrace : WordTrace (prefixWord ++ tailWord_2732056) baseStart_2732056 baseEnd_2732056 := by
    simpa [prefixWord, tailWord_2732056, baseEnd_2732056] using wordTrace_append hprefix tailTrace_2732056
  have hstable : (prefixWord ++ tailWord_2732056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732056).length < 2 ^ (prefixWord ++ tailWord_2732056).sum := by decide
  have hdescent : baseEnd_2732056 < baseStart_2732056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732079 : List Nat := [1, 1, 2, 1, 2, 1, 1, 6, 8]
def baseStart_2732079 : Nat := 118140960795 + 2732079 * 2 ^ 59
def prefixEnd_2732079 : Nat := 4983230072969 + 3 ^ 40 * 2732079 * 2
def baseEnd_2732079 : Nat := 155874412561680162449767

theorem tailTrace_2732079 : CollatzResearch.WordTrace tailWord_2732079 prefixEnd_2732079 155874412561680162449767 := by
  unfold tailWord_2732079
  simp only [CollatzResearch.WordTrace]
  refine ⟨99647107469151859790231291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66431404979434573193487527 99647107469151859790231291)
  ·
    refine ⟨149470661203727789685346937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99647107469151859790231291 149470661203727789685346937)
    ·
      refine ⟨112102995902795842264010203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149470661203727789685346937 112102995902795842264010203)
      ·
        refine ⟨168154493854193763396015305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112102995902795842264010203 168154493854193763396015305)
        ·
          refine ⟨126115870390645322547011479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168154493854193763396015305 126115870390645322547011479)
          ·
            refine ⟨189173805585967983820517219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126115870390645322547011479 189173805585967983820517219)
            ·
              refine ⟨283760708378951975730775829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189173805585967983820517219 283760708378951975730775829)
              ·
                refine ⟨13301283205263373862380117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 283760708378951975730775829 13301283205263373862380117)
                ·
                  refine ⟨155874412561680162449767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13301283205263373862380117 155874412561680162449767)
                  ·
                    rfl

theorem cell23_2732079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 8].length) (baseStart_2732079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732079 prefixEnd_2732079 := by exact prefixLift 2732079
  have htrace : WordTrace (prefixWord ++ tailWord_2732079) baseStart_2732079 baseEnd_2732079 := by
    simpa [prefixWord, tailWord_2732079, baseEnd_2732079] using wordTrace_append hprefix tailTrace_2732079
  have hstable : (prefixWord ++ tailWord_2732079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732079).length < 2 ^ (prefixWord ++ tailWord_2732079).sum := by decide
  have hdescent : baseEnd_2732079 < baseStart_2732079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732093 : List Nat := [1, 4, 1, 3, 1, 1, 1, 4, 2, 2, 3]
def baseStart_2732093 : Nat := 118140960795 + 2732093 * 2 ^ 59
def prefixEnd_2732093 : Nat := 4983230072969 + 3 ^ 40 * 2732093 * 2
def baseEnd_2732093 : Nat := 1402876901784284407272839

theorem tailTrace_2732093 : CollatzResearch.WordTrace tailWord_2732093 prefixEnd_2732093 1402876901784284407272839 := by
  unfold tailWord_2732093
  simp only [CollatzResearch.WordTrace]
  refine ⟨99647618091101140181240933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66431745394067426787493955 99647618091101140181240933)
  ·
    refine ⟨18683928392081463783982675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99647618091101140181240933 18683928392081463783982675)
    ·
      refine ⟨28025892588122195675974013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18683928392081463783982675 28025892588122195675974013)
      ·
        refine ⟨10509709720545823378490255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28025892588122195675974013 10509709720545823378490255)
        ·
          refine ⟨15764564580818735067735383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10509709720545823378490255 15764564580818735067735383)
          ·
            refine ⟨23646846871228102601603075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15764564580818735067735383 23646846871228102601603075)
            ·
              refine ⟨35470270306842153902404613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23646846871228102601603075 35470270306842153902404613)
              ·
                refine ⟨6650675682532903856700865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35470270306842153902404613 6650675682532903856700865)
                ·
                  refine ⟨4988006761899677892525649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6650675682532903856700865 4988006761899677892525649)
                  ·
                    refine ⟨3741005071424758419394237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4988006761899677892525649 3741005071424758419394237)
                    ·
                      refine ⟨1402876901784284407272839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3741005071424758419394237 1402876901784284407272839)
                      ·
                        rfl

theorem cell23_2732093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_2732093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732093 prefixEnd_2732093 := by exact prefixLift 2732093
  have htrace : WordTrace (prefixWord ++ tailWord_2732093) baseStart_2732093 baseEnd_2732093 := by
    simpa [prefixWord, tailWord_2732093, baseEnd_2732093] using wordTrace_append hprefix tailTrace_2732093
  have hstable : (prefixWord ++ tailWord_2732093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732093).length < 2 ^ (prefixWord ++ tailWord_2732093).sum := by decide
  have hdescent : baseEnd_2732093 < baseStart_2732093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732096 : List Nat := [2, 1, 1, 2, 2, 4, 1, 4, 6]
def baseStart_2732096 : Nat := 118140960795 + 2732096 * 2 ^ 59
def prefixEnd_2732096 : Nat := 4983230072969 + 3 ^ 40 * 2732096 * 2
def baseEnd_2732096 : Nat := 155875382469583099503925

theorem tailTrace_2732096 : CollatzResearch.WordTrace tailWord_2732096 prefixEnd_2732096 155875382469583099503925 := by
  unfold tailWord_2732096
  simp only [CollatzResearch.WordTrace]
  refine ⟨49823863755045135846800071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66431818340060181129066761 49823863755045135846800071)
  ·
    refine ⟨74735795632567703770200107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49823863755045135846800071 74735795632567703770200107)
    ·
      refine ⟨112103693448851555655300161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74735795632567703770200107 112103693448851555655300161)
      ·
        refine ⟨84077770086638666741475121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112103693448851555655300161 84077770086638666741475121)
        ·
          refine ⟨63058327564979000056106341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84077770086638666741475121 63058327564979000056106341)
          ·
            refine ⟨11823436418433562510519939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63058327564979000056106341 11823436418433562510519939)
            ·
              refine ⟨17735154627650343765779909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11823436418433562510519939 17735154627650343765779909)
              ·
                refine ⟨3325341492684439456083733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17735154627650343765779909 3325341492684439456083733)
                ·
                  refine ⟨155875382469583099503925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3325341492684439456083733 155875382469583099503925)
                  ·
                    rfl

theorem cell23_2732096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 6].length) (baseStart_2732096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732096 prefixEnd_2732096 := by exact prefixLift 2732096
  have htrace : WordTrace (prefixWord ++ tailWord_2732096) baseStart_2732096 baseEnd_2732096 := by
    simpa [prefixWord, tailWord_2732096, baseEnd_2732096] using wordTrace_append hprefix tailTrace_2732096
  have hstable : (prefixWord ++ tailWord_2732096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732096).length < 2 ^ (prefixWord ++ tailWord_2732096).sum := by decide
  have hdescent : baseEnd_2732096 < baseStart_2732096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732106 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 2, 5, 3]
def baseStart_2732106 : Nat := 118140960795 + 2732106 * 2 ^ 59
def prefixEnd_2732106 : Nat := 4983230072969 + 3 ^ 40 * 2732106 * 2
def baseEnd_2732106 : Nat := 1402883577032792856410279

theorem tailTrace_2732106 : CollatzResearch.WordTrace tailWord_2732106 prefixEnd_2732106 1402883577032792856410279 := by
  unfold tailWord_2732106
  simp only [CollatzResearch.WordTrace]
  refine ⟨24912023060013510850366043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66432061493369362267642781 24912023060013510850366043)
  ·
    refine ⟨37368034590020266275549065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24912023060013510850366043 37368034590020266275549065)
    ·
      refine ⟨28026025942515199706661799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37368034590020266275549065 28026025942515199706661799)
      ·
        refine ⟨42039038913772799559992699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28026025942515199706661799 42039038913772799559992699)
        ·
          refine ⟨63058558370659199339989049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42039038913772799559992699 63058558370659199339989049)
          ·
            refine ⟨47293918777994399504991787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63058558370659199339989049 47293918777994399504991787)
            ·
              refine ⟨70940878166991599257487681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47293918777994399504991787 70940878166991599257487681)
              ·
                refine ⟨53205658625243699443115761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70940878166991599257487681 53205658625243699443115761)
                ·
                  refine ⟨39904243968932774582336821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53205658625243699443115761 39904243968932774582336821)
                  ·
                    refine ⟨3741022872087447617094077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39904243968932774582336821 3741022872087447617094077)
                    ·
                      refine ⟨1402883577032792856410279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3741022872087447617094077 1402883577032792856410279)
                      ·
                        rfl

theorem cell23_2732106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_2732106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732106 prefixEnd_2732106 := by exact prefixLift 2732106
  have htrace : WordTrace (prefixWord ++ tailWord_2732106) baseStart_2732106 baseEnd_2732106 := by
    simpa [prefixWord, tailWord_2732106, baseEnd_2732106] using wordTrace_append hprefix tailTrace_2732106
  have hstable : (prefixWord ++ tailWord_2732106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732106).length < 2 ^ (prefixWord ++ tailWord_2732106).sum := by decide
  have hdescent : baseEnd_2732106 < baseStart_2732106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732143 : List Nat := [1, 1, 2, 1, 3, 5, 1, 3, 1, 5]
def baseStart_2732143 : Nat := 118140960795 + 2732143 * 2 ^ 59
def prefixEnd_2732143 : Nat := 4983230072969 + 3 ^ 40 * 2732143 * 2
def baseEnd_2732143 : Nat := 467634191939003070549203

theorem tailTrace_2732143 : CollatzResearch.WordTrace tailWord_2732143 prefixEnd_2732143 467634191939003070549203 := by
  unfold tailWord_2732143
  simp only [CollatzResearch.WordTrace]
  refine ⟨99649441740919998720561083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66432961160613332480374055 99649441740919998720561083)
  ·
    refine ⟨149474162611379998080841625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99649441740919998720561083 149474162611379998080841625)
    ·
      refine ⟨112105621958534998560631219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149474162611379998080841625 112105621958534998560631219)
      ·
        refine ⟨168158432937802497840946829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112105621958534998560631219 168158432937802497840946829)
        ·
          refine ⟨63059412351675936690355061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168158432937802497840946829 63059412351675936690355061)
          ·
            refine ⟨5911819907969619064720787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63059412351675936690355061 5911819907969619064720787)
            ·
              refine ⟨8867729861954428597081181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5911819907969619064720787 8867729861954428597081181)
              ·
                refine ⟨3325398698232910723905443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8867729861954428597081181 3325398698232910723905443)
                ·
                  refine ⟨4988098047349366085858165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3325398698232910723905443 4988098047349366085858165)
                  ·
                    refine ⟨467634191939003070549203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4988098047349366085858165 467634191939003070549203)
                    ·
                      rfl

theorem cell23_2732143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 5].length) (baseStart_2732143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732143 prefixEnd_2732143 := by exact prefixLift 2732143
  have htrace : WordTrace (prefixWord ++ tailWord_2732143) baseStart_2732143 baseEnd_2732143 := by
    simpa [prefixWord, tailWord_2732143, baseEnd_2732143] using wordTrace_append hprefix tailTrace_2732143
  have hstable : (prefixWord ++ tailWord_2732143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732143).length < 2 ^ (prefixWord ++ tailWord_2732143).sum := by decide
  have hdescent : baseEnd_2732143 < baseStart_2732143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732157 : List Nat := [1, 4, 1, 1, 3, 2, 2, 4, 1, 1, 3]
def baseStart_2732157 : Nat := 118140960795 + 2732157 * 2 ^ 59
def prefixEnd_2732157 : Nat := 4983230072969 + 3 ^ 40 * 2732157 * 2
def baseEnd_2732157 : Nat := 1402909764546172156872545

theorem tailTrace_2732157 : CollatzResearch.WordTrace tailWord_2732157 prefixEnd_2732157 1402909764546172156872545 := by
  unfold tailWord_2732157
  simp only [CollatzResearch.WordTrace]
  refine ⟨99649952362869279111570725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66433301575246186074380483 99649952362869279111570725)
  ·
    refine ⟨18684366068037989833419511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99649952362869279111570725 18684366068037989833419511)
    ·
      refine ⟨28026549102056984750129267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18684366068037989833419511 28026549102056984750129267)
      ·
        refine ⟨42039823653085477125193901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28026549102056984750129267 42039823653085477125193901)
        ·
          refine ⟨15764933869907053921947713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42039823653085477125193901 15764933869907053921947713)
          ·
            refine ⟨11823700402430290441460785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15764933869907053921947713 11823700402430290441460785)
            ·
              refine ⟨8867775301822717831095589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11823700402430290441460785 8867775301822717831095589)
              ·
                refine ⟨1662707869091759593330423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8867775301822717831095589 1662707869091759593330423)
                ·
                  refine ⟨2494061803637639389995635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1662707869091759593330423 2494061803637639389995635)
                  ·
                    refine ⟨3741092705456459084993453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2494061803637639389995635 3741092705456459084993453)
                    ·
                      refine ⟨1402909764546172156872545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3741092705456459084993453 1402909764546172156872545)
                      ·
                        rfl

theorem cell23_2732157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4, 1, 1, 3].length) (baseStart_2732157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732157 prefixEnd_2732157 := by exact prefixLift 2732157
  have htrace : WordTrace (prefixWord ++ tailWord_2732157) baseStart_2732157 baseEnd_2732157 := by
    simpa [prefixWord, tailWord_2732157, baseEnd_2732157] using wordTrace_append hprefix tailTrace_2732157
  have hstable : (prefixWord ++ tailWord_2732157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732157).length < 2 ^ (prefixWord ++ tailWord_2732157).sum := by decide
  have hdescent : baseEnd_2732157 < baseStart_2732157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732176 : List Nat := [2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 6]
def baseStart_2732176 : Nat := 118140960795 + 2732176 * 2 ^ 59
def prefixEnd_2732176 : Nat := 4983230072969 + 3 ^ 40 * 2732176 * 2
def baseEnd_2732176 : Nat := 1402919520678607582534957

theorem tailTrace_2732176 : CollatzResearch.WordTrace tailWord_2732176 prefixEnd_2732176 1402919520678607582534957 := by
  unfold tailWord_2732176
  simp only [CollatzResearch.WordTrace]
  refine ⟨49825322674900222678256191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66433763566533630237674921 49825322674900222678256191)
  ·
    refine ⟨74737984012350334017384287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49825322674900222678256191 74737984012350334017384287)
    ·
      refine ⟨112106976018525501026076431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74737984012350334017384287 112106976018525501026076431)
      ·
        refine ⟨168160464027788251539114647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112106976018525501026076431 168160464027788251539114647)
        ·
          refine ⟨252240696041682377308671971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168160464027788251539114647 252240696041682377308671971)
          ·
            refine ⟨378361044062523565963007957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252240696041682377308671971 378361044062523565963007957)
            ·
              refine ⟨8867836970215396077257999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 378361044062523565963007957 8867836970215396077257999)
              ·
                refine ⟨13301755455323094115886999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8867836970215396077257999 13301755455323094115886999)
                ·
                  refine ⟨19952633182984641173830499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13301755455323094115886999 19952633182984641173830499)
                  ·
                    refine ⟨29928949774476961760745749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19952633182984641173830499 29928949774476961760745749)
                    ·
                      refine ⟨1402919520678607582534957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29928949774476961760745749 1402919520678607582534957)
                      ·
                        rfl

theorem cell23_2732176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 6].length) (baseStart_2732176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732176 prefixEnd_2732176 := by exact prefixLift 2732176
  have htrace : WordTrace (prefixWord ++ tailWord_2732176) baseStart_2732176 baseEnd_2732176 := by
    simpa [prefixWord, tailWord_2732176, baseEnd_2732176] using wordTrace_append hprefix tailTrace_2732176
  have hstable : (prefixWord ++ tailWord_2732176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732176).length < 2 ^ (prefixWord ++ tailWord_2732176).sum := by decide
  have hdescent : baseEnd_2732176 < baseStart_2732176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732216 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 2, 7]
def baseStart_2732216 : Nat := 118140960795 + 2732216 * 2 ^ 59
def prefixEnd_2732216 : Nat := 4983230072969 + 3 ^ 40 * 2732216 * 2
def baseEnd_2732216 : Nat := 467646686634929142011591

theorem tailTrace_2732216 : CollatzResearch.WordTrace tailWord_2732216 prefixEnd_2732216 467646686634929142011591 := by
  unfold tailWord_2732216
  simp only [CollatzResearch.WordTrace]
  refine ⟨49826052134827766093984251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66434736179770354791979001 49826052134827766093984251)
  ·
    refine ⟨74739078202241649140976377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49826052134827766093984251 74739078202241649140976377)
    ·
      refine ⟨56054308651681236855732283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74739078202241649140976377 56054308651681236855732283)
      ·
        refine ⟨84081462977521855283598425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56054308651681236855732283 84081462977521855283598425)
        ·
          refine ⟨63061097233141391462698819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84081462977521855283598425 63061097233141391462698819)
          ·
            refine ⟨94591645849712087194048229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63061097233141391462698819 94591645849712087194048229)
            ·
              refine ⟨17735933596821016348884043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94591645849712087194048229 17735933596821016348884043)
              ·
                refine ⟨26603900395231524523326065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17735933596821016348884043 26603900395231524523326065)
                ·
                  refine ⟨19952925296423643392494549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26603900395231524523326065 19952925296423643392494549)
                  ·
                    refine ⟨467646686634929142011591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19952925296423643392494549 467646686634929142011591)
                    ·
                      rfl

theorem cell23_2732216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 2, 7].length) (baseStart_2732216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732216 prefixEnd_2732216 := by exact prefixLift 2732216
  have htrace : WordTrace (prefixWord ++ tailWord_2732216) baseStart_2732216 baseEnd_2732216 := by
    simpa [prefixWord, tailWord_2732216, baseEnd_2732216] using wordTrace_append hprefix tailTrace_2732216
  have hstable : (prefixWord ++ tailWord_2732216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732216).length < 2 ^ (prefixWord ++ tailWord_2732216).sum := by decide
  have hdescent : baseEnd_2732216 < baseStart_2732216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732223 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 2, 7, 2]
def baseStart_2732223 : Nat := 118140960795 + 2732223 * 2 ^ 59
def prefixEnd_2732223 : Nat := 4983230072969 + 3 ^ 40 * 2732223 * 2
def baseEnd_2732223 : Nat := 1402943654269368898647241

theorem tailTrace_2732223 : CollatzResearch.WordTrace tailWord_2732223 prefixEnd_2732223 1402943654269368898647241 := by
  unfold tailWord_2732223
  simp only [CollatzResearch.WordTrace]
  refine ⟨99652359580630172383473323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66434906387086781588982215 99652359580630172383473323)
  ·
    refine ⟨149478539370945258575209985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99652359580630172383473323 149478539370945258575209985)
    ·
      refine ⟨112108904528208943931407489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149478539370945258575209985 112108904528208943931407489)
      ·
        refine ⟨84081678396156707948555617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112108904528208943931407489 84081678396156707948555617)
        ·
          refine ⟨63061258797117530961416713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84081678396156707948555617 63061258797117530961416713)
          ·
            refine ⟨47295944097838148221062535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63061258797117530961416713 47295944097838148221062535)
            ·
              refine ⟨70943916146757222331593803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47295944097838148221062535 70943916146757222331593803)
              ·
                refine ⟨106415874220135833497390705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70943916146757222331593803 106415874220135833497390705)
                ·
                  refine ⟨79811905665101875123043029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106415874220135833497390705 79811905665101875123043029)
                  ·
                    refine ⟨1870591539025825198196321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 79811905665101875123043029 1870591539025825198196321)
                    ·
                      refine ⟨1402943654269368898647241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1870591539025825198196321 1402943654269368898647241)
                      ·
                        rfl

theorem cell23_2732223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 7, 2].length) (baseStart_2732223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732223 prefixEnd_2732223 := by exact prefixLift 2732223
  have htrace : WordTrace (prefixWord ++ tailWord_2732223) baseStart_2732223 baseEnd_2732223 := by
    simpa [prefixWord, tailWord_2732223, baseEnd_2732223] using wordTrace_append hprefix tailTrace_2732223
  have hstable : (prefixWord ++ tailWord_2732223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732223).length < 2 ^ (prefixWord ++ tailWord_2732223).sum := by decide
  have hdescent : baseEnd_2732223 < baseStart_2732223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732270 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 5, 4, 2]
def baseStart_2732270 : Nat := 118140960795 + 2732270 * 2 ^ 59
def prefixEnd_2732270 : Nat := 4983230072969 + 3 ^ 40 * 2732270 * 2
def baseEnd_2732270 : Nat := 1402967787860130214759525

theorem tailTrace_2732270 : CollatzResearch.WordTrace tailWord_2732270 prefixEnd_2732270 1402967787860130214759525 := by
  unfold tailWord_2732270
  simp only [CollatzResearch.WordTrace]
  refine ⟨12456759226432487426304283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66436049207639932940289509 12456759226432487426304283)
  ·
    refine ⟨18685138839648731139456425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12456759226432487426304283 18685138839648731139456425)
    ·
      refine ⟨14013854129736548354592319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18685138839648731139456425 14013854129736548354592319)
      ·
        refine ⟨21020781194604822531888479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14013854129736548354592319 21020781194604822531888479)
        ·
          refine ⟨31531171791907233797832719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21020781194604822531888479 31531171791907233797832719)
          ·
            refine ⟨47296757687860850696749079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31531171791907233797832719 47296757687860850696749079)
            ·
              refine ⟨70945136531791276045123619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47296757687860850696749079 70945136531791276045123619)
              ·
                refine ⟨106417704797686914067685429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70945136531791276045123619 106417704797686914067685429)
                ·
                  refine ⟨9976659824783148193845509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106417704797686914067685429 9976659824783148193845509)
                  ·
                    refine ⟨1870623717146840286346033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9976659824783148193845509 1870623717146840286346033)
                    ·
                      refine ⟨1402967787860130214759525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1870623717146840286346033 1402967787860130214759525)
                      ·
                        rfl

theorem cell23_2732270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_2732270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732270 prefixEnd_2732270 := by exact prefixLift 2732270
  have htrace : WordTrace (prefixWord ++ tailWord_2732270) baseStart_2732270 baseEnd_2732270 := by
    simpa [prefixWord, tailWord_2732270, baseEnd_2732270] using wordTrace_append hprefix tailTrace_2732270
  have hstable : (prefixWord ++ tailWord_2732270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732270).length < 2 ^ (prefixWord ++ tailWord_2732270).sum := by decide
  have hdescent : baseEnd_2732270 < baseStart_2732270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732273 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 2, 4, 3]
def baseStart_2732273 : Nat := 118140960795 + 2732273 * 2 ^ 59
def prefixEnd_2732273 : Nat := 4983230072969 + 3 ^ 40 * 2732273 * 2
def baseEnd_2732273 : Nat := 1402969328302093703022011

theorem tailTrace_2732273 : CollatzResearch.WordTrace tailWord_2732273 prefixEnd_2732273 1402969328302093703022011 := by
  unfold tailWord_2732273
  simp only [CollatzResearch.WordTrace]
  refine ⟨99654183230449030922793473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66436122153632687281862315 99654183230449030922793473)
  ·
    refine ⟨74740637422836773192095105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99654183230449030922793473 74740637422836773192095105)
    ·
      refine ⟨56055478067127579894071329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74740637422836773192095105 56055478067127579894071329)
      ·
        refine ⟨42041608550345684920553497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56055478067127579894071329 42041608550345684920553497)
        ·
          refine ⟨31531206412759263690415123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42041608550345684920553497 31531206412759263690415123)
          ·
            refine ⟨47296809619138895535622685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31531206412759263690415123 47296809619138895535622685)
            ·
              refine ⟨17736303607177085825858507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47296809619138895535622685 17736303607177085825858507)
              ·
                refine ⟨26604455410765628738787761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17736303607177085825858507 26604455410765628738787761)
                ·
                  refine ⟨19953341558074221554090821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26604455410765628738787761 19953341558074221554090821)
                  ·
                    refine ⟨3741251542138916541392029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19953341558074221554090821 3741251542138916541392029)
                    ·
                      refine ⟨1402969328302093703022011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3741251542138916541392029 1402969328302093703022011)
                      ·
                        rfl

theorem cell23_2732273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_2732273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732273 prefixEnd_2732273 := by exact prefixLift 2732273
  have htrace : WordTrace (prefixWord ++ tailWord_2732273) baseStart_2732273 baseEnd_2732273 := by
    simpa [prefixWord, tailWord_2732273, baseEnd_2732273] using wordTrace_append hprefix tailTrace_2732273
  have hstable : (prefixWord ++ tailWord_2732273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732273).length < 2 ^ (prefixWord ++ tailWord_2732273).sum := by decide
  have hdescent : baseEnd_2732273 < baseStart_2732273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732287 : List Nat := [1, 1, 2, 2, 1, 4, 1, 5, 2, 2, 2]
def baseStart_2732287 : Nat := 118140960795 + 2732287 * 2 ^ 59
def prefixEnd_2732287 : Nat := 4983230072969 + 3 ^ 40 * 2732287 * 2
def baseEnd_2732287 : Nat := 1402976517031256648246947

theorem tailTrace_2732287 : CollatzResearch.WordTrace tailWord_2732287 prefixEnd_2732287 1402976517031256648246947 := by
  unfold tailWord_2732287
  simp only [CollatzResearch.WordTrace]
  refine ⟨99654693852398311313803115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66436462568265540875868743 99654693852398311313803115)
  ·
    refine ⟨149482040778597466970704673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99654693852398311313803115 149482040778597466970704673)
    ·
      refine ⟨112111530583948100228028505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149482040778597466970704673 112111530583948100228028505)
      ·
        refine ⟨84083647937961075171021379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112111530583948100228028505 84083647937961075171021379)
        ·
          refine ⟨126125471906941612756532069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84083647937961075171021379 126125471906941612756532069)
          ·
            refine ⟨23648525982551552391849763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126125471906941612756532069 23648525982551552391849763)
            ·
              refine ⟨35472788973827328587774645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23648525982551552391849763 35472788973827328587774645)
              ·
                refine ⟨3325573966296312055103873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35472788973827328587774645 3325573966296312055103873)
                ·
                  refine ⟨2494180474722234041327905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3325573966296312055103873 2494180474722234041327905)
                  ·
                    refine ⟨1870635356041675530995929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2494180474722234041327905 1870635356041675530995929)
                    ·
                      refine ⟨1402976517031256648246947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1870635356041675530995929 1402976517031256648246947)
                      ·
                        rfl

theorem cell23_2732287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2, 2, 2].length) (baseStart_2732287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732287 prefixEnd_2732287 := by exact prefixLift 2732287
  have htrace : WordTrace (prefixWord ++ tailWord_2732287) baseStart_2732287 baseEnd_2732287 := by
    simpa [prefixWord, tailWord_2732287, baseEnd_2732287] using wordTrace_append hprefix tailTrace_2732287
  have hstable : (prefixWord ++ tailWord_2732287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732287).length < 2 ^ (prefixWord ++ tailWord_2732287).sum := by decide
  have hdescent : baseEnd_2732287 < baseStart_2732287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732320 : List Nat := [2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 3]
def baseStart_2732320 : Nat := 118140960795 + 2732320 * 2 ^ 59
def prefixEnd_2732320 : Nat := 4983230072969 + 3 ^ 40 * 2732320 * 2
def baseEnd_2732320 : Nat := 1402993461892855019134295

theorem tailTrace_2732320 : CollatzResearch.WordTrace tailWord_2732320 prefixEnd_2732320 1402993461892855019134295 := by
  unfold tailWord_2732320
  simp only [CollatzResearch.WordTrace]
  refine ⟨49827948730639378974877207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66437264974185838633169609 49827948730639378974877207)
  ·
    refine ⟨74741923095959068462315811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49827948730639378974877207 74741923095959068462315811)
    ·
      refine ⟨112112884643938602693473717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74741923095959068462315811 112112884643938602693473717)
      ·
        refine ⟨10510582935369244002513161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112112884643938602693473717 10510582935369244002513161)
        ·
          refine ⟨7882937201526933001884871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10510582935369244002513161 7882937201526933001884871)
          ·
            refine ⟨11824405802290399502827307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7882937201526933001884871 11824405802290399502827307)
            ·
              refine ⟨17736608703435599254240961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11824405802290399502827307 17736608703435599254240961)
              ·
                refine ⟨13302456527576699440680721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17736608703435599254240961 13302456527576699440680721)
                ·
                  refine ⟨9976842395682524580510541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13302456527576699440680721 9976842395682524580510541)
                  ·
                    refine ⟨3741315898380946717691453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9976842395682524580510541 3741315898380946717691453)
                    ·
                      refine ⟨1402993461892855019134295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3741315898380946717691453 1402993461892855019134295)
                      ·
                        rfl

theorem cell23_2732320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_2732320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732320 prefixEnd_2732320 := by exact prefixLift 2732320
  have htrace : WordTrace (prefixWord ++ tailWord_2732320) baseStart_2732320 baseEnd_2732320 := by
    simpa [prefixWord, tailWord_2732320, baseEnd_2732320] using wordTrace_append hprefix tailTrace_2732320
  have hstable : (prefixWord ++ tailWord_2732320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732320).length < 2 ^ (prefixWord ++ tailWord_2732320).sum := by decide
  have hdescent : baseEnd_2732320 < baseStart_2732320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732323 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 4, 5]
def baseStart_2732323 : Nat := 118140960795 + 2732323 * 2 ^ 59
def prefixEnd_2732323 : Nat := 4983230072969 + 3 ^ 40 * 2732323 * 2
def baseEnd_2732323 : Nat := 467665000778272835798927

theorem tailTrace_2732323 : CollatzResearch.WordTrace tailWord_2732323 prefixEnd_2732323 467665000778272835798927 := by
  unfold tailWord_2732323
  simp only [CollatzResearch.WordTrace]
  refine ⟨99656006880267889462113623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66437337920178592974742415 99656006880267889462113623)
  ·
    refine ⟨149484010320401834193170435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99656006880267889462113623 149484010320401834193170435)
    ·
      refine ⟨224226015480602751289755653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149484010320401834193170435 224226015480602751289755653)
      ·
        refine ⟨42042377902613015866829185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 224226015480602751289755653 42042377902613015866829185)
        ·
          refine ⟨31531783426959761900121889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42042377902613015866829185 31531783426959761900121889)
          ·
            refine ⟨23648837570219821425091417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31531783426959761900121889 23648837570219821425091417)
            ·
              refine ⟨17736628177664866068818563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23648837570219821425091417 17736628177664866068818563)
              ·
                refine ⟨26604942266497299103227845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17736628177664866068818563 26604942266497299103227845)
                ·
                  refine ⟨4988426674968243581855221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26604942266497299103227845 4988426674968243581855221)
                  ·
                    refine ⟨467665000778272835798927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4988426674968243581855221 467665000778272835798927)
                    ·
                      rfl

theorem cell23_2732323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 5].length) (baseStart_2732323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732323 prefixEnd_2732323 := by exact prefixLift 2732323
  have htrace : WordTrace (prefixWord ++ tailWord_2732323) baseStart_2732323 baseEnd_2732323 := by
    simpa [prefixWord, tailWord_2732323, baseEnd_2732323] using wordTrace_append hprefix tailTrace_2732323
  have hstable : (prefixWord ++ tailWord_2732323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732323).length < 2 ^ (prefixWord ++ tailWord_2732323).sum := by decide
  have hdescent : baseEnd_2732323 < baseStart_2732323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732340 : List Nat := [2, 5, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_2732340 : Nat := 118140960795 + 2732340 * 2 ^ 59
def prefixEnd_2732340 : Nat := 4983230072969 + 3 ^ 40 * 2732340 * 2
def baseEnd_2732340 : Nat := 467667910501981646961401

theorem tailTrace_2732340 : CollatzResearch.WordTrace tailWord_2732340 prefixEnd_2732340 467667910501981646961401 := by
  unfold tailWord_2732340
  simp only [CollatzResearch.WordTrace]
  refine ⟨49828313460603150682741237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66437751280804200910321649 49828313460603150682741237)
  ·
    refine ⟨4671404386931545376506991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49828313460603150682741237 4671404386931545376506991)
    ·
      refine ⟨7007106580397318064760487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4671404386931545376506991 7007106580397318064760487)
      ·
        refine ⟨10510659870595977097140731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7007106580397318064760487 10510659870595977097140731)
        ·
          refine ⟨15765989805893965645711097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10510659870595977097140731 15765989805893965645711097)
          ·
            refine ⟨11824492354420474234283323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15765989805893965645711097 11824492354420474234283323)
            ·
              refine ⟨17736738531630711351424985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11824492354420474234283323 17736738531630711351424985)
              ·
                refine ⟨13302553898723033513568739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17736738531630711351424985 13302553898723033513568739)
                ·
                  refine ⟨19953830848084550270353109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13302553898723033513568739 19953830848084550270353109)
                  ·
                    refine ⟨467667910501981646961401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19953830848084550270353109 467667910501981646961401)
                    ·
                      rfl

theorem cell23_2732340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_2732340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732340 prefixEnd_2732340 := by exact prefixLift 2732340
  have htrace : WordTrace (prefixWord ++ tailWord_2732340) baseStart_2732340 baseEnd_2732340 := by
    simpa [prefixWord, tailWord_2732340, baseEnd_2732340] using wordTrace_append hprefix tailTrace_2732340
  have hstable : (prefixWord ++ tailWord_2732340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732340).length < 2 ^ (prefixWord ++ tailWord_2732340).sum := by decide
  have hdescent : baseEnd_2732340 < baseStart_2732340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732360 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 1, 6, 2]
def baseStart_2732360 : Nat := 118140960795 + 2732360 * 2 ^ 59
def prefixEnd_2732360 : Nat := 4983230072969 + 3 ^ 40 * 2732360 * 2
def baseEnd_2732360 : Nat := 1403014001119034862634111

theorem tailTrace_2732360 : CollatzResearch.WordTrace tailWord_2732360 prefixEnd_2732360 1403014001119034862634111 := by
  unfold tailWord_2732360
  simp only [CollatzResearch.WordTrace]
  refine ⟨49828678190566922390605267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66438237587422563187473689 49828678190566922390605267)
  ·
    refine ⟨74743017285850383585907901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49828678190566922390605267 74743017285850383585907901)
    ·
      refine ⟨28028631482193893844715463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74743017285850383585907901 28028631482193893844715463)
      ·
        refine ⟨42042947223290840767073195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28028631482193893844715463 42042947223290840767073195)
        ·
          refine ⟨63064420834936261150609793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42042947223290840767073195 63064420834936261150609793)
          ·
            refine ⟨47298315626202195862957345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63064420834936261150609793 47298315626202195862957345)
            ·
              refine ⟨35473736719651646897218009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47298315626202195862957345 35473736719651646897218009)
              ·
                refine ⟨26605302539738735172913507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35473736719651646897218009 26605302539738735172913507)
                ·
                  refine ⟨39907953809608102759370261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26605302539738735172913507 39907953809608102759370261)
                  ·
                    refine ⟨1870685334825379816845481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 39907953809608102759370261 1870685334825379816845481)
                    ·
                      refine ⟨1403014001119034862634111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1870685334825379816845481 1403014001119034862634111)
                      ·
                        rfl

theorem cell23_2732360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 1, 6, 2].length) (baseStart_2732360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732360 prefixEnd_2732360 := by exact prefixLift 2732360
  have htrace : WordTrace (prefixWord ++ tailWord_2732360) baseStart_2732360 baseEnd_2732360 := by
    simpa [prefixWord, tailWord_2732360, baseEnd_2732360] using wordTrace_append hprefix tailTrace_2732360
  have hstable : (prefixWord ++ tailWord_2732360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732360).length < 2 ^ (prefixWord ++ tailWord_2732360).sum := by decide
  have hdescent : baseEnd_2732360 < baseStart_2732360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732370 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 5, 4]
def baseStart_2732370 : Nat := 118140960795 + 2732370 * 2 ^ 59
def prefixEnd_2732370 : Nat := 4983230072969 + 3 ^ 40 * 2732370 * 2
def baseEnd_2732370 : Nat := 467673045308526607836355

theorem tailTrace_2732370 : CollatzResearch.WordTrace tailWord_2732370 prefixEnd_2732370 467673045308526607836355 := by
  unfold tailWord_2732370
  simp only [CollatzResearch.WordTrace]
  refine ⟨24914430277774404122268641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66438480740731744326049709 24914430277774404122268641)
  ·
    refine ⟨18685822708330803091701481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24914430277774404122268641 18685822708330803091701481)
    ·
      refine ⟨14014367031248102318776111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18685822708330803091701481 14014367031248102318776111)
      ·
        refine ⟨21021550546872153478164167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14014367031248102318776111 21021550546872153478164167)
        ·
          refine ⟨31532325820308230217246251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21021550546872153478164167 31532325820308230217246251)
          ·
            refine ⟨47298488730462345325869377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31532325820308230217246251 47298488730462345325869377)
            ·
              refine ⟨35473866547846758994402033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47298488730462345325869377 35473866547846758994402033)
              ·
                refine ⟨26605399910885069245801525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35473866547846758994402033 26605399910885069245801525)
                ·
                  refine ⟨2494256241645475241793893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26605399910885069245801525 2494256241645475241793893)
                  ·
                    refine ⟨467673045308526607836355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2494256241645475241793893 467673045308526607836355)
                    ·
                      rfl

theorem cell23_2732370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_2732370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732370 prefixEnd_2732370 := by exact prefixLift 2732370
  have htrace : WordTrace (prefixWord ++ tailWord_2732370) baseStart_2732370 baseEnd_2732370 := by
    simpa [prefixWord, tailWord_2732370, baseEnd_2732370] using wordTrace_append hprefix tailTrace_2732370
  have hstable : (prefixWord ++ tailWord_2732370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732370).length < 2 ^ (prefixWord ++ tailWord_2732370).sum := by decide
  have hdescent : baseEnd_2732370 < baseStart_2732370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732383 : List Nat := [1, 1, 2, 3, 1, 2, 4, 1, 8]
def baseStart_2732383 : Nat := 118140960795 + 2732383 * 2 ^ 59
def prefixEnd_2732383 : Nat := 4983230072969 + 3 ^ 40 * 2732383 * 2
def baseEnd_2732383 : Nat := 155891756797120919182945

theorem tailTrace_2732383 : CollatzResearch.WordTrace tailWord_2732383 prefixEnd_2732383 155891756797120919182945 := by
  unfold tailWord_2732383
  simp only [CollatzResearch.WordTrace]
  refine ⟨99658195260050519709297803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66438796840033679806198535 99658195260050519709297803)
  ·
    refine ⟨149487292890075779563946705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99658195260050519709297803 149487292890075779563946705)
    ·
      refine ⟨112115469667556834672960029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149487292890075779563946705 112115469667556834672960029)
      ·
        refine ⟨42043301125333813002360011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112115469667556834672960029 42043301125333813002360011)
        ·
          refine ⟨63064951688000719503540017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42043301125333813002360011 63064951688000719503540017)
          ·
            refine ⟨47298713766000539627655013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63064951688000719503540017 47298713766000539627655013)
            ·
              refine ⟨8868508831125101180185315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47298713766000539627655013 8868508831125101180185315)
              ·
                refine ⟨13302763246687651770277973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8868508831125101180185315 13302763246687651770277973)
                ·
                  refine ⟨155891756797120919182945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13302763246687651770277973 155891756797120919182945)
                  ·
                    rfl

theorem cell23_2732383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 8].length) (baseStart_2732383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732383 prefixEnd_2732383 := by exact prefixLift 2732383
  have htrace : WordTrace (prefixWord ++ tailWord_2732383) baseStart_2732383 baseEnd_2732383 := by
    simpa [prefixWord, tailWord_2732383, baseEnd_2732383] using wordTrace_append hprefix tailTrace_2732383
  have hstable : (prefixWord ++ tailWord_2732383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732383).length < 2 ^ (prefixWord ++ tailWord_2732383).sum := by decide
  have hdescent : baseEnd_2732383 < baseStart_2732383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732400 : List Nat := [2, 1, 1, 1, 4, 4, 1, 3, 6]
def baseStart_2732400 : Nat := 118140960795 + 2732400 * 2 ^ 59
def prefixEnd_2732400 : Nat := 4983230072969 + 3 ^ 40 * 2732400 * 2
def baseEnd_2732400 : Nat := 155892726705023856237103

theorem tailTrace_2732400 : CollatzResearch.WordTrace tailWord_2732400 prefixEnd_2732400 155892726705023856237103 := by
  unfold tailWord_2732400
  simp only [CollatzResearch.WordTrace]
  refine ⟨49829407650494465806333327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66439210200659287741777769 49829407650494465806333327)
  ·
    refine ⟨74744111475741698709499991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49829407650494465806333327 74744111475741698709499991)
    ·
      refine ⟨112116167213612548064249987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74744111475741698709499991 112116167213612548064249987)
      ·
        refine ⟨168174250820418822096374981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112116167213612548064249987 168174250820418822096374981)
        ·
          refine ⟨31532672028828529143070309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168174250820418822096374981 31532672028828529143070309)
          ·
            refine ⟨5912376005405349214325683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31532672028828529143070309 5912376005405349214325683)
            ·
              refine ⟨8868564008108023821488525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5912376005405349214325683 8868564008108023821488525)
              ·
                refine ⟨3325711503040508933058197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8868564008108023821488525 3325711503040508933058197)
                ·
                  refine ⟨155892726705023856237103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3325711503040508933058197 155892726705023856237103)
                  ·
                    rfl

theorem cell23_2732400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 6].length) (baseStart_2732400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732400 prefixEnd_2732400 := by exact prefixLift 2732400
  have htrace : WordTrace (prefixWord ++ tailWord_2732400) baseStart_2732400 baseEnd_2732400 := by
    simpa [prefixWord, tailWord_2732400, baseEnd_2732400] using wordTrace_append hprefix tailTrace_2732400
  have hstable : (prefixWord ++ tailWord_2732400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732400).length < 2 ^ (prefixWord ++ tailWord_2732400).sum := by decide
  have hdescent : baseEnd_2732400 < baseStart_2732400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732460 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 6, 4]
def baseStart_2732460 : Nat := 118140960795 + 2732460 * 2 ^ 59
def prefixEnd_2732460 : Nat := 4983230072969 + 3 ^ 40 * 2732460 * 2
def baseEnd_2732460 : Nat := 467688449728161490461217

theorem tailTrace_2732460 : CollatzResearch.WordTrace tailWord_2732460 prefixEnd_2732460 467688449728161490461217 := by
  unfold tailWord_2732460
  simp only [CollatzResearch.WordTrace]
  refine ⟨49830501840385780929925417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66440669120514374573233889 49830501840385780929925417)
  ·
    refine ⟨37372876380289335697444063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49830501840385780929925417 37372876380289335697444063)
    ·
      refine ⟨56059314570434003546166095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37372876380289335697444063 56059314570434003546166095)
      ·
        refine ⟨84088971855651005319249143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56059314570434003546166095 84088971855651005319249143)
        ·
          refine ⟨126133457783476507978873715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84088971855651005319249143 126133457783476507978873715)
          ·
            refine ⟨189200186675214761968310573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126133457783476507978873715 189200186675214761968310573)
            ·
              refine ⟨70950070003205535738116465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189200186675214761968310573 70950070003205535738116465)
              ·
                refine ⟨53212552502404151803587349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70950070003205535738116465 53212552502404151803587349)
                ·
                  refine ⟨2494338398550194615793157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53212552502404151803587349 2494338398550194615793157)
                  ·
                    refine ⟨467688449728161490461217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2494338398550194615793157 467688449728161490461217)
                    ·
                      rfl

theorem cell23_2732460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 4].length) (baseStart_2732460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732460 prefixEnd_2732460 := by exact prefixLift 2732460
  have htrace : WordTrace (prefixWord ++ tailWord_2732460) baseStart_2732460 baseEnd_2732460 := by
    simpa [prefixWord, tailWord_2732460, baseEnd_2732460] using wordTrace_append hprefix tailTrace_2732460
  have hstable : (prefixWord ++ tailWord_2732460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732460).length < 2 ^ (prefixWord ++ tailWord_2732460).sum := by decide
  have hdescent : baseEnd_2732460 < baseStart_2732460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732461 : List Nat := [1, 5, 2, 2, 2, 1, 1, 2, 3, 1, 3]
def baseStart_2732461 : Nat := 118140960795 + 2732461 * 2 ^ 59
def prefixEnd_2732461 : Nat := 4983230072969 + 3 ^ 40 * 2732461 * 2
def baseEnd_2732461 : Nat := 1403065862665138967471147

theorem tailTrace_2732461 : CollatzResearch.WordTrace tailWord_2732461 prefixEnd_2732461 1403065862665138967471147 := by
  unfold tailWord_2732461
  simp only [CollatzResearch.WordTrace]
  refine ⟨99661040153767939030637237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66440693435845292687091491 99661040153767939030637237)
  ·
    refine ⟨9343222514415744284122241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99661040153767939030637237 9343222514415744284122241)
    ·
      refine ⟨7007416885811808213091681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9343222514415744284122241 7007416885811808213091681)
      ·
        refine ⟨5255562664358856159818761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7007416885811808213091681 5255562664358856159818761)
        ·
          refine ⟨3941671998269142119864071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5255562664358856159818761 3941671998269142119864071)
          ·
            refine ⟨5912507997403713179796107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3941671998269142119864071 5912507997403713179796107)
            ·
              refine ⟨8868761996105569769694161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5912507997403713179796107 8868761996105569769694161)
              ·
                refine ⟨6651571497079177327270621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8868761996105569769694161 6651571497079177327270621)
                ·
                  refine ⟨2494339311404691497726483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6651571497079177327270621 2494339311404691497726483)
                  ·
                    refine ⟨3741508967107037246589725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2494339311404691497726483 3741508967107037246589725)
                    ·
                      refine ⟨1403065862665138967471147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3741508967107037246589725 1403065862665138967471147)
                      ·
                        rfl

theorem cell23_2732461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_2732461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732461 prefixEnd_2732461 := by exact prefixLift 2732461
  have htrace : WordTrace (prefixWord ++ tailWord_2732461) baseStart_2732461 baseEnd_2732461 := by
    simpa [prefixWord, tailWord_2732461, baseEnd_2732461] using wordTrace_append hprefix tailTrace_2732461
  have hstable : (prefixWord ++ tailWord_2732461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732461).length < 2 ^ (prefixWord ++ tailWord_2732461).sum := by decide
  have hdescent : baseEnd_2732461 < baseStart_2732461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732501 : List Nat := [1, 3, 2, 3, 1, 3, 2, 1, 3, 2, 2]
def baseStart_2732501 : Nat := 118140960795 + 2732501 * 2 ^ 59
def prefixEnd_2732501 : Nat := 4983230072969 + 3 ^ 40 * 2732501 * 2
def baseEnd_2732501 : Nat := 1403086401891318810970963

theorem tailTrace_2732501 : CollatzResearch.WordTrace tailWord_2732501 prefixEnd_2732501 1403086401891318810970963 := by
  unfold tailWord_2732501
  simp only [CollatzResearch.WordTrace]
  refine ⟨99662499073623025862093357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66441666049082017241395571 99662499073623025862093357)
  ·
    refine ⟨37373437152608634698285009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99662499073623025862093357 37373437152608634698285009)
    ·
      refine ⟨28030077864456476023713757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37373437152608634698285009 28030077864456476023713757)
      ·
        refine ⟨10511279199171178508892659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28030077864456476023713757 10511279199171178508892659)
        ·
          refine ⟨15766918798756767763338989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10511279199171178508892659 15766918798756767763338989)
          ·
            refine ⟨5912594549533787911252121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15766918798756767763338989 5912594549533787911252121)
            ·
              refine ⟨4434445912150340933439091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5912594549533787911252121 4434445912150340933439091)
              ·
                refine ⟨6651668868225511400158637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4434445912150340933439091 6651668868225511400158637)
                ·
                  refine ⟨2494375825584566775059489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6651668868225511400158637 2494375825584566775059489)
                  ·
                    refine ⟨1870781869188425081294617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2494375825584566775059489 1870781869188425081294617)
                    ·
                      refine ⟨1403086401891318810970963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1870781869188425081294617 1403086401891318810970963)
                      ·
                        rfl

theorem cell23_2732501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_2732501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732501 prefixEnd_2732501 := by exact prefixLift 2732501
  have htrace : WordTrace (prefixWord ++ tailWord_2732501) baseStart_2732501 baseEnd_2732501 := by
    simpa [prefixWord, tailWord_2732501, baseEnd_2732501] using wordTrace_append hprefix tailTrace_2732501
  have hstable : (prefixWord ++ tailWord_2732501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732501).length < 2 ^ (prefixWord ++ tailWord_2732501).sum := by decide
  have hdescent : baseEnd_2732501 < baseStart_2732501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732534 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3]
def baseStart_2732534 : Nat := 118140960795 + 2732534 * 2 ^ 59
def prefixEnd_2732534 : Nat := 4983230072969 + 3 ^ 40 * 2732534 * 2
def baseEnd_2732534 : Nat := 1403103346752917181858311

theorem tailTrace_2732534 : CollatzResearch.WordTrace tailWord_2732534 prefixEnd_2732534 1403103346752917181858311 := by
  unfold tailWord_2732534
  simp only [CollatzResearch.WordTrace]
  refine ⟨6228981417656467031127791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66442468455002314998696437 6228981417656467031127791)
  ·
    refine ⟨9343472126484700546691687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6228981417656467031127791 9343472126484700546691687)
    ·
      refine ⟨14015208189727050820037531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9343472126484700546691687 14015208189727050820037531)
      ·
        refine ⟨21022812284590576230056297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14015208189727050820037531 21022812284590576230056297)
        ·
          refine ⟨15767109213442932172542223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21022812284590576230056297 15767109213442932172542223)
          ·
            refine ⟨23650663820164398258813335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15767109213442932172542223 23650663820164398258813335)
            ·
              refine ⟨35475995730246597388220003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23650663820164398258813335 35475995730246597388220003)
              ·
                refine ⟨53213993595369896082330005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35475995730246597388220003 53213993595369896082330005)
                ·
                  refine ⟨2494405949782963878859219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53213993595369896082330005 2494405949782963878859219)
                  ·
                    refine ⟨3741608924674445818288829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2494405949782963878859219 3741608924674445818288829)
                    ·
                      refine ⟨1403103346752917181858311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3741608924674445818288829 1403103346752917181858311)
                      ·
                        rfl

theorem cell23_2732534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_2732534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732534 prefixEnd_2732534 := by exact prefixLift 2732534
  have htrace : WordTrace (prefixWord ++ tailWord_2732534) baseStart_2732534 baseEnd_2732534 := by
    simpa [prefixWord, tailWord_2732534, baseEnd_2732534] using wordTrace_append hprefix tailTrace_2732534
  have hstable : (prefixWord ++ tailWord_2732534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732534).length < 2 ^ (prefixWord ++ tailWord_2732534).sum := by decide
  have hdescent : baseEnd_2732534 < baseStart_2732534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732540 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 1, 5, 4]
def baseStart_2732540 : Nat := 118140960795 + 2732540 * 2 ^ 59
def prefixEnd_2732540 : Nat := 4983230072969 + 3 ^ 40 * 2732540 * 2
def baseEnd_2732540 : Nat := 1403106427636844158383283

theorem tailTrace_2732540 : CollatzResearch.WordTrace tailWord_2732540 prefixEnd_2732540 1403106427636844158383283 := by
  unfold tailWord_2732540
  simp only [CollatzResearch.WordTrace]
  refine ⟨49831960760240867761381537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66442614346987823681842049 49831960760240867761381537)
  ·
    refine ⟨37373970570180650821036153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49831960760240867761381537 37373970570180650821036153)
    ·
      refine ⟨28030477927635488115777115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37373970570180650821036153 28030477927635488115777115)
      ·
        refine ⟨42045716891453232173665673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28030477927635488115777115 42045716891453232173665673)
        ·
          refine ⟨31534287668589924130249255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42045716891453232173665673 31534287668589924130249255)
          ·
            refine ⟨47301431502884886195373883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31534287668589924130249255 47301431502884886195373883)
            ·
              refine ⟨70952147254327329293060825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47301431502884886195373883 70952147254327329293060825)
              ·
                refine ⟨53214110440745496969795619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70952147254327329293060825 53214110440745496969795619)
                ·
                  refine ⟨79821165661118245454693429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53214110440745496969795619 79821165661118245454693429)
                  ·
                    refine ⟨7483234280729835511377509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 79821165661118245454693429 7483234280729835511377509)
                    ·
                      refine ⟨1403106427636844158383283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7483234280729835511377509 1403106427636844158383283)
                      ·
                        rfl

theorem cell23_2732540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_2732540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732540 prefixEnd_2732540 := by exact prefixLift 2732540
  have htrace : WordTrace (prefixWord ++ tailWord_2732540) baseStart_2732540 baseEnd_2732540 := by
    simpa [prefixWord, tailWord_2732540, baseEnd_2732540] using wordTrace_append hprefix tailTrace_2732540
  have hstable : (prefixWord ++ tailWord_2732540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732540).length < 2 ^ (prefixWord ++ tailWord_2732540).sum := by decide
  have hdescent : baseEnd_2732540 < baseStart_2732540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732568 : List Nat := [2, 1, 2, 3, 3, 3, 2, 1, 2, 1, 3]
def baseStart_2732568 : Nat := 118140960795 + 2732568 * 2 ^ 59
def prefixEnd_2732568 : Nat := 4983230072969 + 3 ^ 40 * 2732568 * 2
def baseEnd_2732568 : Nat := 1403120805095170048833155

theorem tailTrace_2732568 : CollatzResearch.WordTrace tailWord_2732568 prefixEnd_2732568 1403120805095170048833155 := by
  unfold tailWord_2732568
  simp only [CollatzResearch.WordTrace]
  refine ⟨49832471382190148152391179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66443295176253530869854905 49832471382190148152391179)
  ·
    refine ⟨74748707073285222228586769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49832471382190148152391179 74748707073285222228586769)
    ·
      refine ⟨56061530304963916671440077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74748707073285222228586769 56061530304963916671440077)
      ·
        refine ⟨21023073864361468751790029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56061530304963916671440077 21023073864361468751790029)
        ·
          refine ⟨7883652699135550781921261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21023073864361468751790029 7883652699135550781921261)
          ·
            refine ⟨2956369762175831543220473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7883652699135550781921261 2956369762175831543220473)
            ·
              refine ⟨2217277321631873657415355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2956369762175831543220473 2217277321631873657415355)
              ·
                refine ⟨3325915982447810486123033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2217277321631873657415355 3325915982447810486123033)
                ·
                  refine ⟨2494436986835857864592275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3325915982447810486123033 2494436986835857864592275)
                  ·
                    refine ⟨3741655480253786796888413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2494436986835857864592275 3741655480253786796888413)
                    ·
                      refine ⟨1403120805095170048833155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3741655480253786796888413 1403120805095170048833155)
                      ·
                        rfl

theorem cell23_2732568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_2732568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732568 prefixEnd_2732568 := by exact prefixLift 2732568
  have htrace : WordTrace (prefixWord ++ tailWord_2732568) baseStart_2732568 baseEnd_2732568 := by
    simpa [prefixWord, tailWord_2732568, baseEnd_2732568] using wordTrace_append hprefix tailTrace_2732568
  have hstable : (prefixWord ++ tailWord_2732568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732568).length < 2 ^ (prefixWord ++ tailWord_2732568).sum := by decide
  have hdescent : baseEnd_2732568 < baseStart_2732568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732607 : List Nat := [1, 1, 2, 2, 3, 2, 2, 2, 2, 3, 3]
def baseStart_2732607 : Nat := 118140960795 + 2732607 * 2 ^ 59
def prefixEnd_2732607 : Nat := 4983230072969 + 3 ^ 40 * 2732607 * 2
def baseEnd_2732607 : Nat := 1403140830840695396245475

theorem tailTrace_2732607 : CollatzResearch.WordTrace tailWord_2732607 prefixEnd_2732607 1403140830840695396245475 := by
  unfold tailWord_2732607
  simp only [CollatzResearch.WordTrace]
  refine ⟨99666365211239005965452075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66444243474159337310301383 99666365211239005965452075)
  ·
    refine ⟨149499547816858508948178113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99666365211239005965452075 149499547816858508948178113)
    ·
      refine ⟨112124660862643881711133585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149499547816858508948178113 112124660862643881711133585)
      ·
        refine ⟨84093495646982911283350189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112124660862643881711133585 84093495646982911283350189)
        ·
          refine ⟨31535060867618591731256321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84093495646982911283350189 31535060867618591731256321)
          ·
            refine ⟨23651295650713943798442241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31535060867618591731256321 23651295650713943798442241)
            ·
              refine ⟨17738471738035457848831681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23651295650713943798442241 17738471738035457848831681)
              ·
                refine ⟨13303853803526593386623761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17738471738035457848831681 13303853803526593386623761)
                ·
                  refine ⟨9977890352644945039967821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13303853803526593386623761 9977890352644945039967821)
                  ·
                    refine ⟨3741708882241854389987933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9977890352644945039967821 3741708882241854389987933)
                    ·
                      refine ⟨1403140830840695396245475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3741708882241854389987933 1403140830840695396245475)
                      ·
                        rfl

theorem cell23_2732607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3, 3].length) (baseStart_2732607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732607 prefixEnd_2732607 := by exact prefixLift 2732607
  have htrace : WordTrace (prefixWord ++ tailWord_2732607) baseStart_2732607 baseEnd_2732607 := by
    simpa [prefixWord, tailWord_2732607, baseEnd_2732607] using wordTrace_append hprefix tailTrace_2732607
  have hstable : (prefixWord ++ tailWord_2732607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732607).length < 2 ^ (prefixWord ++ tailWord_2732607).sum := by decide
  have hdescent : baseEnd_2732607 < baseStart_2732607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732697 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 2, 5, 3]
def baseStart_2732697 : Nat := 118140960795 + 2732697 * 2 ^ 59
def prefixEnd_2732697 : Nat := 4983230072969 + 3 ^ 40 * 2732697 * 2
def baseEnd_2732697 : Nat := 1403187044099600044120061

theorem tailTrace_2732697 : CollatzResearch.WordTrace tailWord_2732697 prefixEnd_2732697 1403187044099600044120061 := by
  unfold tailWord_2732697
  simp only [CollatzResearch.WordTrace]
  refine ⟨99669647780912951336228345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66446431853941967557485563 99669647780912951336228345)
  ·
    refine ⟨74752235835684713502171259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99669647780912951336228345 74752235835684713502171259)
    ·
      refine ⟨112128353753527070253256889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74752235835684713502171259 112128353753527070253256889)
      ·
        refine ⟨84096265315145302689942667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112128353753527070253256889 84096265315145302689942667)
        ·
          refine ⟨126144397972717954034914001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84096265315145302689942667 126144397972717954034914001)
          ·
            refine ⟨94608298479538465526185501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126144397972717954034914001 94608298479538465526185501)
            ·
              refine ⟨35478111929826924572319563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94608298479538465526185501 35478111929826924572319563)
              ·
                refine ⟨53217167894740386858479345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35478111929826924572319563 53217167894740386858479345)
                ·
                  refine ⟨39912875921055290143859509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53217167894740386858479345 39912875921055290143859509)
                  ·
                    refine ⟨3741832117598933450986829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39912875921055290143859509 3741832117598933450986829)
                    ·
                      refine ⟨1403187044099600044120061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3741832117598933450986829 1403187044099600044120061)
                      ·
                        rfl

theorem cell23_2732697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 5, 3].length) (baseStart_2732697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732697 prefixEnd_2732697 := by exact prefixLift 2732697
  have htrace : WordTrace (prefixWord ++ tailWord_2732697) baseStart_2732697 baseEnd_2732697 := by
    simpa [prefixWord, tailWord_2732697, baseEnd_2732697] using wordTrace_append hprefix tailTrace_2732697
  have hstable : (prefixWord ++ tailWord_2732697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732697).length < 2 ^ (prefixWord ++ tailWord_2732697).sum := by decide
  have hdescent : baseEnd_2732697 < baseStart_2732697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732718 : List Nat := [4, 1, 4, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_2732718 : Nat := 118140960795 + 2732718 * 2 ^ 59
def prefixEnd_2732718 : Nat := 4983230072969 + 3 ^ 40 * 2732718 * 2
def baseEnd_2732718 : Nat := 1403197827193344461957465

theorem tailTrace_2732718 : CollatzResearch.WordTrace tailWord_2732718 prefixEnd_2732718 1403197827193344461957465 := by
  unfold tailWord_2732718
  simp only [CollatzResearch.WordTrace]
  refine ⟨12458801714229608990342851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66446942475891247948495205 12458801714229608990342851)
  ·
    refine ⟨18688202571344413485514277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12458801714229608990342851 18688202571344413485514277)
    ·
      refine ⟨3504037982127077528533927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18688202571344413485514277 3504037982127077528533927)
      ·
        refine ⟨5256056973190616292800891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3504037982127077528533927 5256056973190616292800891)
        ·
          refine ⟨7884085459785924439201337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5256056973190616292800891 7884085459785924439201337)
          ·
            refine ⟨5913064094839443329401003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7884085459785924439201337 5913064094839443329401003)
            ·
              refine ⟨8869596142259164994101505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5913064094839443329401003 8869596142259164994101505)
              ·
                refine ⟨6652197106694373745576129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8869596142259164994101505 6652197106694373745576129)
                ·
                  refine ⟨4989147830020780309182097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6652197106694373745576129 4989147830020780309182097)
                  ·
                    refine ⟨3741860872515585231886573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4989147830020780309182097 3741860872515585231886573)
                    ·
                      refine ⟨1403197827193344461957465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3741860872515585231886573 1403197827193344461957465)
                      ·
                        rfl

theorem cell23_2732718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_2732718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732718 prefixEnd_2732718 := by exact prefixLift 2732718
  have htrace : WordTrace (prefixWord ++ tailWord_2732718) baseStart_2732718 baseEnd_2732718 := by
    simpa [prefixWord, tailWord_2732718, baseEnd_2732718] using wordTrace_append hprefix tailTrace_2732718
  have hstable : (prefixWord ++ tailWord_2732718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732718).length < 2 ^ (prefixWord ++ tailWord_2732718).sum := by decide
  have hdescent : baseEnd_2732718 < baseStart_2732718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732725 : List Nat := [1, 3, 3, 3, 1, 2, 3, 2, 1, 4]
def baseStart_2732725 : Nat := 118140960795 + 2732725 * 2 ^ 59
def prefixEnd_2732725 : Nat := 4983230072969 + 3 ^ 40 * 2732725 * 2
def baseEnd_2732725 : Nat := 467733807185975311523311

theorem tailTrace_2732725 : CollatzResearch.WordTrace tailWord_2732725 prefixEnd_2732725 467733807185975311523311 := by
  unfold tailWord_2732725
  simp only [CollatzResearch.WordTrace]
  refine ⟨99670669024811512118247629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66447112683207674745498419 99670669024811512118247629)
  ·
    refine ⟨37376500884304317044342861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99670669024811512118247629 37376500884304317044342861)
    ·
      refine ⟨14016187831614118891628573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37376500884304317044342861 14016187831614118891628573)
      ·
        refine ⟨5256070436855294584360715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14016187831614118891628573 5256070436855294584360715)
        ·
          refine ⟨7884105655282941876541073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5256070436855294584360715 7884105655282941876541073)
          ·
            refine ⟨5913079241462206407405805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7884105655282941876541073 5913079241462206407405805)
            ·
              refine ⟨2217404715548327402777177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5913079241462206407405805 2217404715548327402777177)
              ·
                refine ⟨1663053536661245552082883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2217404715548327402777177 1663053536661245552082883)
                ·
                  refine ⟨2494580304991868328124325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1663053536661245552082883 2494580304991868328124325)
                  ·
                    refine ⟨467733807185975311523311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2494580304991868328124325 467733807185975311523311)
                    ·
                      rfl

theorem cell23_2732725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_2732725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732725 prefixEnd_2732725 := by exact prefixLift 2732725
  have htrace : WordTrace (prefixWord ++ tailWord_2732725) baseStart_2732725 baseEnd_2732725 := by
    simpa [prefixWord, tailWord_2732725, baseEnd_2732725] using wordTrace_append hprefix tailTrace_2732725
  have hstable : (prefixWord ++ tailWord_2732725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732725).length < 2 ^ (prefixWord ++ tailWord_2732725).sum := by decide
  have hdescent : baseEnd_2732725 < baseStart_2732725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732734 : List Nat := [4, 2, 1, 1, 2, 1, 2, 2, 3, 5]
def baseStart_2732734 : Nat := 118140960795 + 2732734 * 2 ^ 59
def prefixEnd_2732734 : Nat := 4983230072969 + 3 ^ 40 * 2732734 * 2
def baseEnd_2732734 : Nat := 467735347627938799785797

theorem tailTrace_2732734 : CollatzResearch.WordTrace tailWord_2732734 prefixEnd_2732734 467735347627938799785797 := by
  unfold tailWord_2732734
  simp only [CollatzResearch.WordTrace]
  refine ⟨12458874660222363331915657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66447331521185937770216837 12458874660222363331915657)
  ·
    refine ⟨9344155995166772498936743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12458874660222363331915657 9344155995166772498936743)
    ·
      refine ⟨14016233992750158748405115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9344155995166772498936743 14016233992750158748405115)
      ·
        refine ⟨21024350989125238122607673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14016233992750158748405115 21024350989125238122607673)
        ·
          refine ⟨15768263241843928591955755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21024350989125238122607673 15768263241843928591955755)
          ·
            refine ⟨23652394862765892887933633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15768263241843928591955755 23652394862765892887933633)
            ·
              refine ⟨17739296147074419665950225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23652394862765892887933633 17739296147074419665950225)
              ·
                refine ⟨13304472110305814749462669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17739296147074419665950225 13304472110305814749462669)
                ·
                  refine ⟨4989177041364680531048501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13304472110305814749462669 4989177041364680531048501)
                  ·
                    refine ⟨467735347627938799785797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4989177041364680531048501 467735347627938799785797)
                    ·
                      rfl

theorem cell23_2732734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_2732734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732734 prefixEnd_2732734 := by exact prefixLift 2732734
  have htrace : WordTrace (prefixWord ++ tailWord_2732734) baseStart_2732734 baseEnd_2732734 := by
    simpa [prefixWord, tailWord_2732734, baseEnd_2732734] using wordTrace_append hprefix tailTrace_2732734
  have hstable : (prefixWord ++ tailWord_2732734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732734).length < 2 ^ (prefixWord ++ tailWord_2732734).sum := by decide
  have hdescent : baseEnd_2732734 < baseStart_2732734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732782 : List Nat := [4, 1, 2, 1, 1, 5, 2, 2, 1, 1, 3]
def baseStart_2732782 : Nat := 118140960795 + 2732782 * 2 ^ 59
def prefixEnd_2732782 : Nat := 4983230072969 + 3 ^ 40 * 2732782 * 2
def baseEnd_2732782 : Nat := 1403230689955232211557171

theorem tailTrace_2732782 : CollatzResearch.WordTrace tailWord_2732782 prefixEnd_2732782 1403230689955232211557171 := by
  unfold tailWord_2732782
  simp only [CollatzResearch.WordTrace]
  refine ⟨12459093498200626356634075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66448498657070007235381733 12459093498200626356634075)
  ·
    refine ⟨18688640247300939534951113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12459093498200626356634075 18688640247300939534951113)
    ·
      refine ⟨14016480185475704651213335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18688640247300939534951113 14016480185475704651213335)
      ·
        refine ⟨21024720278213556976820003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14016480185475704651213335 21024720278213556976820003)
        ·
          refine ⟨31537080417320335465230005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21024720278213556976820003 31537080417320335465230005)
          ·
            refine ⟨2956601289123781449865313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31537080417320335465230005 2956601289123781449865313)
            ·
              refine ⟨2217450966842836087398985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2956601289123781449865313 2217450966842836087398985)
              ·
                refine ⟨1663088225132127065549239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2217450966842836087398985 1663088225132127065549239)
                ·
                  refine ⟨2494632337698190598323859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1663088225132127065549239 2494632337698190598323859)
                  ·
                    refine ⟨3741948506547285897485789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2494632337698190598323859 3741948506547285897485789)
                    ·
                      refine ⟨1403230689955232211557171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3741948506547285897485789 1403230689955232211557171)
                      ·
                        rfl

theorem cell23_2732782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_2732782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732782 prefixEnd_2732782 := by exact prefixLift 2732782
  have htrace : WordTrace (prefixWord ++ tailWord_2732782) baseStart_2732782 baseEnd_2732782 := by
    simpa [prefixWord, tailWord_2732782, baseEnd_2732782] using wordTrace_append hprefix tailTrace_2732782
  have hstable : (prefixWord ++ tailWord_2732782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732782).length < 2 ^ (prefixWord ++ tailWord_2732782).sum := by decide
  have hdescent : baseEnd_2732782 < baseStart_2732782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732798 : List Nat := [4, 2, 2, 1, 2, 1, 2, 3, 2, 4]
def baseStart_2732798 : Nat := 118140960795 + 2732798 * 2 ^ 59
def prefixEnd_2732798 : Nat := 4983230072969 + 3 ^ 40 * 2732798 * 2
def baseEnd_2732798 : Nat := 467746301881901382985699

theorem tailTrace_2732798 : CollatzResearch.WordTrace tailWord_2732798 prefixEnd_2732798 467746301881901382985699 := by
  unfold tailWord_2732798
  simp only [CollatzResearch.WordTrace]
  refine ⟨12459166444193380698206881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66448887702364697057103365 12459166444193380698206881)
  ·
    refine ⟨9344374833145035523655161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12459166444193380698206881 9344374833145035523655161)
    ·
      refine ⟨7008281124858776642741371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9344374833145035523655161 7008281124858776642741371)
      ·
        refine ⟨10512421687288164964112057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7008281124858776642741371 10512421687288164964112057)
        ·
          refine ⟨7884316265466123723084043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10512421687288164964112057 7884316265466123723084043)
          ·
            refine ⟨11826474398199185584626065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7884316265466123723084043 11826474398199185584626065)
            ·
              refine ⟨8869855798649389188469549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11826474398199185584626065 8869855798649389188469549)
              ·
                refine ⟨3326195924493520945676081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8869855798649389188469549 3326195924493520945676081)
                ·
                  refine ⟨2494646943370140709257061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3326195924493520945676081 2494646943370140709257061)
                  ·
                    refine ⟨467746301881901382985699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2494646943370140709257061 467746301881901382985699)
                    ·
                      rfl

theorem cell23_2732798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_2732798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732798 prefixEnd_2732798 := by exact prefixLift 2732798
  have htrace : WordTrace (prefixWord ++ tailWord_2732798) baseStart_2732798 baseEnd_2732798 := by
    simpa [prefixWord, tailWord_2732798, baseEnd_2732798] using wordTrace_append hprefix tailTrace_2732798
  have hstable : (prefixWord ++ tailWord_2732798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732798).length < 2 ^ (prefixWord ++ tailWord_2732798).sum := by decide
  have hdescent : baseEnd_2732798 < baseStart_2732798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732821 : List Nat := [1, 3, 2, 1, 2, 2, 2, 2, 4, 1, 3]
def baseStart_2732821 : Nat := 118140960795 + 2732821 * 2 ^ 59
def prefixEnd_2732821 : Nat := 4983230072969 + 3 ^ 40 * 2732821 * 2
def baseEnd_2732821 : Nat := 1403250715700757558969491

theorem tailTrace_2732821 : CollatzResearch.WordTrace tailWord_2732821 prefixEnd_2732821 1403250715700757558969491 := by
  unfold tailWord_2732821
  simp only [CollatzResearch.WordTrace]
  refine ⟨99674170432463720513742317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66449446954975813675828211 99674170432463720513742317)
  ·
    refine ⟨37377813912173895192653369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99674170432463720513742317 37377813912173895192653369)
    ·
      refine ⟨28033360434130421394490027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37377813912173895192653369 28033360434130421394490027)
      ·
        refine ⟨42050040651195632091735041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28033360434130421394490027 42050040651195632091735041)
        ·
          refine ⟨31537530488396724068801281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42050040651195632091735041 31537530488396724068801281)
          ·
            refine ⟨23653147866297543051600961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31537530488396724068801281 23653147866297543051600961)
            ·
              refine ⟨17739860899723157288700721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23653147866297543051600961 17739860899723157288700721)
              ·
                refine ⟨13304895674792367966525541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17739860899723157288700721 13304895674792367966525541)
                ·
                  refine ⟨2494667939023568993723539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13304895674792367966525541 2494667939023568993723539)
                  ·
                    refine ⟨3742001908535353490585309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2494667939023568993723539 3742001908535353490585309)
                    ·
                      refine ⟨1403250715700757558969491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3742001908535353490585309 1403250715700757558969491)
                      ·
                        rfl

theorem cell23_2732821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_2732821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732821 prefixEnd_2732821 := by exact prefixLift 2732821
  have htrace : WordTrace (prefixWord ++ tailWord_2732821) baseStart_2732821 baseEnd_2732821 := by
    simpa [prefixWord, tailWord_2732821, baseEnd_2732821] using wordTrace_append hprefix tailTrace_2732821
  have hstable : (prefixWord ++ tailWord_2732821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732821).length < 2 ^ (prefixWord ++ tailWord_2732821).sum := by decide
  have hdescent : baseEnd_2732821 < baseStart_2732821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732864 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 3]
def baseStart_2732864 : Nat := 118140960795 + 2732864 * 2 ^ 59
def prefixEnd_2732864 : Nat := 4983230072969 + 3 ^ 40 * 2732864 * 2
def baseEnd_2732864 : Nat := 1403272795368900890731793

theorem tailTrace_2732864 : CollatzResearch.WordTrace tailWord_2732864 prefixEnd_2732864 1403272795368900890731793 := by
  unfold tailWord_2732864
  simp only [CollatzResearch.WordTrace]
  refine ⟨49837869385653969428778823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66450492514205292571705097 49837869385653969428778823)
  ·
    refine ⟨74756804078480954143168235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49837869385653969428778823 74756804078480954143168235)
    ·
      refine ⟨112135206117721431214752353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74756804078480954143168235 112135206117721431214752353)
      ·
        refine ⟨84101404588291073411064265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112135206117721431214752353 84101404588291073411064265)
        ·
          refine ⟨63076053441218305058298199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84101404588291073411064265 63076053441218305058298199)
          ·
            refine ⟨94614080161827457587447299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63076053441218305058298199 94614080161827457587447299)
            ·
              refine ⟨141921120242741186381170949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94614080161827457587447299 141921120242741186381170949)
              ·
                refine ⟨26610210045513972446469553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141921120242741186381170949 26610210045513972446469553)
                ·
                  refine ⟨19957657534135479334852165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26610210045513972446469553 19957657534135479334852165)
                  ·
                    refine ⟨3742060787650402375284781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19957657534135479334852165 3742060787650402375284781)
                    ·
                      refine ⟨1403272795368900890731793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3742060787650402375284781 1403272795368900890731793)
                      ·
                        rfl

theorem cell23_2732864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 3].length) (baseStart_2732864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732864 prefixEnd_2732864 := by exact prefixLift 2732864
  have htrace : WordTrace (prefixWord ++ tailWord_2732864) baseStart_2732864 baseEnd_2732864 := by
    simpa [prefixWord, tailWord_2732864, baseEnd_2732864] using wordTrace_append hprefix tailTrace_2732864
  have hstable : (prefixWord ++ tailWord_2732864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732864).length < 2 ^ (prefixWord ++ tailWord_2732864).sum := by decide
  have hdescent : baseEnd_2732864 < baseStart_2732864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732874 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 4, 2, 4]
def baseStart_2732874 : Nat := 118140960795 + 2732874 * 2 ^ 59
def prefixEnd_2732874 : Nat := 4983230072969 + 3 ^ 40 * 2732874 * 2
def baseEnd_2732874 : Nat := 1403277930175445851606747

theorem tailTrace_2732874 : CollatzResearch.WordTrace tailWord_2732874 prefixEnd_2732874 1403277930175445851606747 := by
  unfold tailWord_2732874
  simp only [CollatzResearch.WordTrace]
  refine ⟨24919025875317927641355419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66450735667514473710281117 24919025875317927641355419)
  ·
    refine ⟨37378538812976891462033129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24919025875317927641355419 37378538812976891462033129)
    ·
      refine ⟨28033904109732668596524847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37378538812976891462033129 28033904109732668596524847)
      ·
        refine ⟨42050856164599002894787271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28033904109732668596524847 42050856164599002894787271)
        ·
          refine ⟨63076284246898504342180907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42050856164599002894787271 63076284246898504342180907)
          ·
            refine ⟨94614426370347756513271361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63076284246898504342180907 94614426370347756513271361)
            ·
              refine ⟨70960819777760817384953521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94614426370347756513271361 70960819777760817384953521)
              ·
                refine ⟨53220614833320613038715141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70960819777760817384953521 53220614833320613038715141)
                ·
                  refine ⟨9978865281247614944759089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53220614833320613038715141 9978865281247614944759089)
                  ·
                    refine ⟨7484148960935711208569317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9978865281247614944759089 7484148960935711208569317)
                    ·
                      refine ⟨1403277930175445851606747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7484148960935711208569317 1403277930175445851606747)
                      ·
                        rfl

theorem cell23_2732874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_2732874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732874 prefixEnd_2732874 := by exact prefixLift 2732874
  have htrace : WordTrace (prefixWord ++ tailWord_2732874) baseStart_2732874 baseEnd_2732874 := by
    simpa [prefixWord, tailWord_2732874, baseEnd_2732874] using wordTrace_append hprefix tailTrace_2732874
  have hstable : (prefixWord ++ tailWord_2732874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732874).length < 2 ^ (prefixWord ++ tailWord_2732874).sum := by decide
  have hdescent : baseEnd_2732874 < baseStart_2732874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732881 : List Nat := [1, 2, 2, 1, 6, 1, 1, 1, 2, 1, 5]
def baseStart_2732881 : Nat := 118140960795 + 2732881 * 2 ^ 59
def prefixEnd_2732881 : Nat := 4983230072969 + 3 ^ 40 * 2732881 * 2
def baseEnd_2732881 : Nat := 1403281524540027324219215

theorem tailTrace_2732881 : CollatzResearch.WordTrace tailWord_2732881 prefixEnd_2732881 1403281524540027324219215 := by
  unfold tailWord_2732881
  simp only [CollatzResearch.WordTrace]
  refine ⟨99676358812246350760926497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66450905874830900507284331 99676358812246350760926497)
  ·
    refine ⟨74757269109184763070694873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99676358812246350760926497 74757269109184763070694873)
    ·
      refine ⟨56067951831888572303021155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74757269109184763070694873 56067951831888572303021155)
      ·
        refine ⟨84101927747832858454531733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56067951831888572303021155 84101927747832858454531733)
        ·
          refine ⟨3942277863179665240056175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 84101927747832858454531733 3942277863179665240056175)
          ·
            refine ⟨5913416794769497860084263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3942277863179665240056175 5913416794769497860084263)
            ·
              refine ⟨8870125192154246790126395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5913416794769497860084263 8870125192154246790126395)
              ·
                refine ⟨13305187788231370185189593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8870125192154246790126395 13305187788231370185189593)
                ·
                  refine ⟨9978890841173527638892195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13305187788231370185189593 9978890841173527638892195)
                  ·
                    refine ⟨14968336261760291458338293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9978890841173527638892195 14968336261760291458338293)
                    ·
                      refine ⟨1403281524540027324219215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14968336261760291458338293 1403281524540027324219215)
                      ·
                        rfl

theorem cell23_2732881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 1, 5].length) (baseStart_2732881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732881 prefixEnd_2732881 := by exact prefixLift 2732881
  have htrace : WordTrace (prefixWord ++ tailWord_2732881) baseStart_2732881 baseEnd_2732881 := by
    simpa [prefixWord, tailWord_2732881, baseEnd_2732881] using wordTrace_append hprefix tailTrace_2732881
  have hstable : (prefixWord ++ tailWord_2732881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732881).length < 2 ^ (prefixWord ++ tailWord_2732881).sum := by decide
  have hdescent : baseEnd_2732881 < baseStart_2732881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732901 : List Nat := [1, 3, 1, 3, 1, 1, 2, 6, 5]
def baseStart_2732901 : Nat := 118140960795 + 2732901 * 2 ^ 59
def prefixEnd_2732901 : Nat := 4983230072969 + 3 ^ 40 * 2732901 * 2
def baseEnd_2732901 : Nat := 155921310461457471774347

theorem tailTrace_2732901 : CollatzResearch.WordTrace tailWord_2732901 prefixEnd_2732901 155921310461457471774347 := by
  unfold tailWord_2732901
  simp only [CollatzResearch.WordTrace]
  refine ⟨99677088272173894176654557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66451392181449262784436371 99677088272173894176654557)
  ·
    refine ⟨37378908102065210316245459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99677088272173894176654557 37378908102065210316245459)
    ·
      refine ⟨56068362153097815474368189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37378908102065210316245459 56068362153097815474368189)
      ·
        refine ⟨21025635807411680802888071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56068362153097815474368189 21025635807411680802888071)
        ·
          refine ⟨31538453711117521204332107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21025635807411680802888071 31538453711117521204332107)
          ·
            refine ⟨47307680566676281806498161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31538453711117521204332107 47307680566676281806498161)
            ·
              refine ⟨35480760425007211354873621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47307680566676281806498161 35480760425007211354873621)
              ·
                refine ⟨1663160644922213032259701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35480760425007211354873621 1663160644922213032259701)
                ·
                  refine ⟨155921310461457471774347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1663160644922213032259701 155921310461457471774347)
                  ·
                    rfl

theorem cell23_2732901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6, 5].length) (baseStart_2732901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732901 prefixEnd_2732901 := by exact prefixLift 2732901
  have htrace : WordTrace (prefixWord ++ tailWord_2732901) baseStart_2732901 baseEnd_2732901 := by
    simpa [prefixWord, tailWord_2732901, baseEnd_2732901] using wordTrace_append hprefix tailTrace_2732901
  have hstable : (prefixWord ++ tailWord_2732901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732901).length < 2 ^ (prefixWord ++ tailWord_2732901).sum := by decide
  have hdescent : baseEnd_2732901 < baseStart_2732901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732914 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 3, 7]
def baseStart_2732914 : Nat := 118140960795 + 2732914 * 2 ^ 59
def prefixEnd_2732914 : Nat := 4983230072969 + 3 ^ 40 * 2732914 * 2
def baseEnd_2732914 : Nat := 467766156467208565035521

theorem tailTrace_2732914 : CollatzResearch.WordTrace tailWord_2732914 prefixEnd_2732914 467766156467208565035521 := by
  unfold tailWord_2732914
  simp only [CollatzResearch.WordTrace]
  refine ⟨24919390605281699349219449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66451708280751198264585197 24919390605281699349219449)
  ·
    refine ⟨18689542953961274511914587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24919390605281699349219449 18689542953961274511914587)
    ·
      refine ⟨28034314430941911767871881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18689542953961274511914587 28034314430941911767871881)
      ·
        refine ⟨21025735823206433825903911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28034314430941911767871881 21025735823206433825903911)
        ·
          refine ⟨31538603734809650738855867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21025735823206433825903911 31538603734809650738855867)
          ·
            refine ⟨47307905602214476108283801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31538603734809650738855867 47307905602214476108283801)
            ·
              refine ⟨35480929201660857081212851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47307905602214476108283801 35480929201660857081212851)
              ·
                refine ⟨53221393802491285621819277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35480929201660857081212851 53221393802491285621819277)
                ·
                  refine ⟨19958022675934232108182229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53221393802491285621819277 19958022675934232108182229)
                  ·
                    refine ⟨467766156467208565035521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19958022675934232108182229 467766156467208565035521)
                    ·
                      rfl

theorem cell23_2732914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_2732914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732914 prefixEnd_2732914 := by exact prefixLift 2732914
  have htrace : WordTrace (prefixWord ++ tailWord_2732914) baseStart_2732914 baseEnd_2732914 := by
    simpa [prefixWord, tailWord_2732914, baseEnd_2732914] using wordTrace_append hprefix tailTrace_2732914
  have hstable : (prefixWord ++ tailWord_2732914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732914).length < 2 ^ (prefixWord ++ tailWord_2732914).sum := by decide
  have hdescent : baseEnd_2732914 < baseStart_2732914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732931 : List Nat := [1, 1, 1, 3, 4, 1, 4, 1, 2, 5]
def baseStart_2732931 : Nat := 118140960795 + 2732931 * 2 ^ 59
def prefixEnd_2732931 : Nat := 4983230072969 + 3 ^ 40 * 2732931 * 2
def baseEnd_2732931 : Nat := 467769066190917376197995

theorem tailTrace_2732931 : CollatzResearch.WordTrace tailWord_2732931 prefixEnd_2732931 467769066190917376197995 := by
  unfold tailWord_2732931
  simp only [CollatzResearch.WordTrace]
  refine ⟨99678182462065209300246647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66452121641376806200164431 99678182462065209300246647)
  ·
    refine ⟨149517273693097813950369971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99678182462065209300246647 149517273693097813950369971)
    ·
      refine ⟨224275910539646720925554957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149517273693097813950369971 224275910539646720925554957)
      ·
        refine ⟨84103466452367520347083109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224275910539646720925554957 84103466452367520347083109)
        ·
          refine ⟨15769399959818910065078083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84103466452367520347083109 15769399959818910065078083)
          ·
            refine ⟨23654099939728365097617125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15769399959818910065078083 23654099939728365097617125)
            ·
              refine ⟨4435143738699068455803211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23654099939728365097617125 4435143738699068455803211)
              ·
                refine ⟨6652715608048602683704817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4435143738699068455803211 6652715608048602683704817)
                ·
                  refine ⟨4989536706036452012778613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6652715608048602683704817 4989536706036452012778613)
                  ·
                    refine ⟨467769066190917376197995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4989536706036452012778613 467769066190917376197995)
                    ·
                      rfl

theorem cell23_2732931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 5].length) (baseStart_2732931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732931 prefixEnd_2732931 := by exact prefixLift 2732931
  have htrace : WordTrace (prefixWord ++ tailWord_2732931) baseStart_2732931 baseEnd_2732931 := by
    simpa [prefixWord, tailWord_2732931, baseEnd_2732931] using wordTrace_append hprefix tailTrace_2732931
  have hstable : (prefixWord ++ tailWord_2732931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732931).length < 2 ^ (prefixWord ++ tailWord_2732931).sum := by decide
  have hdescent : baseEnd_2732931 < baseStart_2732931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732951 : List Nat := [1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 4]
def baseStart_2732951 : Nat := 118140960795 + 2732951 * 2 ^ 59
def prefixEnd_2732951 : Nat := 4983230072969 + 3 ^ 40 * 2732951 * 2
def baseEnd_2732951 : Nat := 1403317468185842050343893

theorem tailTrace_2732951 : CollatzResearch.WordTrace tailWord_2732951 prefixEnd_2732951 1403317468185842050343893 := by
  unfold tailWord_2732951
  simp only [CollatzResearch.WordTrace]
  refine ⟨99678911921992752715974707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66452607947995168477316471 99678911921992752715974707)
  ·
    refine ⟨149518367882989129073962061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99678911921992752715974707 149518367882989129073962061)
    ·
      refine ⟨56069387956120923402735773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149518367882989129073962061 56069387956120923402735773)
      ·
        refine ⟨21026020483545346276025915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56069387956120923402735773 21026020483545346276025915)
        ·
          refine ⟨31539030725318019414038873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21026020483545346276025915 31539030725318019414038873)
          ·
            refine ⟨23654273043988514560529155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31539030725318019414038873 23654273043988514560529155)
            ·
              refine ⟨35481409565982771840793733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23654273043988514560529155 35481409565982771840793733)
              ·
                refine ⟨6652764293621769720148825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35481409565982771840793733 6652764293621769720148825)
                ·
                  refine ⟨4989573220216327290111619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6652764293621769720148825 4989573220216327290111619)
                  ·
                    refine ⟨7484359830324490935167429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4989573220216327290111619 7484359830324490935167429)
                    ·
                      refine ⟨1403317468185842050343893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7484359830324490935167429 1403317468185842050343893)
                      ·
                        rfl

theorem cell23_2732951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_2732951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732951 prefixEnd_2732951 := by exact prefixLift 2732951
  have htrace : WordTrace (prefixWord ++ tailWord_2732951) baseStart_2732951 baseEnd_2732951 := by
    simpa [prefixWord, tailWord_2732951, baseEnd_2732951] using wordTrace_append hprefix tailTrace_2732951
  have hstable : (prefixWord ++ tailWord_2732951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732951).length < 2 ^ (prefixWord ++ tailWord_2732951).sum := by decide
  have hdescent : baseEnd_2732951 < baseStart_2732951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732982 : List Nat := [5, 1, 4, 1, 1, 1, 1, 1, 1, 7]
def baseStart_2732982 : Nat := 118140960795 + 2732982 * 2 ^ 59
def prefixEnd_2732982 : Nat := 4983230072969 + 3 ^ 40 * 2732982 * 2
def baseEnd_2732982 : Nat := 467777795362043809685417

theorem tailTrace_2732982 : CollatzResearch.WordTrace tailWord_2732982 prefixEnd_2732982 467777795362043809685417 := by
  unfold tailWord_2732982
  simp only [CollatzResearch.WordTrace]
  refine ⟨6230002661555027813147075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66453361723253630006902133 6230002661555027813147075)
  ·
    refine ⟨9345003992332541719720613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6230002661555027813147075 9345003992332541719720613)
    ·
      refine ⟨1752188248562351572447615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9345003992332541719720613 1752188248562351572447615)
      ·
        refine ⟨2628282372843527358671423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1752188248562351572447615 2628282372843527358671423)
        ·
          refine ⟨3942423559265291038007135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2628282372843527358671423 3942423559265291038007135)
          ·
            refine ⟨5913635338897936557010703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3942423559265291038007135 5913635338897936557010703)
            ·
              refine ⟨8870453008346904835516055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5913635338897936557010703 8870453008346904835516055)
              ·
                refine ⟨13305679512520357253274083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8870453008346904835516055 13305679512520357253274083)
                ·
                  refine ⟨19958519268780535879911125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13305679512520357253274083 19958519268780535879911125)
                  ·
                    refine ⟨467777795362043809685417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19958519268780535879911125 467777795362043809685417)
                    ·
                      rfl

theorem cell23_2732982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_2732982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2732982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2732982 prefixEnd_2732982 := by exact prefixLift 2732982
  have htrace : WordTrace (prefixWord ++ tailWord_2732982) baseStart_2732982 baseEnd_2732982 := by
    simpa [prefixWord, tailWord_2732982, baseEnd_2732982] using wordTrace_append hprefix tailTrace_2732982
  have hstable : (prefixWord ++ tailWord_2732982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732982).length < 2 ^ (prefixWord ++ tailWord_2732982).sum := by decide
  have hdescent : baseEnd_2732982 < baseStart_2732982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733028 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 6, 3, 2]
def baseStart_2733028 : Nat := 118140960795 + 2733028 * 2 ^ 59
def prefixEnd_2733028 : Nat := 4983230072969 + 3 ^ 40 * 2733028 * 2
def baseEnd_2733028 : Nat := 1403357006196238249081039

theorem tailTrace_2733028 : CollatzResearch.WordTrace tailWord_2733028 prefixEnd_2733028 1403357006196238249081039 := by
  unfold tailWord_2733028
  simp only [CollatzResearch.WordTrace]
  refine ⟨49840860171356897433263869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66454480228475863244351825 49840860171356897433263869)
  ·
    refine ⟨18690322564258836537473951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49840860171356897433263869 18690322564258836537473951)
    ·
      refine ⟨28035483846388254806210927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18690322564258836537473951 28035483846388254806210927)
      ·
        refine ⟨42053225769582382209316391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28035483846388254806210927 42053225769582382209316391)
        ·
          refine ⟨63079838654373573313974587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42053225769582382209316391 63079838654373573313974587)
          ·
            refine ⟨94619757981560359970961881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63079838654373573313974587 94619757981560359970961881)
            ·
              refine ⟨70964818486170269978221411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94619757981560359970961881 70964818486170269978221411)
              ·
                refine ⟨106447227729255404967332117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70964818486170269978221411 106447227729255404967332117)
                ·
                  refine ⟨4989713799808847107843693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 106447227729255404967332117 4989713799808847107843693)
                  ·
                    refine ⟨1871142674928317665441385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4989713799808847107843693 1871142674928317665441385)
                    ·
                      refine ⟨1403357006196238249081039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1871142674928317665441385 1403357006196238249081039)
                      ·
                        rfl

theorem cell23_2733028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 6, 3, 2].length) (baseStart_2733028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733028 prefixEnd_2733028 := by exact prefixLift 2733028
  have htrace : WordTrace (prefixWord ++ tailWord_2733028) baseStart_2733028 baseEnd_2733028 := by
    simpa [prefixWord, tailWord_2733028, baseEnd_2733028] using wordTrace_append hprefix tailTrace_2733028
  have hstable : (prefixWord ++ tailWord_2733028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733028).length < 2 ^ (prefixWord ++ tailWord_2733028).sum := by decide
  have hdescent : baseEnd_2733028 < baseStart_2733028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733052 : List Nat := [2, 2, 2, 1, 2, 3, 3, 3, 1, 1, 3]
def baseStart_2733052 : Nat := 118140960795 + 2733052 * 2 ^ 59
def prefixEnd_2733052 : Nat := 4983230072969 + 3 ^ 40 * 2733052 * 2
def baseEnd_2733052 : Nat := 1403369329731946155180929

theorem tailTrace_2733052 : CollatzResearch.WordTrace tailWord_2733052 prefixEnd_2733052 1403369329731946155180929 := by
  unfold tailWord_2733052
  simp only [CollatzResearch.WordTrace]
  refine ⟨49841297847313423482700705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66455063796417897976934273 49841297847313423482700705)
  ·
    refine ⟨37380973385485067612025529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49841297847313423482700705 37380973385485067612025529)
    ·
      refine ⟨28035730039113800709019147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37380973385485067612025529 28035730039113800709019147)
      ·
        refine ⟨42053595058670701063528721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28035730039113800709019147 42053595058670701063528721)
        ·
          refine ⟨31540196294003025797646541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42053595058670701063528721 31540196294003025797646541)
          ·
            refine ⟨11827573610251134674117453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31540196294003025797646541 11827573610251134674117453)
            ·
              refine ⟨4435340103844175502794045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11827573610251134674117453 4435340103844175502794045)
              ·
                refine ⟨1663252538941565813547767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4435340103844175502794045 1663252538941565813547767)
                ·
                  refine ⟨2494878808412348720321651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1663252538941565813547767 2494878808412348720321651)
                  ·
                    refine ⟨3742318212618523080482477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2494878808412348720321651 3742318212618523080482477)
                    ·
                      refine ⟨1403369329731946155180929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3742318212618523080482477 1403369329731946155180929)
                      ·
                        rfl

theorem cell23_2733052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3, 1, 1, 3].length) (baseStart_2733052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733052 prefixEnd_2733052 := by exact prefixLift 2733052
  have htrace : WordTrace (prefixWord ++ tailWord_2733052) baseStart_2733052 baseEnd_2733052 := by
    simpa [prefixWord, tailWord_2733052, baseEnd_2733052] using wordTrace_append hprefix tailTrace_2733052
  have hstable : (prefixWord ++ tailWord_2733052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733052).length < 2 ^ (prefixWord ++ tailWord_2733052).sum := by decide
  have hdescent : baseEnd_2733052 < baseStart_2733052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
