import V185TrunkScan23Chunk0036

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_219865 : List Nat := [1, 2, 1, 2, 3, 2, 2, 2, 2, 6]
def baseStart_219865 : Nat := 118140960795 + 219865 * 2 ^ 59
def prefixEnd_219865 : Nat := 4983230072969 + 3 ^ 40 * 219865 * 2
def baseEnd_219865 : Nat := 37632141366962503625455

theorem tailTrace_219865 : CollatzResearch.WordTrace tailWord_219865 prefixEnd_219865 37632141366962503625455 := by
  unfold tailWord_219865
  simp only [CollatzResearch.WordTrace]
  refine ⟨8019135348474129797605049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5346090232316086531736699 8019135348474129797605049)
  ·
    refine ⟨6014351511355597348203787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8019135348474129797605049 6014351511355597348203787)
    ·
      refine ⟨9021527267033396022305681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6014351511355597348203787 9021527267033396022305681)
      ·
        refine ⟨6766145450275047016729261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9021527267033396022305681 6766145450275047016729261)
        ·
          refine ⟨2537304543853142631273473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6766145450275047016729261 2537304543853142631273473)
          ·
            refine ⟨1902978407889856973455105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2537304543853142631273473 1902978407889856973455105)
            ·
              refine ⟨1427233805917392730091329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1902978407889856973455105 1427233805917392730091329)
              ·
                refine ⟨1070425354438044547568497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1427233805917392730091329 1070425354438044547568497)
                ·
                  refine ⟨802819015828533410676373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1070425354438044547568497 802819015828533410676373)
                  ·
                    refine ⟨37632141366962503625455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 802819015828533410676373 37632141366962503625455)
                    ·
                      rfl

theorem cell23_219865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 6].length) (baseStart_219865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219865 prefixEnd_219865 := by exact prefixLift 219865
  have htrace : WordTrace (prefixWord ++ tailWord_219865) baseStart_219865 baseEnd_219865 := by
    simpa [prefixWord, tailWord_219865, baseEnd_219865] using wordTrace_append hprefix tailTrace_219865
  have hstable : (prefixWord ++ tailWord_219865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219865).length < 2 ^ (prefixWord ++ tailWord_219865).sum := by decide
  have hdescent : baseEnd_219865 < baseStart_219865 := by decide
  rcases family_descends (prefixWord ++ tailWord_219865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219872 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 5, 4, 2]
def baseStart_219872 : Nat := 118140960795 + 219872 * 2 ^ 59
def prefixEnd_219872 : Nat := 4983230072969 + 3 ^ 40 * 219872 * 2
def baseEnd_219872 : Nat := 112900018465468983488833

theorem tailTrace_219872 : CollatzResearch.WordTrace tailWord_219872 prefixEnd_219872 112900018465468983488833 := by
  unfold tailWord_219872
  simp only [CollatzResearch.WordTrace]
  refine ⟨4009695329724384996554935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5346260439632513328739913 4009695329724384996554935)
  ·
    refine ⟨6014542994586577494832403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4009695329724384996554935 6014542994586577494832403)
    ·
      refine ⟨9021814491879866242248605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6014542994586577494832403 9021814491879866242248605)
      ·
        refine ⟨3383180434454949840843227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9021814491879866242248605 3383180434454949840843227)
        ·
          refine ⟨5074770651682424761264841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3383180434454949840843227 5074770651682424761264841)
          ·
            refine ⟨3806077988761818570948631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5074770651682424761264841 3806077988761818570948631)
            ·
              refine ⟨5709116983142727856422947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3806077988761818570948631 5709116983142727856422947)
              ·
                refine ⟨8563675474714091784634421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5709116983142727856422947 8563675474714091784634421)
                ·
                  refine ⟨802844575754446104809477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8563675474714091784634421 802844575754446104809477)
                  ·
                    refine ⟨150533357953958644651777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 802844575754446104809477 150533357953958644651777)
                    ·
                      refine ⟨112900018465468983488833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 150533357953958644651777 112900018465468983488833)
                      ·
                        rfl

theorem cell23_219872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 5, 4, 2].length) (baseStart_219872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219872 prefixEnd_219872 := by exact prefixLift 219872
  have htrace : WordTrace (prefixWord ++ tailWord_219872) baseStart_219872 baseEnd_219872 := by
    simpa [prefixWord, tailWord_219872, baseEnd_219872] using wordTrace_append hprefix tailTrace_219872
  have hstable : (prefixWord ++ tailWord_219872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219872).length < 2 ^ (prefixWord ++ tailWord_219872).sum := by decide
  have hdescent : baseEnd_219872 < baseStart_219872 := by decide
  rcases family_descends (prefixWord ++ tailWord_219872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219889 : List Nat := [1, 2, 2, 2, 2, 2, 4, 1, 1, 4, 2]
def baseStart_219889 : Nat := 118140960795 + 219889 * 2 ^ 59
def prefixEnd_219889 : Nat := 4983230072969 + 3 ^ 40 * 219889 * 2
def baseEnd_219889 : Nat := 112908747636595416976255

theorem tailTrace_219889 : CollatzResearch.WordTrace tailWord_219889 prefixEnd_219889 112908747636595416976255 := by
  unfold tailWord_219889
  simp only [CollatzResearch.WordTrace]
  refine ⟨8020010700387181896478721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5346673800258121264319147 8020010700387181896478721)
  ·
    refine ⟨6015008025290386422359041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8020010700387181896478721 6015008025290386422359041)
    ·
      refine ⟨4511256018967789816769281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6015008025290386422359041 4511256018967789816769281)
      ·
        refine ⟨3383442014225842362576961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4511256018967789816769281 3383442014225842362576961)
        ·
          refine ⟨2537581510669381771932721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3383442014225842362576961 2537581510669381771932721)
          ·
            refine ⟨1903186133002036328949541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2537581510669381771932721 1903186133002036328949541)
            ·
              refine ⟨356847399937881811678039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1903186133002036328949541 356847399937881811678039)
              ·
                refine ⟨535271099906822717517059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356847399937881811678039 535271099906822717517059)
                ·
                  refine ⟨802906649860234076275589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 535271099906822717517059 802906649860234076275589)
                  ·
                    refine ⟨150544996848793889301673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 802906649860234076275589 150544996848793889301673)
                    ·
                      refine ⟨112908747636595416976255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 150544996848793889301673 112908747636595416976255)
                      ·
                        rfl

theorem cell23_219889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 4, 2].length) (baseStart_219889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219889 prefixEnd_219889 := by exact prefixLift 219889
  have htrace : WordTrace (prefixWord ++ tailWord_219889) baseStart_219889 baseEnd_219889 := by
    simpa [prefixWord, tailWord_219889, baseEnd_219889] using wordTrace_append hprefix tailTrace_219889
  have hstable : (prefixWord ++ tailWord_219889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219889).length < 2 ^ (prefixWord ++ tailWord_219889).sum := by decide
  have hdescent : baseEnd_219889 < baseStart_219889 := by decide
  rcases family_descends (prefixWord ++ tailWord_219889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219905 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_219905 : Nat := 118140960795 + 219905 * 2 ^ 59
def prefixEnd_219905 : Nat := 4983230072969 + 3 ^ 40 * 219905 * 2
def baseEnd_219905 : Nat := 112916963327067354376181

theorem tailTrace_219905 : CollatzResearch.WordTrace tailWord_219905 prefixEnd_219905 112916963327067354376181 := by
  unfold tailWord_219905
  simp only [CollatzResearch.WordTrace]
  refine ⟨8020594268329216629061169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5347062845552811086040779 8020594268329216629061169)
  ·
    refine ⟨6015445701246912471795877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8020594268329216629061169 6015445701246912471795877)
    ·
      refine ⟨1127896068983796088461727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6015445701246912471795877 1127896068983796088461727)
      ·
        refine ⟨1691844103475694132692591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1127896068983796088461727 1691844103475694132692591)
        ·
          refine ⟨2537766155213541199038887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1691844103475694132692591 2537766155213541199038887)
          ·
            refine ⟨3806649232820311798558331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2537766155213541199038887 3806649232820311798558331)
            ·
              refine ⟨5709973849230467697837497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3806649232820311798558331 5709973849230467697837497)
              ·
                refine ⟨4282480386922850773378123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5709973849230467697837497 4282480386922850773378123)
                ·
                  refine ⟨6423720580384276160067185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4282480386922850773378123 6423720580384276160067185)
                  ·
                    refine ⟨4817790435288207120050389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6423720580384276160067185 4817790435288207120050389)
                    ·
                      refine ⟨112916963327067354376181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 4817790435288207120050389 112916963327067354376181)
                      ·
                        rfl

theorem cell23_219905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_219905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219905 prefixEnd_219905 := by exact prefixLift 219905
  have htrace : WordTrace (prefixWord ++ tailWord_219905) baseStart_219905 baseEnd_219905 := by
    simpa [prefixWord, tailWord_219905, baseEnd_219905] using wordTrace_append hprefix tailTrace_219905
  have hstable : (prefixWord ++ tailWord_219905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219905).length < 2 ^ (prefixWord ++ tailWord_219905).sum := by decide
  have hdescent : baseEnd_219905 < baseStart_219905 := by decide
  rcases family_descends (prefixWord ++ tailWord_219905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219906 : List Nat := [3, 4, 1, 1, 1, 2, 2, 2, 1, 4, 2]
def baseStart_219906 : Nat := 118140960795 + 219906 * 2 ^ 59
def prefixEnd_219906 : Nat := 4983230072969 + 3 ^ 40 * 219906 * 2
def baseEnd_219906 : Nat := 112917476807721850463677

theorem tailTrace_219906 : CollatzResearch.WordTrace tailWord_219906 prefixEnd_219906 112917476807721850463677 := by
  unfold tailWord_219906
  simp only [CollatzResearch.WordTrace]
  refine ⟨2005157685331398449961893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5347087160883729199898381 2005157685331398449961893)
  ·
    refine ⟨375967065999637209367855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2005157685331398449961893 375967065999637209367855)
    ·
      refine ⟨563950598999455814051783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375967065999637209367855 563950598999455814051783)
      ·
        refine ⟨845925898499183721077675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563950598999455814051783 845925898499183721077675)
        ·
          refine ⟨1268888847748775581616513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845925898499183721077675 1268888847748775581616513)
          ·
            refine ⟨951666635811581686212385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1268888847748775581616513 951666635811581686212385)
            ·
              refine ⟨713749976858686264659289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 951666635811581686212385 713749976858686264659289)
              ·
                refine ⟨535312482644014698494467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 713749976858686264659289 535312482644014698494467)
                ·
                  refine ⟨802968723966022047741701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 535312482644014698494467 802968723966022047741701)
                  ·
                    refine ⟨150556635743629133951569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 802968723966022047741701 150556635743629133951569)
                    ·
                      refine ⟨112917476807721850463677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 150556635743629133951569 112917476807721850463677)
                      ·
                        rfl

theorem cell23_219906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_219906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219906 prefixEnd_219906 := by exact prefixLift 219906
  have htrace : WordTrace (prefixWord ++ tailWord_219906) baseStart_219906 baseEnd_219906 := by
    simpa [prefixWord, tailWord_219906, baseEnd_219906] using wordTrace_append hprefix tailTrace_219906
  have hstable : (prefixWord ++ tailWord_219906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219906).length < 2 ^ (prefixWord ++ tailWord_219906).sum := by decide
  have hdescent : baseEnd_219906 < baseStart_219906 := by decide
  rcases family_descends (prefixWord ++ tailWord_219906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219940 : List Nat := [2, 3, 1, 3, 3, 1, 3, 1, 2, 2, 2]
def baseStart_219940 : Nat := 118140960795 + 219940 * 2 ^ 59
def prefixEnd_219940 : Nat := 4983230072969 + 3 ^ 40 * 219940 * 2
def baseEnd_219940 : Nat := 112934935149974717438521

theorem tailTrace_219940 : CollatzResearch.WordTrace tailWord_219940 prefixEnd_219940 112934935149974717438521 := by
  unfold tailWord_219940
  simp only [CollatzResearch.WordTrace]
  refine ⟨4010935411601208803292637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5347913882134945071056849 4010935411601208803292637)
  ·
    refine ⟨1504100779350453301234739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4010935411601208803292637 1504100779350453301234739)
    ·
      refine ⟨2256151169025679951852109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1504100779350453301234739 2256151169025679951852109)
      ·
        refine ⟨846056688384629981944541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2256151169025679951852109 846056688384629981944541)
        ·
          refine ⟨317271258144236243229203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 846056688384629981944541 317271258144236243229203)
          ·
            refine ⟨475906887216354364843805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317271258144236243229203 475906887216354364843805)
            ·
              refine ⟨178465082706132886816427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 475906887216354364843805 178465082706132886816427)
              ·
                refine ⟨267697624059199330224641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178465082706132886816427 267697624059199330224641)
                ·
                  refine ⟨200773218044399497668481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267697624059199330224641 200773218044399497668481)
                  ·
                    refine ⟨150579913533299623251361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 200773218044399497668481 150579913533299623251361)
                    ·
                      refine ⟨112934935149974717438521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 150579913533299623251361 112934935149974717438521)
                      ·
                        rfl

theorem cell23_219940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_219940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219940 prefixEnd_219940 := by exact prefixLift 219940
  have htrace : WordTrace (prefixWord ++ tailWord_219940) baseStart_219940 baseEnd_219940 := by
    simpa [prefixWord, tailWord_219940, baseEnd_219940] using wordTrace_append hprefix tailTrace_219940
  have hstable : (prefixWord ++ tailWord_219940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219940).length < 2 ^ (prefixWord ++ tailWord_219940).sum := by decide
  have hdescent : baseEnd_219940 < baseStart_219940 := by decide
  rcases family_descends (prefixWord ++ tailWord_219940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219995 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 7]
def baseStart_219995 : Nat := 118140960795 + 219995 * 2 ^ 59
def prefixEnd_219995 : Nat := 4983230072969 + 3 ^ 40 * 219995 * 2
def baseEnd_219995 : Nat := 112963176585972002250767

theorem tailTrace_219995 : CollatzResearch.WordTrace tailWord_219995 prefixEnd_219995 112963176585972002250767 := by
  unfold tailWord_219995
  simp only [CollatzResearch.WordTrace]
  refine ⟨8023876838003161999837439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5349251225335441333224959 8023876838003161999837439)
  ·
    refine ⟨12035815257004742999756159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8023876838003161999837439 12035815257004742999756159)
    ·
      refine ⟨18053722885507114499634239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12035815257004742999756159 18053722885507114499634239)
      ·
        refine ⟨27080584328260671749451359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18053722885507114499634239 27080584328260671749451359)
        ·
          refine ⟨40620876492391007624177039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27080584328260671749451359 40620876492391007624177039)
          ·
            refine ⟨60931314738586511436265559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40620876492391007624177039 60931314738586511436265559)
            ·
              refine ⟨91396972107879767154398339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60931314738586511436265559 91396972107879767154398339)
              ·
                refine ⟨137095458161819650731597509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91396972107879767154398339 137095458161819650731597509)
                ·
                  refine ⟨25705398405341184512174533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137095458161819650731597509 25705398405341184512174533)
                  ·
                    refine ⟨4819762201001472096032725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25705398405341184512174533 4819762201001472096032725)
                    ·
                      refine ⟨112963176585972002250767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 4819762201001472096032725 112963176585972002250767)
                      ·
                        rfl

theorem cell23_219995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 7].length) (baseStart_219995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_219995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_219995 prefixEnd_219995 := by exact prefixLift 219995
  have htrace : WordTrace (prefixWord ++ tailWord_219995) baseStart_219995 baseEnd_219995 := by
    simpa [prefixWord, tailWord_219995, baseEnd_219995] using wordTrace_append hprefix tailTrace_219995
  have hstable : (prefixWord ++ tailWord_219995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219995).length < 2 ^ (prefixWord ++ tailWord_219995).sum := by decide
  have hdescent : baseEnd_219995 < baseStart_219995 := by decide
  rcases family_descends (prefixWord ++ tailWord_219995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220040 : List Nat := [2, 1, 3, 3, 2, 3, 2, 2, 1, 4]
def baseStart_220040 : Nat := 118140960795 + 220040 * 2 ^ 59
def prefixEnd_220040 : Nat := 4983230072969 + 3 ^ 40 * 220040 * 2
def baseEnd_220040 : Nat := 37662094405141442062687

theorem tailTrace_220040 : CollatzResearch.WordTrace tailWord_220040 prefixEnd_220040 37662094405141442062687 := by
  unfold tailWord_220040
  simp only [CollatzResearch.WordTrace]
  refine ⟨4012759061420067342612787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5350345415226756456817049 4012759061420067342612787)
  ·
    refine ⟨6019138592130101013919181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4012759061420067342612787 6019138592130101013919181)
    ·
      refine ⟨2257176972048787880219693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6019138592130101013919181 2257176972048787880219693)
      ·
        refine ⟨846441364518295455082385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2257176972048787880219693 846441364518295455082385)
        ·
          refine ⟨634831023388721591311789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 846441364518295455082385 634831023388721591311789)
          ·
            refine ⟨238061633770770596741921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 634831023388721591311789 238061633770770596741921)
            ·
              refine ⟨178546225328077947556441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238061633770770596741921 178546225328077947556441)
              ·
                refine ⟨133909668996058460667331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178546225328077947556441 133909668996058460667331)
                ·
                  refine ⟨200864503494087691000997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133909668996058460667331 200864503494087691000997)
                  ·
                    refine ⟨37662094405141442062687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 200864503494087691000997 37662094405141442062687)
                    ·
                      rfl

theorem cell23_220040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_220040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220040 prefixEnd_220040 := by exact prefixLift 220040
  have htrace : WordTrace (prefixWord ++ tailWord_220040) baseStart_220040 baseEnd_220040 := by
    simpa [prefixWord, tailWord_220040, baseEnd_220040] using wordTrace_append hprefix tailTrace_220040
  have hstable : (prefixWord ++ tailWord_220040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220040).length < 2 ^ (prefixWord ++ tailWord_220040).sum := by decide
  have hdescent : baseEnd_220040 < baseStart_220040 := by decide
  rcases family_descends (prefixWord ++ tailWord_220040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220082 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6]
def baseStart_220082 : Nat := 118140960795 + 220082 * 2 ^ 59
def prefixEnd_220082 : Nat := 4983230072969 + 3 ^ 40 * 220082 * 2
def baseEnd_220082 : Nat := 113007849402913161862867

theorem tailTrace_220082 : CollatzResearch.WordTrace tailWord_220082 prefixEnd_220082 113007849402913161862867 := by
  unfold tailWord_220082
  simp only [CollatzResearch.WordTrace]
  refine ⟨2006762497171993964563625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5351366659125317238836333 2006762497171993964563625)
  ·
    refine ⟨1505071872878995473422719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2006762497171993964563625 1505071872878995473422719)
    ·
      refine ⟨2257607809318493210134079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1505071872878995473422719 2257607809318493210134079)
      ·
        refine ⟨3386411713977739815201119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2257607809318493210134079 3386411713977739815201119)
        ·
          refine ⟨5079617570966609722801679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3386411713977739815201119 5079617570966609722801679)
          ·
            refine ⟨7619426356449914584202519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5079617570966609722801679 7619426356449914584202519)
            ·
              refine ⟨11429139534674871876303779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7619426356449914584202519 11429139534674871876303779)
              ·
                refine ⟨17143709302012307814455669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11429139534674871876303779 17143709302012307814455669)
                ·
                  refine ⟨1607222747063653857605219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17143709302012307814455669 1607222747063653857605219)
                  ·
                    refine ⟨2410834120595480786407829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1607222747063653857605219 2410834120595480786407829)
                    ·
                      refine ⟨113007849402913161862867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2410834120595480786407829 113007849402913161862867)
                      ·
                        rfl

theorem cell23_220082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_220082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220082 prefixEnd_220082 := by exact prefixLift 220082
  have htrace : WordTrace (prefixWord ++ tailWord_220082) baseStart_220082 baseEnd_220082 := by
    simpa [prefixWord, tailWord_220082, baseEnd_220082] using wordTrace_append hprefix tailTrace_220082
  have hstable : (prefixWord ++ tailWord_220082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220082).length < 2 ^ (prefixWord ++ tailWord_220082).sum := by decide
  have hdescent : baseEnd_220082 < baseStart_220082 := by decide
  rcases family_descends (prefixWord ++ tailWord_220082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220096 : List Nat := [2, 1, 1, 2, 3, 3, 3, 2, 2, 4]
def baseStart_220096 : Nat := 118140960795 + 220096 * 2 ^ 59
def prefixEnd_220096 : Nat := 4983230072969 + 3 ^ 40 * 220096 * 2
def baseEnd_220096 : Nat := 37671679377358702362601

theorem tailTrace_220096 : CollatzResearch.WordTrace tailWord_220096 prefixEnd_220096 37671679377358702362601 := by
  unfold tailWord_220096
  simp only [CollatzResearch.WordTrace]
  refine ⟨4013780305318628124632071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5351707073758170832842761 4013780305318628124632071)
  ·
    refine ⟨6020670457977942186948107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4013780305318628124632071 6020670457977942186948107)
    ·
      refine ⟨9031005686966913280422161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6020670457977942186948107 9031005686966913280422161)
      ·
        refine ⟨6773254265225184960316621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9031005686966913280422161 6773254265225184960316621)
        ·
          refine ⟨2539970349459444360118733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6773254265225184960316621 2539970349459444360118733)
          ·
            refine ⟨952488881047291635044525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2539970349459444360118733 952488881047291635044525)
            ·
              refine ⟨357183330392734363141697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 952488881047291635044525 357183330392734363141697)
              ·
                refine ⟨267887497794550772356273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 357183330392734363141697 267887497794550772356273)
                ·
                  refine ⟨200915623345913079267205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267887497794550772356273 200915623345913079267205)
                  ·
                    refine ⟨37671679377358702362601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 200915623345913079267205 37671679377358702362601)
                    ·
                      rfl

theorem cell23_220096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 2, 4].length) (baseStart_220096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220096 prefixEnd_220096 := by exact prefixLift 220096
  have htrace : WordTrace (prefixWord ++ tailWord_220096) baseStart_220096 baseEnd_220096 := by
    simpa [prefixWord, tailWord_220096, baseEnd_220096] using wordTrace_append hprefix tailTrace_220096
  have hstable : (prefixWord ++ tailWord_220096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220096).length < 2 ^ (prefixWord ++ tailWord_220096).sum := by decide
  have hdescent : baseEnd_220096 < baseStart_220096 := by decide
  rcases family_descends (prefixWord ++ tailWord_220096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220116 : List Nat := [2, 4, 1, 2, 1, 2, 3, 1, 1, 2, 4]
def baseStart_220116 : Nat := 118140960795 + 220116 * 2 ^ 59
def prefixEnd_220116 : Nat := 4983230072969 + 3 ^ 40 * 220116 * 2
def baseEnd_220116 : Nat := 113025307745166028837711

theorem tailTrace_220116 : CollatzResearch.WordTrace tailWord_220116 prefixEnd_220116 113025307745166028837711 := by
  unfold tailWord_220116
  simp only [CollatzResearch.WordTrace]
  refine ⟨4014145035282399832496101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5352193380376533109994801 4014145035282399832496101)
  ·
    refine ⟨752652194115449968593019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4014145035282399832496101 752652194115449968593019)
    ·
      refine ⟨1128978291173174952889529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 752652194115449968593019 1128978291173174952889529)
      ·
        refine ⟨846733718379881214667147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1128978291173174952889529 846733718379881214667147)
        ·
          refine ⟨1270100577569821822000721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 846733718379881214667147 1270100577569821822000721)
          ·
            refine ⟨952575433177366366500541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1270100577569821822000721 952575433177366366500541)
            ·
              refine ⟨357215787441512387437703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 952575433177366366500541 357215787441512387437703)
              ·
                refine ⟨535823681162268581156555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357215787441512387437703 535823681162268581156555)
                ·
                  refine ⟨803735521743402871734833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 535823681162268581156555 803735521743402871734833)
                  ·
                    refine ⟨602801641307552153801125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 803735521743402871734833 602801641307552153801125)
                    ·
                      refine ⟨113025307745166028837711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 602801641307552153801125 113025307745166028837711)
                      ·
                        rfl

theorem cell23_220116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_220116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220116 prefixEnd_220116 := by exact prefixLift 220116
  have htrace : WordTrace (prefixWord ++ tailWord_220116) baseStart_220116 baseEnd_220116 := by
    simpa [prefixWord, tailWord_220116, baseEnd_220116] using wordTrace_append hprefix tailTrace_220116
  have hstable : (prefixWord ++ tailWord_220116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220116).length < 2 ^ (prefixWord ++ tailWord_220116).sum := by decide
  have hdescent : baseEnd_220116 < baseStart_220116 := by decide
  rcases family_descends (prefixWord ++ tailWord_220116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220119 : List Nat := [1, 1, 3, 2, 1, 1, 2, 5, 1, 3, 3]
def baseStart_220119 : Nat := 118140960795 + 220119 * 2 ^ 59
def prefixEnd_220119 : Nat := 4983230072969 + 3 ^ 40 * 220119 * 2
def baseEnd_220119 : Nat := 113026848187129517100197

theorem tailTrace_220119 : CollatzResearch.WordTrace tailWord_220119 prefixEnd_220119 113026848187129517100197 := by
  unfold tailWord_220119
  simp only [CollatzResearch.WordTrace]
  refine ⟨8028399489553931177351411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5352266326369287451567607 8028399489553931177351411)
  ·
    refine ⟨12042599234330896766027117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8028399489553931177351411 12042599234330896766027117)
    ·
      refine ⟨4515974712874086287260169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12042599234330896766027117 4515974712874086287260169)
      ·
        refine ⟨3386981034655564715445127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4515974712874086287260169 3386981034655564715445127)
        ·
          refine ⟨5080471551983347073167691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3386981034655564715445127 5080471551983347073167691)
          ·
            refine ⟨7620707327975020609751537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5080471551983347073167691 7620707327975020609751537)
            ·
              refine ⟨5715530495981265457313653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7620707327975020609751537 5715530495981265457313653)
              ·
                refine ⟨535830983998243636623155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5715530495981265457313653 535830983998243636623155)
                ·
                  refine ⟨803746475997365454934733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 535830983998243636623155 803746475997365454934733)
                  ·
                    refine ⟨301404928499012045600525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 803746475997365454934733 301404928499012045600525)
                    ·
                      refine ⟨113026848187129517100197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 301404928499012045600525 113026848187129517100197)
                      ·
                        rfl

theorem cell23_220119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_220119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220119 prefixEnd_220119 := by exact prefixLift 220119
  have htrace : WordTrace (prefixWord ++ tailWord_220119) baseStart_220119 baseEnd_220119 := by
    simpa [prefixWord, tailWord_220119, baseEnd_220119] using wordTrace_append hprefix tailTrace_220119
  have hstable : (prefixWord ++ tailWord_220119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220119).length < 2 ^ (prefixWord ++ tailWord_220119).sum := by decide
  have hdescent : baseEnd_220119 < baseStart_220119 := by decide
  rcases family_descends (prefixWord ++ tailWord_220119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220136 : List Nat := [2, 1, 4, 1, 1, 1, 3, 2, 4, 1, 3]
def baseStart_220136 : Nat := 118140960795 + 220136 * 2 ^ 59
def prefixEnd_220136 : Nat := 4983230072969 + 3 ^ 40 * 220136 * 2
def baseEnd_220136 : Nat := 113035577358255950587619

theorem tailTrace_220136 : CollatzResearch.WordTrace tailWord_220136 prefixEnd_220136 113035577358255950587619 := by
  unfold tailWord_220136
  simp only [CollatzResearch.WordTrace]
  refine ⟨4014509765246171540360131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5352679686994895387146841 4014509765246171540360131)
  ·
    refine ⟨6021764647869257310540197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4014509765246171540360131 6021764647869257310540197)
    ·
      refine ⟨1129080871475485745726287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6021764647869257310540197 1129080871475485745726287)
      ·
        refine ⟨1693621307213228618589431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1129080871475485745726287 1693621307213228618589431)
        ·
          refine ⟨2540431960819842927884147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1693621307213228618589431 2540431960819842927884147)
          ·
            refine ⟨3810647941229764391826221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2540431960819842927884147 3810647941229764391826221)
            ·
              refine ⟨1428992977961161646934833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3810647941229764391826221 1428992977961161646934833)
              ·
                refine ⟨1071744733470871235201125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1428992977961161646934833 1071744733470871235201125)
                ·
                  refine ⟨200952137525788356600211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1071744733470871235201125 200952137525788356600211)
                  ·
                    refine ⟨301428206288682534900317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 200952137525788356600211 301428206288682534900317)
                    ·
                      refine ⟨113035577358255950587619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 301428206288682534900317 113035577358255950587619)
                      ·
                        rfl

theorem cell23_220136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_220136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220136 prefixEnd_220136 := by exact prefixLift 220136
  have htrace : WordTrace (prefixWord ++ tailWord_220136) baseStart_220136 baseEnd_220136 := by
    simpa [prefixWord, tailWord_220136, baseEnd_220136] using wordTrace_append hprefix tailTrace_220136
  have hstable : (prefixWord ++ tailWord_220136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220136).length < 2 ^ (prefixWord ++ tailWord_220136).sum := by decide
  have hdescent : baseEnd_220136 < baseStart_220136 := by decide
  rcases family_descends (prefixWord ++ tailWord_220136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220148 : List Nat := [2, 6, 2, 1, 1, 1, 3, 2, 1, 1, 3]
def baseStart_220148 : Nat := 118140960795 + 220148 * 2 ^ 59
def prefixEnd_220148 : Nat := 4983230072969 + 3 ^ 40 * 220148 * 2
def baseEnd_220148 : Nat := 113041739126109903637565

theorem tailTrace_220148 : CollatzResearch.WordTrace tailWord_220148 prefixEnd_220148 113041739126109903637565 := by
  unfold tailWord_220148
  simp only [CollatzResearch.WordTrace]
  refine ⟨4014728603224434565078549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5352971470965912753438065 4014728603224434565078549)
  ·
    refine ⟨188190403276145370238057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4014728603224434565078549 188190403276145370238057)
    ·
      refine ⟨141142802457109027678543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188190403276145370238057 141142802457109027678543)
      ·
        refine ⟨211714203685663541517815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141142802457109027678543 211714203685663541517815)
        ·
          refine ⟨317571305528495312276723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211714203685663541517815 317571305528495312276723)
          ·
            refine ⟨476356958292742968415085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317571305528495312276723 476356958292742968415085)
            ·
              refine ⟨178633859359778613155657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 476356958292742968415085 178633859359778613155657)
              ·
                refine ⟨133975394519833959866743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178633859359778613155657 133975394519833959866743)
                ·
                  refine ⟨200963091779750939800115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133975394519833959866743 200963091779750939800115)
                  ·
                    refine ⟨301444637669626409700173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 200963091779750939800115 301444637669626409700173)
                    ·
                      refine ⟨113041739126109903637565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 301444637669626409700173 113041739126109903637565)
                      ·
                        rfl

theorem cell23_220148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_220148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220148 prefixEnd_220148 := by exact prefixLift 220148
  have htrace : WordTrace (prefixWord ++ tailWord_220148) baseStart_220148 baseEnd_220148 := by
    simpa [prefixWord, tailWord_220148, baseEnd_220148] using wordTrace_append hprefix tailTrace_220148
  have hstable : (prefixWord ++ tailWord_220148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220148).length < 2 ^ (prefixWord ++ tailWord_220148).sum := by decide
  have hdescent : baseEnd_220148 < baseStart_220148 := by decide
  rcases family_descends (prefixWord ++ tailWord_220148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220170 : List Nat := [3, 1, 2, 2, 3, 1, 4, 1, 2, 1, 3]
def baseStart_220170 : Nat := 118140960795 + 220170 * 2 ^ 59
def prefixEnd_220170 : Nat := 4983230072969 + 3 ^ 40 * 220170 * 2
def baseEnd_220170 : Nat := 113053035700508817562463

theorem tailTrace_220170 : CollatzResearch.WordTrace tailWord_220170 prefixEnd_220170 113053035700508817562463 := by
  unfold tailWord_220170
  simp only [CollatzResearch.WordTrace]
  refine ⟨2007564903092291721864491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5353506408246111258305309 2007564903092291721864491)
  ·
    refine ⟨3011347354638437582796737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2007564903092291721864491 3011347354638437582796737)
    ·
      refine ⟨2258510515978828187097553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3011347354638437582796737 2258510515978828187097553)
      ·
        refine ⟨1693882886984121140323165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2258510515978828187097553 1693882886984121140323165)
        ·
          refine ⟨635206082619045427621187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1693882886984121140323165 635206082619045427621187)
          ·
            refine ⟨952809123928568141431781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635206082619045427621187 952809123928568141431781)
            ·
              refine ⟨178651710736606526518459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 952809123928568141431781 178651710736606526518459)
              ·
                refine ⟨267977566104909789777689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178651710736606526518459 267977566104909789777689)
                ·
                  refine ⟨200983174578682342333267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267977566104909789777689 200983174578682342333267)
                  ·
                    refine ⟨301474761868023513499901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 200983174578682342333267 301474761868023513499901)
                    ·
                      refine ⟨113053035700508817562463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 301474761868023513499901 113053035700508817562463)
                      ·
                        rfl

theorem cell23_220170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_220170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220170 prefixEnd_220170 := by exact prefixLift 220170
  have htrace : WordTrace (prefixWord ++ tailWord_220170) baseStart_220170 baseEnd_220170 := by
    simpa [prefixWord, tailWord_220170, baseEnd_220170] using wordTrace_append hprefix tailTrace_220170
  have hstable : (prefixWord ++ tailWord_220170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220170).length < 2 ^ (prefixWord ++ tailWord_220170).sum := by decide
  have hdescent : baseEnd_220170 < baseStart_220170 := by decide
  rcases family_descends (prefixWord ++ tailWord_220170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220193 : List Nat := [1, 2, 3, 2, 3, 2, 1, 2, 1, 4, 2]
def baseStart_220193 : Nat := 118140960795 + 220193 * 2 ^ 59
def prefixEnd_220193 : Nat := 4983230072969 + 3 ^ 40 * 220193 * 2
def baseEnd_220193 : Nat := 113064845755562227574857

theorem tailTrace_220193 : CollatzResearch.WordTrace tailWord_220193 prefixEnd_220193 113064845755562227574857 := by
  unfold tailWord_220193
  simp only [CollatzResearch.WordTrace]
  refine ⟨8031098491285841815545233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5354065660857227877030155 8031098491285841815545233)
  ·
    refine ⟨6023323868464381361658925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8031098491285841815545233 6023323868464381361658925)
    ·
      refine ⟨2258746450674143010622097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6023323868464381361658925 2258746450674143010622097)
      ·
        refine ⟨1694059838005607257966573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2258746450674143010622097 1694059838005607257966573)
        ·
          refine ⟨635272439252102721737465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1694059838005607257966573 635272439252102721737465)
          ·
            refine ⟨476454329439077041303099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 635272439252102721737465 476454329439077041303099)
            ·
              refine ⟨714681494158615561954649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476454329439077041303099 714681494158615561954649)
              ·
                refine ⟨536011120618961671465987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 714681494158615561954649 536011120618961671465987)
                ·
                  refine ⟨804016680928442507198981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 536011120618961671465987 804016680928442507198981)
                  ·
                    refine ⟨150753127674082970099809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 804016680928442507198981 150753127674082970099809)
                    ·
                      refine ⟨113064845755562227574857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 150753127674082970099809 113064845755562227574857)
                      ·
                        rfl

theorem cell23_220193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_220193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220193 prefixEnd_220193 := by exact prefixLift 220193
  have htrace : WordTrace (prefixWord ++ tailWord_220193) baseStart_220193 baseEnd_220193 := by
    simpa [prefixWord, tailWord_220193, baseEnd_220193] using wordTrace_append hprefix tailTrace_220193
  have hstable : (prefixWord ++ tailWord_220193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220193).length < 2 ^ (prefixWord ++ tailWord_220193).sum := by decide
  have hdescent : baseEnd_220193 < baseStart_220193 := by decide
  rcases family_descends (prefixWord ++ tailWord_220193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220196 : List Nat := [2, 3, 1, 4, 1, 1, 2, 1, 2, 1, 5]
def baseStart_220196 : Nat := 118140960795 + 220196 * 2 ^ 59
def prefixEnd_220196 : Nat := 4983230072969 + 3 ^ 40 * 220196 * 2
def baseEnd_220196 : Nat := 113066386197525715837343

theorem tailTrace_220196 : CollatzResearch.WordTrace tailWord_220196 prefixEnd_220196 113066386197525715837343 := by
  unfold tailWord_220196
  simp only [CollatzResearch.WordTrace]
  refine ⟨4015603955137486663952221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5354138606849982218602961 4015603955137486663952221)
  ·
    refine ⟨1505851483176557498982083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4015603955137486663952221 1505851483176557498982083)
    ·
      refine ⟨2258777224764836248473125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1505851483176557498982083 2258777224764836248473125)
      ·
        refine ⟨423520729643406796588711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2258777224764836248473125 423520729643406796588711)
        ·
          refine ⟨635281094465110194883067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423520729643406796588711 635281094465110194883067)
          ·
            refine ⟨952921641697665292324601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635281094465110194883067 952921641697665292324601)
            ·
              refine ⟨714691231273248969243451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 952921641697665292324601 714691231273248969243451)
              ·
                refine ⟨1072036846909873453865177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 714691231273248969243451 1072036846909873453865177)
                ·
                  refine ⟨804027635182405090398883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1072036846909873453865177 804027635182405090398883)
                  ·
                    refine ⟨1206041452773607635598325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 804027635182405090398883 1206041452773607635598325)
                    ·
                      refine ⟨113066386197525715837343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1206041452773607635598325 113066386197525715837343)
                      ·
                        rfl

theorem cell23_220196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_220196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220196 prefixEnd_220196 := by exact prefixLift 220196
  have htrace : WordTrace (prefixWord ++ tailWord_220196) baseStart_220196 baseEnd_220196 := by
    simpa [prefixWord, tailWord_220196, baseEnd_220196] using wordTrace_append hprefix tailTrace_220196
  have hstable : (prefixWord ++ tailWord_220196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220196).length < 2 ^ (prefixWord ++ tailWord_220196).sum := by decide
  have hdescent : baseEnd_220196 < baseStart_220196 := by decide
  rcases family_descends (prefixWord ++ tailWord_220196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220206 : List Nat := [4, 1, 3, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_220206 : Nat := 118140960795 + 220206 * 2 ^ 59
def prefixEnd_220206 : Nat := 4983230072969 + 3 ^ 40 * 220206 * 2
def baseEnd_220206 : Nat := 113071521004070676712297

theorem tailTrace_220206 : CollatzResearch.WordTrace tailWord_220206 prefixEnd_220206 113071521004070676712297 := by
  unfold tailWord_220206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1003946580029843129471059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5354381760159163357178981 1003946580029843129471059)
  ·
    refine ⟨1505919870044764694206589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1003946580029843129471059 1505919870044764694206589)
    ·
      refine ⟨564719951266786760327471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1505919870044764694206589 564719951266786760327471)
      ·
        refine ⟨847079926900180140491207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564719951266786760327471 847079926900180140491207)
        ·
          refine ⟨1270619890350270210736811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 847079926900180140491207 1270619890350270210736811)
          ·
            refine ⟨1905929835525405316105217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1270619890350270210736811 1905929835525405316105217)
            ·
              refine ⟨1429447376644053987078913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1905929835525405316105217 1429447376644053987078913)
              ·
                refine ⟨1072085532483040490309185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1429447376644053987078913 1072085532483040490309185)
                ·
                  refine ⟨804064149362280367731889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1072085532483040490309185 804064149362280367731889)
                  ·
                    refine ⟨603048112021710275798917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 804064149362280367731889 603048112021710275798917)
                    ·
                      refine ⟨113071521004070676712297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 603048112021710275798917 113071521004070676712297)
                      ·
                        rfl

theorem cell23_220206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_220206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220206 prefixEnd_220206 := by exact prefixLift 220206
  have htrace : WordTrace (prefixWord ++ tailWord_220206) baseStart_220206 baseEnd_220206 := by
    simpa [prefixWord, tailWord_220206, baseEnd_220206] using wordTrace_append hprefix tailTrace_220206
  have hstable : (prefixWord ++ tailWord_220206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220206).length < 2 ^ (prefixWord ++ tailWord_220206).sum := by decide
  have hdescent : baseEnd_220206 < baseStart_220206 := by decide
  rcases family_descends (prefixWord ++ tailWord_220206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220210 : List Nat := [3, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2]
def baseStart_220210 : Nat := 118140960795 + 220210 * 2 ^ 59
def prefixEnd_220210 : Nat := 4983230072969 + 3 ^ 40 * 220210 * 2
def baseEnd_220210 : Nat := 113073574926688661062279

theorem tailTrace_220210 : CollatzResearch.WordTrace tailWord_220210 prefixEnd_220210 113073574926688661062279 := by
  unfold tailWord_220210
  simp only [CollatzResearch.WordTrace]
  refine ⟨2007929633056063429728521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5354479021482835812609389 2007929633056063429728521)
  ·
    refine ⟨1505947224792047572296391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2007929633056063429728521 1505947224792047572296391)
    ·
      refine ⟨2258920837188071358444587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1505947224792047572296391 2258920837188071358444587)
      ·
        refine ⟨3388381255782107037666881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2258920837188071358444587 3388381255782107037666881)
        ·
          refine ⟨2541285941836580278250161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3388381255782107037666881 2541285941836580278250161)
          ·
            refine ⟨1905964456377435208687621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2541285941836580278250161 1905964456377435208687621)
            ·
              refine ⟨357368335570769101628929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1905964456377435208687621 357368335570769101628929)
              ·
                refine ⟨268026251678076826221697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 357368335570769101628929 268026251678076826221697)
                ·
                  refine ⟨201019688758557619666273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268026251678076826221697 201019688758557619666273)
                  ·
                    refine ⟨150764766568918214749705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 201019688758557619666273 150764766568918214749705)
                    ·
                      refine ⟨113073574926688661062279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 150764766568918214749705 113073574926688661062279)
                      ·
                        rfl

theorem cell23_220210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2].length) (baseStart_220210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220210 prefixEnd_220210 := by exact prefixLift 220210
  have htrace : WordTrace (prefixWord ++ tailWord_220210) baseStart_220210 baseEnd_220210 := by
    simpa [prefixWord, tailWord_220210, baseEnd_220210] using wordTrace_append hprefix tailTrace_220210
  have hstable : (prefixWord ++ tailWord_220210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220210).length < 2 ^ (prefixWord ++ tailWord_220210).sum := by decide
  have hdescent : baseEnd_220210 < baseStart_220210 := by decide
  rcases family_descends (prefixWord ++ tailWord_220210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220229 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 4, 5]
def baseStart_220229 : Nat := 118140960795 + 220229 * 2 ^ 59
def prefixEnd_220229 : Nat := 4983230072969 + 3 ^ 40 * 220229 * 2
def baseEnd_220229 : Nat := 37694443686374695574897

theorem tailTrace_220229 : CollatzResearch.WordTrace tailWord_220229 prefixEnd_220229 37694443686374695574897 := by
  unfold tailWord_220229
  simp only [CollatzResearch.WordTrace]
  refine ⟨8032411519155419963855741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5354941012770279975903827 8032411519155419963855741)
  ·
    refine ⟨3012154319683282486445903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8032411519155419963855741 3012154319683282486445903)
    ·
      refine ⟨4518231479524923729668855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3012154319683282486445903 4518231479524923729668855)
      ·
        refine ⟨6777347219287385594503283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4518231479524923729668855 6777347219287385594503283)
        ·
          refine ⟨10166020828931078391754925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6777347219287385594503283 10166020828931078391754925)
          ·
            refine ⟨3812257810849154396908097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10166020828931078391754925 3812257810849154396908097)
            ·
              refine ⟨2859193358136865797681073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3812257810849154396908097 2859193358136865797681073)
              ·
                refine ⟨2144395018602649348260805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2859193358136865797681073 2144395018602649348260805)
                ·
                  refine ⟨402074065987996752798901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2144395018602649348260805 402074065987996752798901)
                  ·
                    refine ⟨37694443686374695574897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 402074065987996752798901 37694443686374695574897)
                    ·
                      rfl

theorem cell23_220229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 5].length) (baseStart_220229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220229 prefixEnd_220229 := by exact prefixLift 220229
  have htrace : WordTrace (prefixWord ++ tailWord_220229) baseStart_220229 baseEnd_220229 := by
    simpa [prefixWord, tailWord_220229, baseEnd_220229] using wordTrace_append hprefix tailTrace_220229
  have hstable : (prefixWord ++ tailWord_220229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220229).length < 2 ^ (prefixWord ++ tailWord_220229).sum := by decide
  have hdescent : baseEnd_220229 < baseStart_220229 := by decide
  rcases family_descends (prefixWord ++ tailWord_220229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220236 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 4, 5, 2]
def baseStart_220236 : Nat := 118140960795 + 220236 * 2 ^ 59
def prefixEnd_220236 : Nat := 4983230072969 + 3 ^ 40 * 220236 * 2
def baseEnd_220236 : Nat := 113086925423705559337159

theorem tailTrace_220236 : CollatzResearch.WordTrace tailWord_220236 prefixEnd_220236 113086925423705559337159 := by
  unfold tailWord_220236
  simp only [CollatzResearch.WordTrace]
  refine ⟨4016333415065030079680281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5355111220086706772907041 4016333415065030079680281)
  ·
    refine ⟨3012250061298772559760211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4016333415065030079680281 3012250061298772559760211)
    ·
      refine ⟨4518375091948158839640317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3012250061298772559760211 4518375091948158839640317)
      ·
        refine ⟨1694390659480559564865119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4518375091948158839640317 1694390659480559564865119)
        ·
          refine ⟨2541585989220839347297679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1694390659480559564865119 2541585989220839347297679)
          ·
            refine ⟨3812378983831259020946519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2541585989220839347297679 3812378983831259020946519)
            ·
              refine ⟨5718568475746888531419779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3812378983831259020946519 5718568475746888531419779)
              ·
                refine ⟨8577852713620332797129669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5718568475746888531419779 8577852713620332797129669)
                ·
                  refine ⟨1608347383803812399461813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8577852713620332797129669 1608347383803812399461813)
                  ·
                    refine ⟨150782567231607412449545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1608347383803812399461813 150782567231607412449545)
                    ·
                      refine ⟨113086925423705559337159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 150782567231607412449545 113086925423705559337159)
                      ·
                        rfl

theorem cell23_220236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_220236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220236 prefixEnd_220236 := by exact prefixLift 220236
  have htrace : WordTrace (prefixWord ++ tailWord_220236) baseStart_220236 baseEnd_220236 := by
    simpa [prefixWord, tailWord_220236, baseEnd_220236] using wordTrace_append hprefix tailTrace_220236
  have hstable : (prefixWord ++ tailWord_220236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220236).length < 2 ^ (prefixWord ++ tailWord_220236).sum := by decide
  have hdescent : baseEnd_220236 < baseStart_220236 := by decide
  rcases family_descends (prefixWord ++ tailWord_220236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220279 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 6]
def baseStart_220279 : Nat := 118140960795 + 220279 * 2 ^ 59
def prefixEnd_220279 : Nat := 4983230072969 + 3 ^ 40 * 220279 * 2
def baseEnd_220279 : Nat := 113109005091848891099461

theorem tailTrace_220279 : CollatzResearch.WordTrace tailWord_220279 prefixEnd_220279 113109005091848891099461 := by
  unfold tailWord_220279
  simp only [CollatzResearch.WordTrace]
  refine ⟨8034235168974278503175891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5356156779316185668783927 8034235168974278503175891)
  ·
    refine ⟨12051352753461417754763837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8034235168974278503175891 12051352753461417754763837)
    ·
      refine ⟨4519257282548031658036439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12051352753461417754763837 4519257282548031658036439)
      ·
        refine ⟨6778885923822047487054659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4519257282548031658036439 6778885923822047487054659)
        ·
          refine ⟨10168328885733071230581989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6778885923822047487054659 10168328885733071230581989)
          ·
            refine ⟨1906561666074950855734123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10168328885733071230581989 1906561666074950855734123)
            ·
              refine ⟨2859842499112426283601185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1906561666074950855734123 2859842499112426283601185)
              ·
                refine ⟨2144881874334319712700889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2859842499112426283601185 2144881874334319712700889)
                ·
                  refine ⟨1608661405750739784525667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2144881874334319712700889 1608661405750739784525667)
                  ·
                    refine ⟨2412992108626109676788501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1608661405750739784525667 2412992108626109676788501)
                    ·
                      refine ⟨113109005091848891099461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2412992108626109676788501 113109005091848891099461)
                      ·
                        rfl

theorem cell23_220279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_220279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220279 prefixEnd_220279 := by exact prefixLift 220279
  have htrace : WordTrace (prefixWord ++ tailWord_220279) baseStart_220279 baseEnd_220279 := by
    simpa [prefixWord, tailWord_220279, baseEnd_220279] using wordTrace_append hprefix tailTrace_220279
  have hstable : (prefixWord ++ tailWord_220279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220279).length < 2 ^ (prefixWord ++ tailWord_220279).sum := by decide
  have hdescent : baseEnd_220279 < baseStart_220279 := by decide
  rcases family_descends (prefixWord ++ tailWord_220279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220306 : List Nat := [3, 2, 3, 1, 1, 2, 1, 2, 8]
def baseStart_220306 : Nat := 118140960795 + 220306 * 2 ^ 59
def prefixEnd_220306 : Nat := 4983230072969 + 3 ^ 40 * 220306 * 2
def baseEnd_220306 : Nat := 12569207674391142829093

theorem tailTrace_220306 : CollatzResearch.WordTrace tailWord_220306 prefixEnd_220306 12569207674391142829093 := by
  unfold tailWord_220306
  simp only [CollatzResearch.WordTrace]
  refine ⟨2008804984969115528602193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5356813293250974742939181 2008804984969115528602193)
  ·
    refine ⟨1506603738726836646451645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2008804984969115528602193 1506603738726836646451645)
    ·
      refine ⟨564976402022563742419367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1506603738726836646451645 564976402022563742419367)
      ·
        refine ⟨847464603033845613629051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564976402022563742419367 847464603033845613629051)
        ·
          refine ⟨1271196904550768420443577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 847464603033845613629051 1271196904550768420443577)
          ·
            refine ⟨953397678413076315332683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1271196904550768420443577 953397678413076315332683)
            ·
              refine ⟨1430096517619614472999025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 953397678413076315332683 1430096517619614472999025)
              ·
                refine ⟨1072572388214710854749269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1430096517619614472999025 1072572388214710854749269)
                ·
                  refine ⟨12569207674391142829093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1072572388214710854749269 12569207674391142829093)
                  ·
                    rfl

theorem cell23_220306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 8].length) (baseStart_220306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220306 prefixEnd_220306 := by exact prefixLift 220306
  have htrace : WordTrace (prefixWord ++ tailWord_220306) baseStart_220306 baseEnd_220306 := by
    simpa [prefixWord, tailWord_220306, baseEnd_220306] using wordTrace_append hprefix tailTrace_220306
  have hstable : (prefixWord ++ tailWord_220306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220306).length < 2 ^ (prefixWord ++ tailWord_220306).sum := by decide
  have hdescent : baseEnd_220306 < baseStart_220306 := by decide
  rcases family_descends (prefixWord ++ tailWord_220306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220309 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 1, 1, 8]
def baseStart_220309 : Nat := 118140960795 + 220309 * 2 ^ 59
def prefixEnd_220309 : Nat := 4983230072969 + 3 ^ 40 * 220309 * 2
def baseEnd_220309 : Nat := 113124409511483773724323

theorem tailTrace_220309 : CollatzResearch.WordTrace tailWord_220309 prefixEnd_220309 113124409511483773724323 := by
  unfold tailWord_220309
  simp only [CollatzResearch.WordTrace]
  refine ⟨8035329358865593626767981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5356886239243729084511987 8035329358865593626767981)
  ·
    refine ⟨3013248509574597610037993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8035329358865593626767981 3013248509574597610037993)
    ·
      refine ⟨2259936382180948207528495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3013248509574597610037993 2259936382180948207528495)
      ·
        refine ⟨3389904573271422311292743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2259936382180948207528495 3389904573271422311292743)
        ·
          refine ⟨5084856859907133466939115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3389904573271422311292743 5084856859907133466939115)
          ·
            refine ⟨7627285289860700200408673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5084856859907133466939115 7627285289860700200408673)
            ·
              refine ⟨5720463967395525150306505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7627285289860700200408673 5720463967395525150306505)
              ·
                refine ⟨4290347975546643862729879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5720463967395525150306505 4290347975546643862729879)
                ·
                  refine ⟨6435521963319965794094819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4290347975546643862729879 6435521963319965794094819)
                  ·
                    refine ⟨9653282944979948691142229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6435521963319965794094819 9653282944979948691142229)
                    ·
                      refine ⟨113124409511483773724323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 9653282944979948691142229 113124409511483773724323)
                      ·
                        rfl

theorem cell23_220309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_220309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220309 prefixEnd_220309 := by exact prefixLift 220309
  have htrace : WordTrace (prefixWord ++ tailWord_220309) baseStart_220309 baseEnd_220309 := by
    simpa [prefixWord, tailWord_220309, baseEnd_220309] using wordTrace_append hprefix tailTrace_220309
  have hstable : (prefixWord ++ tailWord_220309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220309).length < 2 ^ (prefixWord ++ tailWord_220309).sum := by decide
  have hdescent : baseEnd_220309 < baseStart_220309 := by decide
  rcases family_descends (prefixWord ++ tailWord_220309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220329 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 4, 4, 5]
def baseStart_220329 : Nat := 118140960795 + 220329 * 2 ^ 59
def prefixEnd_220329 : Nat := 4983230072969 + 3 ^ 40 * 220329 * 2
def baseEnd_220329 : Nat := 113134679124573695474231

theorem tailTrace_220329 : CollatzResearch.WordTrace tailWord_220329 prefixEnd_220329 113134679124573695474231 := by
  unfold tailWord_220329
  simp only [CollatzResearch.WordTrace]
  refine ⟨8036058818793137042496041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5357372545862091361664027 8036058818793137042496041)
  ·
    refine ⟨6027044114094852781872031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8036058818793137042496041 6027044114094852781872031)
    ·
      refine ⟨9040566171142279172808047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6027044114094852781872031 9040566171142279172808047)
      ·
        refine ⟨13560849256713418759212071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9040566171142279172808047 13560849256713418759212071)
        ·
          refine ⟨20341273885070128138818107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13560849256713418759212071 20341273885070128138818107)
          ·
            refine ⟨30511910827605192208227161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20341273885070128138818107 30511910827605192208227161)
            ·
              refine ⟨22883933120703894156170371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30511910827605192208227161 22883933120703894156170371)
              ·
                refine ⟨34325899681055841234255557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22883933120703894156170371 34325899681055841234255557)
                ·
                  refine ⟨6436106190197970231422917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34325899681055841234255557 6436106190197970231422917)
                  ·
                    refine ⟨1206769910662119418391797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6436106190197970231422917 1206769910662119418391797)
                    ·
                      refine ⟨113134679124573695474231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1206769910662119418391797 113134679124573695474231)
                      ·
                        rfl

theorem cell23_220329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 4, 5].length) (baseStart_220329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220329 prefixEnd_220329 := by exact prefixLift 220329
  have htrace : WordTrace (prefixWord ++ tailWord_220329) baseStart_220329 baseEnd_220329 := by
    simpa [prefixWord, tailWord_220329, baseEnd_220329] using wordTrace_append hprefix tailTrace_220329
  have hstable : (prefixWord ++ tailWord_220329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220329).length < 2 ^ (prefixWord ++ tailWord_220329).sum := by decide
  have hdescent : baseEnd_220329 < baseStart_220329 := by decide
  rcases family_descends (prefixWord ++ tailWord_220329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220343 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 4, 3, 2]
def baseStart_220343 : Nat := 118140960795 + 220343 * 2 ^ 59
def prefixEnd_220343 : Nat := 4983230072969 + 3 ^ 40 * 220343 * 2
def baseEnd_220343 : Nat := 113141867853736640699167

theorem tailTrace_220343 : CollatzResearch.WordTrace tailWord_220343 prefixEnd_220343 113141867853736640699167 := by
  unfold tailWord_220343
  simp only [CollatzResearch.WordTrace]
  refine ⟨8036569440742417433505683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5357712960494944955670455 8036569440742417433505683)
  ·
    refine ⟨12054854161113626150258525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8036569440742417433505683 12054854161113626150258525)
    ·
      refine ⟨4520570310417609806346947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12054854161113626150258525 4520570310417609806346947)
      ·
        refine ⟨6780855465626414709520421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4520570310417609806346947 6780855465626414709520421)
        ·
          refine ⟨1271410399804952758035079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6780855465626414709520421 1271410399804952758035079)
          ·
            refine ⟨1907115599707429137052619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1271410399804952758035079 1907115599707429137052619)
            ·
              refine ⟨2860673399561143705578929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1907115599707429137052619 2860673399561143705578929)
              ·
                refine ⟨2145505049670857779184197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2860673399561143705578929 2145505049670857779184197)
                ·
                  refine ⟨402282196813285833597037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2145505049670857779184197 402282196813285833597037)
                  ·
                    refine ⟨150855823804982187598889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 402282196813285833597037 150855823804982187598889)
                    ·
                      refine ⟨113141867853736640699167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 150855823804982187598889 113141867853736640699167)
                      ·
                        rfl

theorem cell23_220343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 3, 2].length) (baseStart_220343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220343 prefixEnd_220343 := by exact prefixLift 220343
  have htrace : WordTrace (prefixWord ++ tailWord_220343) baseStart_220343 baseEnd_220343 := by
    simpa [prefixWord, tailWord_220343, baseEnd_220343] using wordTrace_append hprefix tailTrace_220343
  have hstable : (prefixWord ++ tailWord_220343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220343).length < 2 ^ (prefixWord ++ tailWord_220343).sum := by decide
  have hdescent : baseEnd_220343 < baseStart_220343 := by decide
  rcases family_descends (prefixWord ++ tailWord_220343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220354 : List Nat := [3, 5, 1, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_220354 : Nat := 118140960795 + 220354 * 2 ^ 59
def prefixEnd_220354 : Nat := 4983230072969 + 3 ^ 40 * 220354 * 2
def baseEnd_220354 : Nat := 113147516140936097661617

theorem tailTrace_220354 : CollatzResearch.WordTrace tailWord_220354 prefixEnd_220354 113147516140936097661617 := by
  unfold tailWord_220354
  simp only [CollatzResearch.WordTrace]
  refine ⟨2009242660925641578039029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5357980429135044208104077 2009242660925641578039029)
  ·
    refine ⟨188366499461778897941159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2009242660925641578039029 188366499461778897941159)
    ·
      refine ⟨282549749192668346911739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188366499461778897941159 282549749192668346911739)
      ·
        refine ⟨423824623789002520367609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282549749192668346911739 423824623789002520367609)
        ·
          refine ⟨317868467841751890275707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423824623789002520367609 317868467841751890275707)
          ·
            refine ⟨476802701762627835413561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317868467841751890275707 476802701762627835413561)
            ·
              refine ⟨357602026321970876560171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 476802701762627835413561 357602026321970876560171)
              ·
                refine ⟨536403039482956314840257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357602026321970876560171 536403039482956314840257)
                ·
                  refine ⟨402302279612217236130193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 536403039482956314840257 402302279612217236130193)
                  ·
                    refine ⟨301726709709162927097645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 402302279612217236130193 301726709709162927097645)
                    ·
                      refine ⟨113147516140936097661617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 301726709709162927097645 113147516140936097661617)
                      ·
                        rfl

theorem cell23_220354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_220354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220354 prefixEnd_220354 := by exact prefixLift 220354
  have htrace : WordTrace (prefixWord ++ tailWord_220354) baseStart_220354 baseEnd_220354 := by
    simpa [prefixWord, tailWord_220354, baseEnd_220354] using wordTrace_append hprefix tailTrace_220354
  have hstable : (prefixWord ++ tailWord_220354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220354).length < 2 ^ (prefixWord ++ tailWord_220354).sum := by decide
  have hdescent : baseEnd_220354 < baseStart_220354 := by decide
  rcases family_descends (prefixWord ++ tailWord_220354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220370 : List Nat := [3, 2, 2, 2, 1, 1, 5, 1, 1, 5]
def baseStart_220370 : Nat := 118140960795 + 220370 * 2 ^ 59
def prefixEnd_220370 : Nat := 4983230072969 + 3 ^ 40 * 220370 * 2
def baseEnd_220370 : Nat := 37718577277136011687181

theorem tailTrace_220370 : CollatzResearch.WordTrace tailWord_220370 prefixEnd_220370 37718577277136011687181 := by
  unfold tailWord_220370
  simp only [CollatzResearch.WordTrace]
  refine ⟨2009388552911150261184641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5358369474429734029825709 2009388552911150261184641)
  ·
    refine ⟨1507041414683362695888481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2009388552911150261184641 1507041414683362695888481)
    ·
      refine ⟨1130281061012522021916361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1507041414683362695888481 1130281061012522021916361)
      ·
        refine ⟨847710795759391516437271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1130281061012522021916361 847710795759391516437271)
        ·
          refine ⟨1271566193639087274655907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 847710795759391516437271 1271566193639087274655907)
          ·
            refine ⟨1907349290458630911983861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1271566193639087274655907 1907349290458630911983861)
            ·
              refine ⟨178813995980496647998487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1907349290458630911983861 178813995980496647998487)
              ·
                refine ⟨268220993970744971997731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178813995980496647998487 268220993970744971997731)
                ·
                  refine ⟨402331490956117457996597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 268220993970744971997731 402331490956117457996597)
                  ·
                    refine ⟨37718577277136011687181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 402331490956117457996597 37718577277136011687181)
                    ·
                      rfl

theorem cell23_220370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_220370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220370 prefixEnd_220370 := by exact prefixLift 220370
  have htrace : WordTrace (prefixWord ++ tailWord_220370) baseStart_220370 baseEnd_220370 := by
    simpa [prefixWord, tailWord_220370, baseEnd_220370] using wordTrace_append hprefix tailTrace_220370
  have hstable : (prefixWord ++ tailWord_220370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220370).length < 2 ^ (prefixWord ++ tailWord_220370).sum := by decide
  have hdescent : baseEnd_220370 < baseStart_220370 := by decide
  rcases family_descends (prefixWord ++ tailWord_220370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220383 : List Nat := [1, 1, 2, 3, 2, 1, 3, 4, 2, 4]
def baseStart_220383 : Nat := 118140960795 + 220383 * 2 ^ 59
def prefixEnd_220383 : Nat := 4983230072969 + 3 ^ 40 * 220383 * 2
def baseEnd_220383 : Nat := 37720802359972161399661

theorem tailTrace_220383 : CollatzResearch.WordTrace tailWord_220383 prefixEnd_220383 37720802359972161399661 := by
  unfold tailWord_220383
  simp only [CollatzResearch.WordTrace]
  refine ⟨8038028360597504264961803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5358685573731669509974535 8038028360597504264961803)
  ·
    refine ⟨12057042540896256397442705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8038028360597504264961803 12057042540896256397442705)
    ·
      refine ⟨9042781905672192298082029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12057042540896256397442705 9042781905672192298082029)
      ·
        refine ⟨3391043214627072111780761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9042781905672192298082029 3391043214627072111780761)
        ·
          refine ⟨2543282410970304083835571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3391043214627072111780761 2543282410970304083835571)
          ·
            refine ⟨3814923616455456125753357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2543282410970304083835571 3814923616455456125753357)
            ·
              refine ⟨1430596356170796047157509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3814923616455456125753357 1430596356170796047157509)
              ·
                refine ⟨268236816782024258842033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1430596356170796047157509 268236816782024258842033)
                ·
                  refine ⟨201177612586518194131525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268236816782024258842033 201177612586518194131525)
                  ·
                    refine ⟨37720802359972161399661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 201177612586518194131525 37720802359972161399661)
                    ·
                      rfl

theorem cell23_220383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2, 4].length) (baseStart_220383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220383 prefixEnd_220383 := by exact prefixLift 220383
  have htrace : WordTrace (prefixWord ++ tailWord_220383) baseStart_220383 baseEnd_220383 := by
    simpa [prefixWord, tailWord_220383, baseEnd_220383] using wordTrace_append hprefix tailTrace_220383
  have hstable : (prefixWord ++ tailWord_220383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220383).length < 2 ^ (prefixWord ++ tailWord_220383).sum := by decide
  have hdescent : baseEnd_220383 < baseStart_220383 := by decide
  rcases family_descends (prefixWord ++ tailWord_220383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220384 : List Nat := [2, 1, 1, 3, 1, 6, 2, 2, 1, 1, 3]
def baseStart_220384 : Nat := 118140960795 + 220384 * 2 ^ 59
def prefixEnd_220384 : Nat := 4983230072969 + 3 ^ 40 * 220384 * 2
def baseEnd_220384 : Nat := 113162920560570980286479

theorem tailTrace_220384 : CollatzResearch.WordTrace tailWord_220384 prefixEnd_220384 113162920560570980286479 := by
  unfold tailWord_220384
  simp only [CollatzResearch.WordTrace]
  refine ⟨4019032416796940717874103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5358709889062587623832137 4019032416796940717874103)
  ·
    refine ⟨6028548625195411076811155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4019032416796940717874103 6028548625195411076811155)
    ·
      refine ⟨9042822937793116615216733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6028548625195411076811155 9042822937793116615216733)
      ·
        refine ⟨3391058601672418730706275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9042822937793116615216733 3391058601672418730706275)
        ·
          refine ⟨5086587902508628096059413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3391058601672418730706275 5086587902508628096059413)
          ·
            refine ⟨238433807930091942002785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5086587902508628096059413 238433807930091942002785)
            ·
              refine ⟨178825355947568956502089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238433807930091942002785 178825355947568956502089)
              ·
                refine ⟨134119016960676717376567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178825355947568956502089 134119016960676717376567)
                ·
                  refine ⟨201178525441015076064851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134119016960676717376567 201178525441015076064851)
                  ·
                    refine ⟨301767788161522614097277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 201178525441015076064851 301767788161522614097277)
                    ·
                      refine ⟨113162920560570980286479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 301767788161522614097277 113162920560570980286479)
                      ·
                        rfl

theorem cell23_220384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2, 1, 1, 3].length) (baseStart_220384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220384 prefixEnd_220384 := by exact prefixLift 220384
  have htrace : WordTrace (prefixWord ++ tailWord_220384) baseStart_220384 baseEnd_220384 := by
    simpa [prefixWord, tailWord_220384, baseEnd_220384] using wordTrace_append hprefix tailTrace_220384
  have hstable : (prefixWord ++ tailWord_220384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220384).length < 2 ^ (prefixWord ++ tailWord_220384).sum := by decide
  have hdescent : baseEnd_220384 < baseStart_220384 := by decide
  rcases family_descends (prefixWord ++ tailWord_220384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220396 : List Nat := [2, 2, 1, 1, 2, 4, 3, 8]
def baseStart_220396 : Nat := 118140960795 + 220396 * 2 ^ 59
def prefixEnd_220396 : Nat := 4983230072969 + 3 ^ 40 * 220396 * 2
def baseEnd_220396 : Nat := 4191447493645367901349

theorem tailTrace_220396 : CollatzResearch.WordTrace tailWord_220396 prefixEnd_220396 4191447493645367901349 := by
  unfold tailWord_220396
  simp only [CollatzResearch.WordTrace]
  refine ⟨4019251254775203742592521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5359001673033604990123361 4019251254775203742592521)
  ·
    refine ⟨3014438441081402806944391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4019251254775203742592521 3014438441081402806944391)
    ·
      refine ⟨4521657661622104210416587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3014438441081402806944391 4521657661622104210416587)
      ·
        refine ⟨6782486492433156315624881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4521657661622104210416587 6782486492433156315624881)
        ·
          refine ⟨5086864869324867236718661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6782486492433156315624881 5086864869324867236718661)
          ·
            refine ⟨953787162998412606884749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5086864869324867236718661 953787162998412606884749)
            ·
              refine ⟨357670186124404727581781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 953787162998412606884749 357670186124404727581781)
              ·
                refine ⟨4191447493645367901349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 357670186124404727581781 4191447493645367901349)
                ·
                  rfl

theorem cell23_220396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 8].length) (baseStart_220396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220396 prefixEnd_220396 := by exact prefixLift 220396
  have htrace : WordTrace (prefixWord ++ tailWord_220396) baseStart_220396 baseEnd_220396 := by
    simpa [prefixWord, tailWord_220396, baseEnd_220396] using wordTrace_append hprefix tailTrace_220396
  have hstable : (prefixWord ++ tailWord_220396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220396).length < 2 ^ (prefixWord ++ tailWord_220396).sum := by decide
  have hdescent : baseEnd_220396 < baseStart_220396 := by decide
  rcases family_descends (prefixWord ++ tailWord_220396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220403 : List Nat := [1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 4]
def baseStart_220403 : Nat := 118140960795 + 220403 * 2 ^ 59
def prefixEnd_220403 : Nat := 4983230072969 + 3 ^ 40 * 220403 * 2
def baseEnd_220403 : Nat := 113172676693006405948891

theorem tailTrace_220403 : CollatzResearch.WordTrace tailWord_220403 prefixEnd_220403 113172676693006405948891 := by
  unfold tailWord_220403
  simp only [CollatzResearch.WordTrace]
  refine ⟨8038757820525047680689863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5359171880350031787126575 8038757820525047680689863)
  ·
    refine ⟨12058136730787571521034795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8038757820525047680689863 12058136730787571521034795)
    ·
      refine ⟨18087205096181357281552193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12058136730787571521034795 18087205096181357281552193)
      ·
        refine ⟨13565403822136017961164145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18087205096181357281552193 13565403822136017961164145)
        ·
          refine ⟨10174052866602013470873109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13565403822136017961164145 10174052866602013470873109)
          ·
            refine ⟨476908728121969381447177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10174052866602013470873109 476908728121969381447177)
            ·
              refine ⟨357681546091477036085383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 476908728121969381447177 357681546091477036085383)
              ·
                refine ⟨536522319137215554128075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357681546091477036085383 536522319137215554128075)
                ·
                  refine ⟨804783478705823331192113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 536522319137215554128075 804783478705823331192113)
                  ·
                    refine ⟨603587609029367498394085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 804783478705823331192113 603587609029367498394085)
                    ·
                      refine ⟨113172676693006405948891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 603587609029367498394085 113172676693006405948891)
                      ·
                        rfl

theorem cell23_220403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 4].length) (baseStart_220403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220403 prefixEnd_220403 := by exact prefixLift 220403
  have htrace : WordTrace (prefixWord ++ tailWord_220403) baseStart_220403 baseEnd_220403 := by
    simpa [prefixWord, tailWord_220403, baseEnd_220403] using wordTrace_append hprefix tailTrace_220403
  have hstable : (prefixWord ++ tailWord_220403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220403).length < 2 ^ (prefixWord ++ tailWord_220403).sum := by decide
  have hdescent : baseEnd_220403 < baseStart_220403 := by decide
  rcases family_descends (prefixWord ++ tailWord_220403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220424 : List Nat := [2, 1, 3, 2, 5, 1, 2, 1, 1, 1, 4]
def baseStart_220424 : Nat := 118140960795 + 220424 * 2 ^ 59
def prefixEnd_220424 : Nat := 4983230072969 + 3 ^ 40 * 220424 * 2
def baseEnd_220424 : Nat := 113183459786750823786295

theorem tailTrace_220424 : CollatzResearch.WordTrace tailWord_220424 prefixEnd_220424 113183459786750823786295 := by
  unfold tailWord_220424
  simp only [CollatzResearch.WordTrace]
  refine ⟨4019761876724484133602163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5359682502299312178136217 4019761876724484133602163)
  ·
    refine ⟨6029642815086726200403245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4019761876724484133602163 6029642815086726200403245)
    ·
      refine ⟨2261116055657522325151217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6029642815086726200403245 2261116055657522325151217)
      ·
        refine ⟨1695837041743141743863413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2261116055657522325151217 1695837041743141743863413)
        ·
          refine ⟨158984722663419538487195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1695837041743141743863413 158984722663419538487195)
          ·
            refine ⟨238477083995129307730793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158984722663419538487195 238477083995129307730793)
            ·
              refine ⟨178857812996346980798095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238477083995129307730793 178857812996346980798095)
              ·
                refine ⟨268286719494520471197143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178857812996346980798095 268286719494520471197143)
                ·
                  refine ⟨402430079241780706795715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 268286719494520471197143 402430079241780706795715)
                  ·
                    refine ⟨603645118862671060193573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 402430079241780706795715 603645118862671060193573)
                    ·
                      refine ⟨113183459786750823786295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 603645118862671060193573 113183459786750823786295)
                      ·
                        rfl

theorem cell23_220424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_220424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220424 prefixEnd_220424 := by exact prefixLift 220424
  have htrace : WordTrace (prefixWord ++ tailWord_220424) baseStart_220424 baseEnd_220424 := by
    simpa [prefixWord, tailWord_220424, baseEnd_220424] using wordTrace_append hprefix tailTrace_220424
  have hstable : (prefixWord ++ tailWord_220424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220424).length < 2 ^ (prefixWord ++ tailWord_220424).sum := by decide
  have hdescent : baseEnd_220424 < baseStart_220424 := by decide
  rcases family_descends (prefixWord ++ tailWord_220424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220427 : List Nat := [1, 1, 1, 1, 5, 5, 2, 1, 1, 2, 3]
def baseStart_220427 : Nat := 118140960795 + 220427 * 2 ^ 59
def prefixEnd_220427 : Nat := 4983230072969 + 3 ^ 40 * 220427 * 2
def baseEnd_220427 : Nat := 113185000228714312048781

theorem tailTrace_220427 : CollatzResearch.WordTrace tailWord_220427 prefixEnd_220427 113185000228714312048781 := by
  unfold tailWord_220427
  simp only [CollatzResearch.WordTrace]
  refine ⟨8039633172438099779563535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5359755448292066519709023 8039633172438099779563535)
  ·
    refine ⟨12059449758657149669345303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8039633172438099779563535 12059449758657149669345303)
    ·
      refine ⟨18089174637985724504017955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12059449758657149669345303 18089174637985724504017955)
      ·
        refine ⟨27133761956978586756026933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18089174637985724504017955 27133761956978586756026933)
        ·
          refine ⟨2543790183466742508377525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27133761956978586756026933 2543790183466742508377525)
          ·
            refine ⟨238480329700007110160393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2543790183466742508377525 238480329700007110160393)
            ·
              refine ⟨178860247275005332620295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238480329700007110160393 178860247275005332620295)
              ·
                refine ⟨268290370912507998930443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178860247275005332620295 268290370912507998930443)
                ·
                  refine ⟨402435556368761998395665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 268290370912507998930443 402435556368761998395665)
                  ·
                    refine ⟨301826667276571498796749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 402435556368761998395665 301826667276571498796749)
                    ·
                      refine ⟨113185000228714312048781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 301826667276571498796749 113185000228714312048781)
                      ·
                        rfl

theorem cell23_220427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 1, 2, 3].length) (baseStart_220427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220427 prefixEnd_220427 := by exact prefixLift 220427
  have htrace : WordTrace (prefixWord ++ tailWord_220427) baseStart_220427 baseEnd_220427 := by
    simpa [prefixWord, tailWord_220427, baseEnd_220427] using wordTrace_append hprefix tailTrace_220427
  have hstable : (prefixWord ++ tailWord_220427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220427).length < 2 ^ (prefixWord ++ tailWord_220427).sum := by decide
  have hdescent : baseEnd_220427 < baseStart_220427 := by decide
  rcases family_descends (prefixWord ++ tailWord_220427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220440 : List Nat := [2, 1, 2, 3, 1, 4, 1, 1, 4, 1, 3]
def baseStart_220440 : Nat := 118140960795 + 220440 * 2 ^ 59
def prefixEnd_220440 : Nat := 4983230072969 + 3 ^ 40 * 220440 * 2
def baseEnd_220440 : Nat := 113191675477222761186221

theorem tailTrace_220440 : CollatzResearch.WordTrace tailWord_220440 prefixEnd_220440 113191675477222761186221 := by
  unfold tailWord_220440
  simp only [CollatzResearch.WordTrace]
  refine ⟨4020053660695501499893387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5360071547594001999857849 4020053660695501499893387)
  ·
    refine ⟨6030080491043252249840081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4020053660695501499893387 6030080491043252249840081)
    ·
      refine ⟨4522560368282439187380061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6030080491043252249840081 4522560368282439187380061)
      ·
        refine ⟨1695960138105914695267523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4522560368282439187380061 1695960138105914695267523)
        ·
          refine ⟨2543940207158872042901285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1695960138105914695267523 2543940207158872042901285)
          ·
            refine ⟨476988788842288508043991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2543940207158872042901285 476988788842288508043991)
            ·
              refine ⟨715483183263432762065987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476988788842288508043991 715483183263432762065987)
              ·
                refine ⟨1073224774895149143098981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 715483183263432762065987 1073224774895149143098981)
                ·
                  refine ⟨201229645292840464331059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1073224774895149143098981 201229645292840464331059)
                  ·
                    refine ⟨301844467939260696496589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 201229645292840464331059 301844467939260696496589)
                    ·
                      refine ⟨113191675477222761186221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 301844467939260696496589 113191675477222761186221)
                      ·
                        rfl

theorem cell23_220440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_220440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220440 prefixEnd_220440 := by exact prefixLift 220440
  have htrace : WordTrace (prefixWord ++ tailWord_220440) baseStart_220440 baseEnd_220440 := by
    simpa [prefixWord, tailWord_220440, baseEnd_220440] using wordTrace_append hprefix tailTrace_220440
  have hstable : (prefixWord ++ tailWord_220440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220440).length < 2 ^ (prefixWord ++ tailWord_220440).sum := by decide
  have hdescent : baseEnd_220440 < baseStart_220440 := by decide
  rcases family_descends (prefixWord ++ tailWord_220440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220467 : List Nat := [1, 1, 1, 2, 5, 3, 2, 2, 1, 3, 2]
def baseStart_220467 : Nat := 118140960795 + 220467 * 2 ^ 59
def prefixEnd_220467 : Nat := 4983230072969 + 3 ^ 40 * 220467 * 2
def baseEnd_220467 : Nat := 113205539454894155548597

theorem tailTrace_220467 : CollatzResearch.WordTrace tailWord_220467 prefixEnd_220467 113205539454894155548597 := by
  unfold tailWord_220467
  simp only [CollatzResearch.WordTrace]
  refine ⟨8041092092293186611019655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5360728061528791074013103 8041092092293186611019655)
  ·
    refine ⟨12061638138439779916529483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8041092092293186611019655 12061638138439779916529483)
    ·
      refine ⟨18092457207659669874794225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12061638138439779916529483 18092457207659669874794225)
      ·
        refine ⟨13569342905744752406095669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18092457207659669874794225 13569342905744752406095669)
        ·
          refine ⟨1272125897413570538071469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13569342905744752406095669 1272125897413570538071469)
          ·
            refine ⟨477047211530088951776801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1272125897413570538071469 477047211530088951776801)
            ·
              refine ⟨357785408647566713832601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477047211530088951776801 357785408647566713832601)
              ·
                refine ⟨268339056485675035374451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 357785408647566713832601 268339056485675035374451)
                ·
                  refine ⟨402508584728512553061677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 268339056485675035374451 402508584728512553061677)
                  ·
                    refine ⟨150940719273192207398129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 402508584728512553061677 150940719273192207398129)
                    ·
                      refine ⟨113205539454894155548597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 150940719273192207398129 113205539454894155548597)
                      ·
                        rfl

theorem cell23_220467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 3, 2].length) (baseStart_220467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220467 prefixEnd_220467 := by exact prefixLift 220467
  have htrace : WordTrace (prefixWord ++ tailWord_220467) baseStart_220467 baseEnd_220467 := by
    simpa [prefixWord, tailWord_220467, baseEnd_220467] using wordTrace_append hprefix tailTrace_220467
  have hstable : (prefixWord ++ tailWord_220467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220467).length < 2 ^ (prefixWord ++ tailWord_220467).sum := by decide
  have hdescent : baseEnd_220467 < baseStart_220467 := by decide
  rcases family_descends (prefixWord ++ tailWord_220467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220480 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 6, 2, 2]
def baseStart_220480 : Nat := 118140960795 + 220480 * 2 ^ 59
def prefixEnd_220480 : Nat := 4983230072969 + 3 ^ 40 * 220480 * 2
def baseEnd_220480 : Nat := 113212214703402604686037

theorem tailTrace_220480 : CollatzResearch.WordTrace tailWord_220480 prefixEnd_220480 113212214703402604686037 := by
  unfold tailWord_220480
  simp only [CollatzResearch.WordTrace]
  refine ⟨4020783120623044915621447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5361044160830726554161929 4020783120623044915621447)
  ·
    refine ⟨6031174680934567373432171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4020783120623044915621447 6031174680934567373432171)
    ·
      refine ⟨9046762021401851060148257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6031174680934567373432171 9046762021401851060148257)
      ·
        refine ⟨6785071516051388295111193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9046762021401851060148257 6785071516051388295111193)
        ·
          refine ⟨5088803637038541221333395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6785071516051388295111193 5088803637038541221333395)
          ·
            refine ⟨7633205455557811832000093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5088803637038541221333395 7633205455557811832000093)
            ·
              refine ⟨2862452045834179437000035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7633205455557811832000093 2862452045834179437000035)
              ·
                refine ⟨4293678068751269155500053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2862452045834179437000035 4293678068751269155500053)
                ·
                  refine ⟨201266159472715741664065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4293678068751269155500053 201266159472715741664065)
                  ·
                    refine ⟨150949619604536806248049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 201266159472715741664065 150949619604536806248049)
                    ·
                      refine ⟨113212214703402604686037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 150949619604536806248049 113212214703402604686037)
                      ·
                        rfl

theorem cell23_220480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 6, 2, 2].length) (baseStart_220480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220480 prefixEnd_220480 := by exact prefixLift 220480
  have htrace : WordTrace (prefixWord ++ tailWord_220480) baseStart_220480 baseEnd_220480 := by
    simpa [prefixWord, tailWord_220480, baseEnd_220480] using wordTrace_append hprefix tailTrace_220480
  have hstable : (prefixWord ++ tailWord_220480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220480).length < 2 ^ (prefixWord ++ tailWord_220480).sum := by decide
  have hdescent : baseEnd_220480 < baseStart_220480 := by decide
  rcases family_descends (prefixWord ++ tailWord_220480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220484 : List Nat := [2, 3, 4, 1, 1, 1, 2, 3, 1, 3, 2]
def baseStart_220484 : Nat := 118140960795 + 220484 * 2 ^ 59
def prefixEnd_220484 : Nat := 4983230072969 + 3 ^ 40 * 220484 * 2
def baseEnd_220484 : Nat := 113214268626020589036019

theorem tailTrace_220484 : CollatzResearch.WordTrace tailWord_220484 prefixEnd_220484 113214268626020589036019 := by
  unfold tailWord_220484
  simp only [CollatzResearch.WordTrace]
  refine ⟨4020856066615799257194253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5361141422154399009592337 4020856066615799257194253)
  ·
    refine ⟨1507821024980924721447845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4020856066615799257194253 1507821024980924721447845)
    ·
      refine ⟨282716442183923385271471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1507821024980924721447845 282716442183923385271471)
      ·
        refine ⟨424074663275885077907207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282716442183923385271471 424074663275885077907207)
        ·
          refine ⟨636111994913827616860811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424074663275885077907207 636111994913827616860811)
          ·
            refine ⟨954167992370741425291217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636111994913827616860811 954167992370741425291217)
            ·
              refine ⟨715625994278056068968413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 954167992370741425291217 715625994278056068968413)
              ·
                refine ⟨268359747854271025863155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 715625994278056068968413 268359747854271025863155)
                ·
                  refine ⟨402539621781406538794733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 268359747854271025863155 402539621781406538794733)
                  ·
                    refine ⟨150952358168027452048025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 402539621781406538794733 150952358168027452048025)
                    ·
                      refine ⟨113214268626020589036019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 150952358168027452048025 113214268626020589036019)
                      ·
                        rfl

theorem cell23_220484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_220484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220484 prefixEnd_220484 := by exact prefixLift 220484
  have htrace : WordTrace (prefixWord ++ tailWord_220484) baseStart_220484 baseEnd_220484 := by
    simpa [prefixWord, tailWord_220484, baseEnd_220484] using wordTrace_append hprefix tailTrace_220484
  have hstable : (prefixWord ++ tailWord_220484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220484).length < 2 ^ (prefixWord ++ tailWord_220484).sum := by decide
  have hdescent : baseEnd_220484 < baseStart_220484 := by decide
  rcases family_descends (prefixWord ++ tailWord_220484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220496 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 7]
def baseStart_220496 : Nat := 118140960795 + 220496 * 2 ^ 59
def prefixEnd_220496 : Nat := 4983230072969 + 3 ^ 40 * 220496 * 2
def baseEnd_220496 : Nat := 113220430393874542085963

theorem tailTrace_220496 : CollatzResearch.WordTrace tailWord_220496 prefixEnd_220496 113220430393874542085963 := by
  unfold tailWord_220496
  simp only [CollatzResearch.WordTrace]
  refine ⟨4021074904594062281912671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5361433206125416375883561 4021074904594062281912671)
  ·
    refine ⟨6031612356891093422869007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4021074904594062281912671 6031612356891093422869007)
    ·
      refine ⟨9047418535336640134303511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6031612356891093422869007 9047418535336640134303511)
      ·
        refine ⟨13571127803004960201455267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9047418535336640134303511 13571127803004960201455267)
        ·
          refine ⟨20356691704507440302182901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13571127803004960201455267 20356691704507440302182901)
          ·
            refine ⟨1908439847297572528329647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20356691704507440302182901 1908439847297572528329647)
            ·
              refine ⟨2862659770946358792494471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1908439847297572528329647 2862659770946358792494471)
              ·
                refine ⟨4293989656419538188741707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2862659770946358792494471 4293989656419538188741707)
                ·
                  refine ⟨6440984484629307283112561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4293989656419538188741707 6440984484629307283112561)
                  ·
                    refine ⟨4830738363471980462334421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6440984484629307283112561 4830738363471980462334421)
                    ·
                      refine ⟨113220430393874542085963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 4830738363471980462334421 113220430393874542085963)
                      ·
                        rfl

theorem cell23_220496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 7].length) (baseStart_220496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220496 prefixEnd_220496 := by exact prefixLift 220496
  have htrace : WordTrace (prefixWord ++ tailWord_220496) baseStart_220496 baseEnd_220496 := by
    simpa [prefixWord, tailWord_220496, baseEnd_220496] using wordTrace_append hprefix tailTrace_220496
  have hstable : (prefixWord ++ tailWord_220496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220496).length < 2 ^ (prefixWord ++ tailWord_220496).sum := by decide
  have hdescent : baseEnd_220496 < baseStart_220496 := by decide
  rcases family_descends (prefixWord ++ tailWord_220496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220497 : List Nat := [1, 2, 2, 1, 4, 1, 2, 4, 2, 2, 2]
def baseStart_220497 : Nat := 118140960795 + 220497 * 2 ^ 59
def prefixEnd_220497 : Nat := 4983230072969 + 3 ^ 40 * 220497 * 2
def baseEnd_220497 : Nat := 113220943874529038173459

theorem tailTrace_220497 : CollatzResearch.WordTrace tailWord_220497 prefixEnd_220497 113220943874529038173459 := by
  unfold tailWord_220497
  simp only [CollatzResearch.WordTrace]
  refine ⟨8042186282184501734611745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5361457521456334489741163 8042186282184501734611745)
  ·
    refine ⟨6031639711638376300958809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8042186282184501734611745 6031639711638376300958809)
    ·
      refine ⟨4523729783728782225719107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6031639711638376300958809 4523729783728782225719107)
      ·
        refine ⟨6785594675593173338578661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4523729783728782225719107 6785594675593173338578661)
        ·
          refine ⟨1272299001673720000983499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6785594675593173338578661 1272299001673720000983499)
          ·
            refine ⟨1908448502510580001475249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1272299001673720000983499 1908448502510580001475249)
            ·
              refine ⟨1431336376882935001106437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1908448502510580001475249 1431336376882935001106437)
              ·
                refine ⟨268375570665550312707457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1431336376882935001106437 268375570665550312707457)
                ·
                  refine ⟨201281677999162734530593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268375570665550312707457 201281677999162734530593)
                  ·
                    refine ⟨150961258499372050897945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 201281677999162734530593 150961258499372050897945)
                    ·
                      refine ⟨113220943874529038173459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 150961258499372050897945 113220943874529038173459)
                      ·
                        rfl

theorem cell23_220497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2, 2, 2].length) (baseStart_220497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220497 prefixEnd_220497 := by exact prefixLift 220497
  have htrace : WordTrace (prefixWord ++ tailWord_220497) baseStart_220497 baseEnd_220497 := by
    simpa [prefixWord, tailWord_220497, baseEnd_220497] using wordTrace_append hprefix tailTrace_220497
  have hstable : (prefixWord ++ tailWord_220497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220497).length < 2 ^ (prefixWord ++ tailWord_220497).sum := by decide
  have hdescent : baseEnd_220497 < baseStart_220497 := by decide
  rcases family_descends (prefixWord ++ tailWord_220497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220503 : List Nat := [1, 1, 3, 2, 3, 2, 3, 1, 7]
def baseStart_220503 : Nat := 118140960795 + 220503 * 2 ^ 59
def prefixEnd_220503 : Nat := 4983230072969 + 3 ^ 40 * 220503 * 2
def baseEnd_220503 : Nat := 12580447195384001633159

theorem tailTrace_220503 : CollatzResearch.WordTrace tailWord_220503 prefixEnd_220503 12580447195384001633159 := by
  unfold tailWord_220503
  simp only [CollatzResearch.WordTrace]
  refine ⟨8042405120162764759330163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5361603413441843172886775 8042405120162764759330163)
  ·
    refine ⟨12063607680244147138995245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8042405120162764759330163 12063607680244147138995245)
    ·
      refine ⟨4523852880091555177123217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12063607680244147138995245 4523852880091555177123217)
      ·
        refine ⟨3392889660068666382842413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4523852880091555177123217 3392889660068666382842413)
        ·
          refine ⟨1272333622525749893565905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3392889660068666382842413 1272333622525749893565905)
          ·
            refine ⟨954250216894312420174429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1272333622525749893565905 954250216894312420174429)
            ·
              refine ⟨357843831335367157565411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 954250216894312420174429 357843831335367157565411)
              ·
                refine ⟨536765747003050736348117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357843831335367157565411 536765747003050736348117)
                ·
                  refine ⟨12580447195384001633159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 536765747003050736348117 12580447195384001633159)
                  ·
                    rfl

theorem cell23_220503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 7].length) (baseStart_220503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220503 prefixEnd_220503 := by exact prefixLift 220503
  have htrace : WordTrace (prefixWord ++ tailWord_220503) baseStart_220503 baseEnd_220503 := by
    simpa [prefixWord, tailWord_220503, baseEnd_220503] using wordTrace_append hprefix tailTrace_220503
  have hstable : (prefixWord ++ tailWord_220503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220503).length < 2 ^ (prefixWord ++ tailWord_220503).sum := by decide
  have hdescent : baseEnd_220503 < baseStart_220503 := by decide
  rcases family_descends (prefixWord ++ tailWord_220503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220513 : List Nat := [1, 2, 3, 1, 1, 1, 1, 5, 2, 3, 3]
def baseStart_220513 : Nat := 118140960795 + 220513 * 2 ^ 59
def prefixEnd_220513 : Nat := 4983230072969 + 3 ^ 40 * 220513 * 2
def baseEnd_220513 : Nat := 113229159565000975573385

theorem tailTrace_220513 : CollatzResearch.WordTrace tailWord_220513 prefixEnd_220513 113229159565000975573385 := by
  unfold tailWord_220513
  simp only [CollatzResearch.WordTrace]
  refine ⟨8042769850126536467194193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5361846566751024311462795 8042769850126536467194193)
  ·
    refine ⟨6032077387594902350395645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8042769850126536467194193 6032077387594902350395645)
    ·
      refine ⟨2262029020348088381398367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6032077387594902350395645 2262029020348088381398367)
      ·
        refine ⟨3393043530522132572097551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2262029020348088381398367 3393043530522132572097551)
        ·
          refine ⟨5089565295783198858146327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3393043530522132572097551 5089565295783198858146327)
          ·
            refine ⟨7634347943674798287219491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5089565295783198858146327 7634347943674798287219491)
            ·
              refine ⟨11451521915512197430829237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7634347943674798287219491 11451521915512197430829237)
              ·
                refine ⟨1073580179579268509140241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11451521915512197430829237 1073580179579268509140241)
                ·
                  refine ⟨805185134684451381855181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1073580179579268509140241 805185134684451381855181)
                  ·
                    refine ⟨301944425506669268195693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 805185134684451381855181 301944425506669268195693)
                    ·
                      refine ⟨113229159565000975573385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 301944425506669268195693 113229159565000975573385)
                      ·
                        rfl

theorem cell23_220513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_220513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220513 prefixEnd_220513 := by exact prefixLift 220513
  have htrace : WordTrace (prefixWord ++ tailWord_220513) baseStart_220513 baseEnd_220513 := by
    simpa [prefixWord, tailWord_220513, baseEnd_220513] using wordTrace_append hprefix tailTrace_220513
  have hstable : (prefixWord ++ tailWord_220513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220513).length < 2 ^ (prefixWord ++ tailWord_220513).sum := by decide
  have hdescent : baseEnd_220513 < baseStart_220513 := by decide
  rcases family_descends (prefixWord ++ tailWord_220513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220514 : List Nat := [3, 3, 2, 1, 1, 1, 3, 3, 2, 2, 2]
def baseStart_220514 : Nat := 118140960795 + 220514 * 2 ^ 59
def prefixEnd_220514 : Nat := 4983230072969 + 3 ^ 40 * 220514 * 2
def baseEnd_220514 : Nat := 113229673045655471660881

theorem tailTrace_220514 : CollatzResearch.WordTrace tailWord_220514 prefixEnd_220514 113229673045655471660881 := by
  unfold tailWord_220514
  simp only [CollatzResearch.WordTrace]
  refine ⟨2010701580780728409495149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5361870882081942425320397 2010701580780728409495149)
  ·
    refine ⟨754013092792773153560681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2010701580780728409495149 754013092792773153560681)
    ·
      refine ⟨565509819594579865170511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 754013092792773153560681 565509819594579865170511)
      ·
        refine ⟨848264729391869797755767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565509819594579865170511 848264729391869797755767)
        ·
          refine ⟨1272397094087804696633651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 848264729391869797755767 1272397094087804696633651)
          ·
            refine ⟨1908595641131707044950477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1272397094087804696633651 1908595641131707044950477)
            ·
              refine ⟨715723365424390141856429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1908595641131707044950477 715723365424390141856429)
              ·
                refine ⟨268396262034146303196161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 715723365424390141856429 268396262034146303196161)
                ·
                  refine ⟨201297196525609727397121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268396262034146303196161 201297196525609727397121)
                  ·
                    refine ⟨150972897394207295547841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 201297196525609727397121 150972897394207295547841)
                    ·
                      refine ⟨113229673045655471660881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 150972897394207295547841 113229673045655471660881)
                      ·
                        rfl

theorem cell23_220514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_220514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220514 prefixEnd_220514 := by exact prefixLift 220514
  have htrace : WordTrace (prefixWord ++ tailWord_220514) baseStart_220514 baseEnd_220514 := by
    simpa [prefixWord, tailWord_220514, baseEnd_220514] using wordTrace_append hprefix tailTrace_220514
  have hstable : (prefixWord ++ tailWord_220514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220514).length < 2 ^ (prefixWord ++ tailWord_220514).sum := by decide
  have hdescent : baseEnd_220514 < baseStart_220514 := by decide
  rcases family_descends (prefixWord ++ tailWord_220514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220563 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 9, 4]
def baseStart_220563 : Nat := 118140960795 + 220563 * 2 ^ 59
def prefixEnd_220563 : Nat := 4983230072969 + 3 ^ 40 * 220563 * 2
def baseEnd_220563 : Nat := 37751611199241926649385

theorem tailTrace_220563 : CollatzResearch.WordTrace tailWord_220563 prefixEnd_220563 37751611199241926649385 := by
  unfold tailWord_220563
  simp only [CollatzResearch.WordTrace]
  refine ⟨8044593499945395006514343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5363062333296930004342895 8044593499945395006514343)
  ·
    refine ⟨12066890249918092509771515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8044593499945395006514343 12066890249918092509771515)
    ·
      refine ⟨18100335374877138764657273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12066890249918092509771515 18100335374877138764657273)
      ·
        refine ⟨13575251531157854073492955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18100335374877138764657273 13575251531157854073492955)
        ·
          refine ⟨20362877296736781110239433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13575251531157854073492955 20362877296736781110239433)
          ·
            refine ⟨15272157972552585832679575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20362877296736781110239433 15272157972552585832679575)
            ·
              refine ⟨22908236958828878749019363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15272157972552585832679575 22908236958828878749019363)
              ·
                refine ⟨34362355438243318123529045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22908236958828878749019363 34362355438243318123529045)
                ·
                  refine ⟨201341926395956942130053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34362355438243318123529045 201341926395956942130053)
                  ·
                    refine ⟨37751611199241926649385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 201341926395956942130053 37751611199241926649385)
                    ·
                      rfl

theorem cell23_220563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9, 4].length) (baseStart_220563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220563 prefixEnd_220563 := by exact prefixLift 220563
  have htrace : WordTrace (prefixWord ++ tailWord_220563) baseStart_220563 baseEnd_220563 := by
    simpa [prefixWord, tailWord_220563, baseEnd_220563] using wordTrace_append hprefix tailTrace_220563
  have hstable : (prefixWord ++ tailWord_220563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220563).length < 2 ^ (prefixWord ++ tailWord_220563).sum := by decide
  have hdescent : baseEnd_220563 < baseStart_220563 := by decide
  rcases family_descends (prefixWord ++ tailWord_220563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220584 : List Nat := [2, 1, 6, 1, 2, 2, 1, 1, 2, 5]
def baseStart_220584 : Nat := 118140960795 + 220584 * 2 ^ 59
def prefixEnd_220584 : Nat := 4983230072969 + 3 ^ 40 * 220584 * 2
def baseEnd_220584 : Nat := 37755205563823399261853

theorem tailTrace_220584 : CollatzResearch.WordTrace tailWord_220584 prefixEnd_220584 37755205563823399261853 := by
  unfold tailWord_220584
  simp only [CollatzResearch.WordTrace]
  refine ⟨4022679716434657796514403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5363572955246210395352537 4022679716434657796514403)
  ·
    refine ⟨6034019574651986694771605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4022679716434657796514403 6034019574651986694771605)
    ·
      refine ⟨282844667561811876317419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6034019574651986694771605 282844667561811876317419)
      ·
        refine ⟨424267001342717814476129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282844667561811876317419 424267001342717814476129)
        ·
          refine ⟨318200251007038360857097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424267001342717814476129 318200251007038360857097)
          ·
            refine ⟨238650188255278770642823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318200251007038360857097 238650188255278770642823)
            ·
              refine ⟨357975282382918155964235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238650188255278770642823 357975282382918155964235)
              ·
                refine ⟨536962923574377233946353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357975282382918155964235 536962923574377233946353)
                ·
                  refine ⟨402722192680782925459765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 536962923574377233946353 402722192680782925459765)
                  ·
                    refine ⟨37755205563823399261853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 402722192680782925459765 37755205563823399261853)
                    ·
                      rfl

theorem cell23_220584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_220584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220584 prefixEnd_220584 := by exact prefixLift 220584
  have htrace : WordTrace (prefixWord ++ tailWord_220584) baseStart_220584 baseEnd_220584 := by
    simpa [prefixWord, tailWord_220584, baseEnd_220584] using wordTrace_append hprefix tailTrace_220584
  have hstable : (prefixWord ++ tailWord_220584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220584).length < 2 ^ (prefixWord ++ tailWord_220584).sum := by decide
  have hdescent : baseEnd_220584 < baseStart_220584 := by decide
  rcases family_descends (prefixWord ++ tailWord_220584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220593 : List Nat := [1, 2, 2, 4, 1, 1, 2, 2, 8]
def baseStart_220593 : Nat := 118140960795 + 220593 * 2 ^ 59
def prefixEnd_220593 : Nat := 4983230072969 + 3 ^ 40 * 220593 * 2
def baseEnd_220593 : Nat := 12585582001928962508113

theorem tailTrace_220593 : CollatzResearch.WordTrace tailWord_220593 prefixEnd_220593 12585582001928962508113 := by
  unfold tailWord_220593
  simp only [CollatzResearch.WordTrace]
  refine ⟨8045687689836710130106433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5363791793224473420070955 8045687689836710130106433)
  ·
    refine ⟨6034265767377532597579825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8045687689836710130106433 6034265767377532597579825)
    ·
      refine ⟨4525699325533149448184869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6034265767377532597579825 4525699325533149448184869)
      ·
        refine ⟨848568623537465521534663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4525699325533149448184869 848568623537465521534663)
        ·
          refine ⟨1272852935306198282301995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 848568623537465521534663 1272852935306198282301995)
          ·
            refine ⟨1909279402959297423452993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1272852935306198282301995 1909279402959297423452993)
            ·
              refine ⟨1431959552219473067589745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1909279402959297423452993 1431959552219473067589745)
              ·
                refine ⟨1073969664164604800692309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1431959552219473067589745 1073969664164604800692309)
                ·
                  refine ⟨12585582001928962508113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1073969664164604800692309 12585582001928962508113)
                  ·
                    rfl

theorem cell23_220593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 8].length) (baseStart_220593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220593 prefixEnd_220593 := by exact prefixLift 220593
  have htrace : WordTrace (prefixWord ++ tailWord_220593) baseStart_220593 baseEnd_220593 := by
    simpa [prefixWord, tailWord_220593, baseEnd_220593] using wordTrace_append hprefix tailTrace_220593
  have hstable : (prefixWord ++ tailWord_220593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220593).length < 2 ^ (prefixWord ++ tailWord_220593).sum := by decide
  have hdescent : baseEnd_220593 < baseStart_220593 := by decide
  rcases family_descends (prefixWord ++ tailWord_220593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220623 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 5, 5]
def baseStart_220623 : Nat := 118140960795 + 220623 * 2 ^ 59
def prefixEnd_220623 : Nat := 4983230072969 + 3 ^ 40 * 220623 * 2
def baseEnd_220623 : Nat := 37761880812331848399293

theorem tailTrace_220623 : CollatzResearch.WordTrace tailWord_220623 prefixEnd_220623 37761880812331848399293 := by
  unfold tailWord_220623
  simp only [CollatzResearch.WordTrace]
  refine ⟨8046781879728025253698523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5364521253152016835799015 8046781879728025253698523)
  ·
    refine ⟨12070172819592037880547785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8046781879728025253698523 12070172819592037880547785)
    ·
      refine ⟨9052629614694028410410839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12070172819592037880547785 9052629614694028410410839)
      ·
        refine ⟨13578944422041042615616259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9052629614694028410410839 13578944422041042615616259)
        ·
          refine ⟨20368416633061563923424389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13578944422041042615616259 20368416633061563923424389)
          ·
            refine ⟨3819078118699043235642073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20368416633061563923424389 3819078118699043235642073)
            ·
              refine ⟨2864308589024282426731555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3819078118699043235642073 2864308589024282426731555)
              ·
                refine ⟨4296462883536423640097333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2864308589024282426731555 4296462883536423640097333)
                ·
                  refine ⟨402793395331539716259125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4296462883536423640097333 402793395331539716259125)
                  ·
                    refine ⟨37761880812331848399293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 402793395331539716259125 37761880812331848399293)
                    ·
                      rfl

theorem cell23_220623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 5].length) (baseStart_220623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220623 prefixEnd_220623 := by exact prefixLift 220623
  have htrace : WordTrace (prefixWord ++ tailWord_220623) baseStart_220623 baseEnd_220623 := by
    simpa [prefixWord, tailWord_220623, baseEnd_220623] using wordTrace_append hprefix tailTrace_220623
  have hstable : (prefixWord ++ tailWord_220623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220623).length < 2 ^ (prefixWord ++ tailWord_220623).sum := by decide
  have hdescent : baseEnd_220623 < baseStart_220623 := by decide
  rcases family_descends (prefixWord ++ tailWord_220623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220647 : List Nat := [1, 1, 5, 2, 1, 2, 2, 1, 1, 5, 2]
def baseStart_220647 : Nat := 118140960795 + 220647 * 2 ^ 59
def prefixEnd_220647 : Nat := 4983230072969 + 3 ^ 40 * 220647 * 2
def baseEnd_220647 : Nat := 113297965972703451297769

theorem tailTrace_220647 : CollatzResearch.WordTrace tailWord_220647 prefixEnd_220647 113297965972703451297769 := by
  unfold tailWord_220647
  simp only [CollatzResearch.WordTrace]
  refine ⟨8047657231641077352572195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5365104821094051568381463 8047657231641077352572195)
  ·
    refine ⟨12071485847461616028858293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8047657231641077352572195 12071485847461616028858293)
    ·
      refine ⟨1131701798199526502705465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12071485847461616028858293 1131701798199526502705465)
      ·
        refine ⟨848776348649644877029099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1131701798199526502705465 848776348649644877029099)
        ·
          refine ⟨1273164522974467315543649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 848776348649644877029099 1273164522974467315543649)
          ·
            refine ⟨954873392230850486657737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1273164522974467315543649 954873392230850486657737)
            ·
              refine ⟨716155044173137864993303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 954873392230850486657737 716155044173137864993303)
              ·
                refine ⟨1074232566259706797489955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716155044173137864993303 1074232566259706797489955)
                ·
                  refine ⟨1611348849389560196234933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1074232566259706797489955 1611348849389560196234933)
                  ·
                    refine ⟨151063954630271268397025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1611348849389560196234933 151063954630271268397025)
                    ·
                      refine ⟨113297965972703451297769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 151063954630271268397025 113297965972703451297769)
                      ·
                        rfl

theorem cell23_220647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_220647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220647 prefixEnd_220647 := by exact prefixLift 220647
  have htrace : WordTrace (prefixWord ++ tailWord_220647) baseStart_220647 baseEnd_220647 := by
    simpa [prefixWord, tailWord_220647, baseEnd_220647] using wordTrace_append hprefix tailTrace_220647
  have hstable : (prefixWord ++ tailWord_220647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220647).length < 2 ^ (prefixWord ++ tailWord_220647).sum := by decide
  have hdescent : baseEnd_220647 < baseStart_220647 := by decide
  rcases family_descends (prefixWord ++ tailWord_220647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220680 : List Nat := [2, 1, 3, 2, 1, 1, 4, 2, 1, 1, 5]
def baseStart_220680 : Nat := 118140960795 + 220680 * 2 ^ 59
def prefixEnd_220680 : Nat := 4983230072969 + 3 ^ 40 * 220680 * 2
def baseEnd_220680 : Nat := 113314910834301822185117

theorem tailTrace_220680 : CollatzResearch.WordTrace tailWord_220680 prefixEnd_220680 113314910834301822185117 := by
  unfold tailWord_220680
  simp only [CollatzResearch.WordTrace]
  refine ⟨4024430420260761994261747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5365907227014349325682329 4024430420260761994261747)
  ·
    refine ⟨6036645630391142991392621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4024430420260761994261747 6036645630391142991392621)
    ·
      refine ⟨2263742111396678621772233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6036645630391142991392621 2263742111396678621772233)
      ·
        refine ⟨1697806583547508966329175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2263742111396678621772233 1697806583547508966329175)
        ·
          refine ⟨2546709875321263449493763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1697806583547508966329175 2546709875321263449493763)
          ·
            refine ⟨3820064812981895174240645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2546709875321263449493763 3820064812981895174240645)
            ·
              refine ⟨716262152434105345170121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3820064812981895174240645 716262152434105345170121)
              ·
                refine ⟨537196614325579008877591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 716262152434105345170121 537196614325579008877591)
                ·
                  refine ⟨805794921488368513316387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 537196614325579008877591 805794921488368513316387)
                  ·
                    refine ⟨1208692382232552769974581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 805794921488368513316387 1208692382232552769974581)
                    ·
                      refine ⟨113314910834301822185117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1208692382232552769974581 113314910834301822185117)
                      ·
                        rfl

theorem cell23_220680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_220680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220680 prefixEnd_220680 := by exact prefixLift 220680
  have htrace : WordTrace (prefixWord ++ tailWord_220680) baseStart_220680 baseEnd_220680 := by
    simpa [prefixWord, tailWord_220680, baseEnd_220680] using wordTrace_append hprefix tailTrace_220680
  have hstable : (prefixWord ++ tailWord_220680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220680).length < 2 ^ (prefixWord ++ tailWord_220680).sum := by decide
  have hdescent : baseEnd_220680 < baseStart_220680 := by decide
  rcases family_descends (prefixWord ++ tailWord_220680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220707 : List Nat := [1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 4]
def baseStart_220707 : Nat := 118140960795 + 220707 * 2 ^ 59
def prefixEnd_220707 : Nat := 4983230072969 + 3 ^ 40 * 220707 * 2
def baseEnd_220707 : Nat := 113328774811973216547493

theorem tailTrace_220707 : CollatzResearch.WordTrace tailWord_220707 prefixEnd_220707 113328774811973216547493 := by
  unfold tailWord_220707
  simp only [CollatzResearch.WordTrace]
  refine ⟨8049845611423707599756375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5366563740949138399837583 8049845611423707599756375)
  ·
    refine ⟨12074768417135561399634563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8049845611423707599756375 12074768417135561399634563)
    ·
      refine ⟨18112152625703342099451845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12074768417135561399634563 18112152625703342099451845)
      ·
        refine ⟨3396028617319376643647221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18112152625703342099451845 3396028617319376643647221)
        ·
          refine ⟨318377682873691560341927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3396028617319376643647221 318377682873691560341927)
          ·
            refine ⟨477566524310537340512891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318377682873691560341927 477566524310537340512891)
            ·
              refine ⟨716349786465806010769337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477566524310537340512891 716349786465806010769337)
              ·
                refine ⟨537262339849354508077003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 716349786465806010769337 537262339849354508077003)
                ·
                  refine ⟨805893509774031762115505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 537262339849354508077003 805893509774031762115505)
                  ·
                    refine ⟨604420132330523821586629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 805893509774031762115505 604420132330523821586629)
                    ·
                      refine ⟨113328774811973216547493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 604420132330523821586629 113328774811973216547493)
                      ·
                        rfl

theorem cell23_220707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_220707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220707 prefixEnd_220707 := by exact prefixLift 220707
  have htrace : WordTrace (prefixWord ++ tailWord_220707) baseStart_220707 baseEnd_220707 := by
    simpa [prefixWord, tailWord_220707, baseEnd_220707] using wordTrace_append hprefix tailTrace_220707
  have hstable : (prefixWord ++ tailWord_220707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220707).length < 2 ^ (prefixWord ++ tailWord_220707).sum := by decide
  have hdescent : baseEnd_220707 < baseStart_220707 := by decide
  rcases family_descends (prefixWord ++ tailWord_220707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220728 : List Nat := [2, 1, 2, 1, 4, 2, 4, 2, 1, 2, 2]
def baseStart_220728 : Nat := 118140960795 + 220728 * 2 ^ 59
def prefixEnd_220728 : Nat := 4983230072969 + 3 ^ 40 * 220728 * 2
def baseEnd_220728 : Nat := 113339557905717634384897

theorem tailTrace_220728 : CollatzResearch.WordTrace tailWord_220728 prefixEnd_220728 113339557905717634384897 := by
  unfold tailWord_220728
  simp only [CollatzResearch.WordTrace]
  refine ⟨4025305772173814093135419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5367074362898418790847225 4025305772173814093135419)
  ·
    refine ⟨6037958658260721139703129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4025305772173814093135419 6037958658260721139703129)
    ·
      refine ⟨4528468993695540854777347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6037958658260721139703129 4528468993695540854777347)
      ·
        refine ⟨6792703490543311282166021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4528468993695540854777347 6792703490543311282166021)
        ·
          refine ⟨1273631904476870865406129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6792703490543311282166021 1273631904476870865406129)
          ·
            refine ⟨955223928357653149054597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1273631904476870865406129 955223928357653149054597)
            ·
              refine ⟨179104486567059965447737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 955223928357653149054597 179104486567059965447737)
              ·
                refine ⟨134328364925294974085803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179104486567059965447737 134328364925294974085803)
                ·
                  refine ⟨201492547387942461128705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134328364925294974085803 201492547387942461128705)
                  ·
                    refine ⟨151119410540956845846529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 201492547387942461128705 151119410540956845846529)
                    ·
                      refine ⟨113339557905717634384897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 151119410540956845846529 113339557905717634384897)
                      ·
                        rfl

theorem cell23_220728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2, 1, 2, 2].length) (baseStart_220728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220728 prefixEnd_220728 := by exact prefixLift 220728
  have htrace : WordTrace (prefixWord ++ tailWord_220728) baseStart_220728 baseEnd_220728 := by
    simpa [prefixWord, tailWord_220728, baseEnd_220728] using wordTrace_append hprefix tailTrace_220728
  have hstable : (prefixWord ++ tailWord_220728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220728).length < 2 ^ (prefixWord ++ tailWord_220728).sum := by decide
  have hdescent : baseEnd_220728 < baseStart_220728 := by decide
  rcases family_descends (prefixWord ++ tailWord_220728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220750 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4]
def baseStart_220750 : Nat := 118140960795 + 220750 * 2 ^ 59
def prefixEnd_220750 : Nat := 4983230072969 + 3 ^ 40 * 220750 * 2
def baseEnd_220750 : Nat := 113350854480116548309795

theorem tailTrace_220750 : CollatzResearch.WordTrace tailWord_220750 prefixEnd_220750 113350854480116548309795 := by
  unfold tailWord_220750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1006426743783490742946463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5367609300178617295714469 1006426743783490742946463)
  ·
    refine ⟨1509640115675236114419695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1006426743783490742946463 1509640115675236114419695)
    ·
      refine ⟨2264460173512854171629543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1509640115675236114419695 2264460173512854171629543)
      ·
        refine ⟨3396690260269281257444315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2264460173512854171629543 3396690260269281257444315)
        ·
          refine ⟨5095035390403921886166473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3396690260269281257444315 5095035390403921886166473)
          ·
            refine ⟨3821276542802941414624855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5095035390403921886166473 3821276542802941414624855)
            ·
              refine ⟨5731914814204412121937283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3821276542802941414624855 5731914814204412121937283)
              ·
                refine ⟨8597872221306618182905925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5731914814204412121937283 8597872221306618182905925)
                ·
                  refine ⟨1612101041494990909294861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8597872221306618182905925 1612101041494990909294861)
                  ·
                    refine ⟨604537890560621590985573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1612101041494990909294861 604537890560621590985573)
                    ·
                      refine ⟨113350854480116548309795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 604537890560621590985573 113350854480116548309795)
                      ·
                        rfl

theorem cell23_220750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_220750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220750 prefixEnd_220750 := by exact prefixLift 220750
  have htrace : WordTrace (prefixWord ++ tailWord_220750) baseStart_220750 baseEnd_220750 := by
    simpa [prefixWord, tailWord_220750, baseEnd_220750] using wordTrace_append hprefix tailTrace_220750
  have hstable : (prefixWord ++ tailWord_220750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220750).length < 2 ^ (prefixWord ++ tailWord_220750).sum := by decide
  have hdescent : baseEnd_220750 < baseStart_220750 := by decide
  rcases family_descends (prefixWord ++ tailWord_220750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220754 : List Nat := [3, 2, 2, 1, 2, 2, 2, 1, 3, 3, 2]
def baseStart_220754 : Nat := 118140960795 + 220754 * 2 ^ 59
def prefixEnd_220754 : Nat := 4983230072969 + 3 ^ 40 * 220754 * 2
def baseEnd_220754 : Nat := 113352908402734532659777

theorem tailTrace_220754 : CollatzResearch.WordTrace tailWord_220754 prefixEnd_220754 113352908402734532659777 := by
  unfold tailWord_220754
  simp only [CollatzResearch.WordTrace]
  refine ⟨2012889960563358656679329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5367706561502289751144877 2012889960563358656679329)
  ·
    refine ⟨1509667470422518992509497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2012889960563358656679329 1509667470422518992509497)
    ·
      refine ⟨1132250602816889244382123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1509667470422518992509497 1132250602816889244382123)
      ·
        refine ⟨1698375904225333866573185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1132250602816889244382123 1698375904225333866573185)
        ·
          refine ⟨1273781928169000399929889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1698375904225333866573185 1273781928169000399929889)
          ·
            refine ⟨955336446126750299947417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1273781928169000399929889 955336446126750299947417)
            ·
              refine ⟨716502334595062724960563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 955336446126750299947417 716502334595062724960563)
              ·
                refine ⟨1074753501892594087440845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716502334595062724960563 1074753501892594087440845)
                ·
                  refine ⟨403032563209722782790317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1074753501892594087440845 403032563209722782790317)
                  ·
                    refine ⟨151137211203646043546369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 403032563209722782790317 151137211203646043546369)
                    ·
                      refine ⟨113352908402734532659777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 151137211203646043546369 113352908402734532659777)
                      ·
                        rfl

theorem cell23_220754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_220754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220754 prefixEnd_220754 := by exact prefixLift 220754
  have htrace : WordTrace (prefixWord ++ tailWord_220754) baseStart_220754 baseEnd_220754 := by
    simpa [prefixWord, tailWord_220754, baseEnd_220754] using wordTrace_append hprefix tailTrace_220754
  have hstable : (prefixWord ++ tailWord_220754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220754).length < 2 ^ (prefixWord ++ tailWord_220754).sum := by decide
  have hdescent : baseEnd_220754 < baseStart_220754 := by decide
  rcases family_descends (prefixWord ++ tailWord_220754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220765 : List Nat := [1, 4, 4, 2, 1, 2, 2, 1, 1, 2, 3]
def baseStart_220765 : Nat := 118140960795 + 220765 * 2 ^ 59
def prefixEnd_220765 : Nat := 4983230072969 + 3 ^ 40 * 220765 * 2
def baseEnd_220765 : Nat := 113358556689933989622227

theorem tailTrace_220765 : CollatzResearch.WordTrace tailWord_220765 prefixEnd_220765 113358556689933989622227 := by
  unfold tailWord_220765
  simp only [CollatzResearch.WordTrace]
  refine ⟨8051961045213583505367749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5367974030142389003578499 8051961045213583505367749)
  ·
    refine ⟨1509742695977546907256453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8051961045213583505367749 1509742695977546907256453)
    ·
      refine ⟨283076755495790045110585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1509742695977546907256453 283076755495790045110585)
      ·
        refine ⟨212307566621842533832939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283076755495790045110585 212307566621842533832939)
        ·
          refine ⟨318461349932763800749409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212307566621842533832939 318461349932763800749409)
          ·
            refine ⟨238846012449572850562057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318461349932763800749409 238846012449572850562057)
            ·
              refine ⟨179134509337179637921543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238846012449572850562057 179134509337179637921543)
              ·
                refine ⟨268701764005769456882315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179134509337179637921543 268701764005769456882315)
                ·
                  refine ⟨403052646008654185323473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 268701764005769456882315 403052646008654185323473)
                  ·
                    refine ⟨302289484506490638992605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 403052646008654185323473 302289484506490638992605)
                    ·
                      refine ⟨113358556689933989622227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 302289484506490638992605 113358556689933989622227)
                      ·
                        rfl

theorem cell23_220765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_220765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220765 prefixEnd_220765 := by exact prefixLift 220765
  have htrace : WordTrace (prefixWord ++ tailWord_220765) baseStart_220765 baseEnd_220765 := by
    simpa [prefixWord, tailWord_220765, baseEnd_220765] using wordTrace_append hprefix tailTrace_220765
  have hstable : (prefixWord ++ tailWord_220765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220765).length < 2 ^ (prefixWord ++ tailWord_220765).sum := by decide
  have hdescent : baseEnd_220765 < baseStart_220765 := by decide
  rcases family_descends (prefixWord ++ tailWord_220765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220771 : List Nat := [1, 1, 1, 5, 1, 3, 4, 1, 1, 3, 2]
def baseStart_220771 : Nat := 118140960795 + 220771 * 2 ^ 59
def prefixEnd_220771 : Nat := 4983230072969 + 3 ^ 40 * 220771 * 2
def baseEnd_220771 : Nat := 113361637573860966147199

theorem tailTrace_220771 : CollatzResearch.WordTrace tailWord_220771 prefixEnd_220771 113361637573860966147199 := by
  unfold tailWord_220771
  simp only [CollatzResearch.WordTrace]
  refine ⟨8052179883191846530086167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5368119922127897686724111 8052179883191846530086167)
  ·
    refine ⟨12078269824787769795129251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8052179883191846530086167 12078269824787769795129251)
    ·
      refine ⟨18117404737181654692693877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12078269824787769795129251 18117404737181654692693877)
      ·
        refine ⟨1698506694110780127440051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18117404737181654692693877 1698506694110780127440051)
        ·
          refine ⟨2547760041166170191160077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1698506694110780127440051 2547760041166170191160077)
          ·
            refine ⟨955410015437313821685029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2547760041166170191160077 955410015437313821685029)
            ·
              refine ⟨179139377894496341565943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 955410015437313821685029 179139377894496341565943)
              ·
                refine ⟨268709066841744512348915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179139377894496341565943 268709066841744512348915)
                ·
                  refine ⟨403063600262616768523373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 268709066841744512348915 403063600262616768523373)
                  ·
                    refine ⟨151148850098481288196265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 403063600262616768523373 151148850098481288196265)
                    ·
                      refine ⟨113361637573860966147199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 151148850098481288196265 113361637573860966147199)
                      ·
                        rfl

theorem cell23_220771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_220771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220771 prefixEnd_220771 := by exact prefixLift 220771
  have htrace : WordTrace (prefixWord ++ tailWord_220771) baseStart_220771 baseEnd_220771 := by
    simpa [prefixWord, tailWord_220771, baseEnd_220771] using wordTrace_append hprefix tailTrace_220771
  have hstable : (prefixWord ++ tailWord_220771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220771).length < 2 ^ (prefixWord ++ tailWord_220771).sum := by decide
  have hdescent : baseEnd_220771 < baseStart_220771 := by decide
  rcases family_descends (prefixWord ++ tailWord_220771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220797 : List Nat := [1, 4, 1, 1, 4, 1, 2, 1, 2, 2, 4]
def baseStart_220797 : Nat := 118140960795 + 220797 * 2 ^ 59
def prefixEnd_220797 : Nat := 4983230072969 + 3 ^ 40 * 220797 * 2
def baseEnd_220797 : Nat := 113374988070877864422079

theorem tailTrace_220797 : CollatzResearch.WordTrace tailWord_220797 prefixEnd_220797 113374988070877864422079 := by
  unfold tailWord_220797
  simp only [CollatzResearch.WordTrace]
  refine ⟨8053128181097652970532645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5368752120731768647021763 8053128181097652970532645)
  ·
    refine ⟨1509961533955809931974871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8053128181097652970532645 1509961533955809931974871)
    ·
      refine ⟨2264942300933714897962307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1509961533955809931974871 2264942300933714897962307)
      ·
        refine ⟨3397413451400572346943461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2264942300933714897962307 3397413451400572346943461)
        ·
          refine ⟨637015022137607315051899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3397413451400572346943461 637015022137607315051899)
          ·
            refine ⟨955522533206410972577849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 637015022137607315051899 955522533206410972577849)
            ·
              refine ⟨716641899904808229433387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 955522533206410972577849 716641899904808229433387)
              ·
                refine ⟨1074962849857212344150081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716641899904808229433387 1074962849857212344150081)
                ·
                  refine ⟨806222137392909258112561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1074962849857212344150081 806222137392909258112561)
                  ·
                    refine ⟨604666603044681943584421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 806222137392909258112561 604666603044681943584421)
                    ·
                      refine ⟨113374988070877864422079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 604666603044681943584421 113374988070877864422079)
                      ·
                        rfl

theorem cell23_220797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_220797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220797 prefixEnd_220797 := by exact prefixLift 220797
  have htrace : WordTrace (prefixWord ++ tailWord_220797) baseStart_220797 baseEnd_220797 := by
    simpa [prefixWord, tailWord_220797, baseEnd_220797] using wordTrace_append hprefix tailTrace_220797
  have hstable : (prefixWord ++ tailWord_220797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220797).length < 2 ^ (prefixWord ++ tailWord_220797).sum := by decide
  have hdescent : baseEnd_220797 < baseStart_220797 := by decide
  rcases family_descends (prefixWord ++ tailWord_220797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220801 : List Nat := [1, 2, 4, 2, 1, 4, 1, 1, 1, 4, 2]
def baseStart_220801 : Nat := 118140960795 + 220801 * 2 ^ 59
def prefixEnd_220801 : Nat := 4983230072969 + 3 ^ 40 * 220801 * 2
def baseEnd_220801 : Nat := 113377041993495848772061

theorem tailTrace_220801 : CollatzResearch.WordTrace tailWord_220801 prefixEnd_220801 113377041993495848772061 := by
  unfold tailWord_220801
  simp only [CollatzResearch.WordTrace]
  refine ⟨8053274073083161653678257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5368849382055441102452171 8053274073083161653678257)
  ·
    refine ⟨6039955554812371240258693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8053274073083161653678257 6039955554812371240258693)
    ·
      refine ⟨1132491666527319607548505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6039955554812371240258693 1132491666527319607548505)
      ·
        refine ⟨849368749895489705661379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1132491666527319607548505 849368749895489705661379)
        ·
          refine ⟨1274053124843234558492069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849368749895489705661379 1274053124843234558492069)
          ·
            refine ⟨238884960908106479717263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1274053124843234558492069 238884960908106479717263)
            ·
              refine ⟨358327441362159719575895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238884960908106479717263 358327441362159719575895)
              ·
                refine ⟨537491162043239579363843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 358327441362159719575895 537491162043239579363843)
                ·
                  refine ⟨806236743064859369045765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 537491162043239579363843 806236743064859369045765)
                  ·
                    refine ⟨151169389324661131696081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 806236743064859369045765 151169389324661131696081)
                    ·
                      refine ⟨113377041993495848772061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 151169389324661131696081 113377041993495848772061)
                      ·
                        rfl

theorem cell23_220801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_220801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220801 prefixEnd_220801 := by exact prefixLift 220801
  have htrace : WordTrace (prefixWord ++ tailWord_220801) baseStart_220801 baseEnd_220801 := by
    simpa [prefixWord, tailWord_220801, baseEnd_220801] using wordTrace_append hprefix tailTrace_220801
  have hstable : (prefixWord ++ tailWord_220801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220801).length < 2 ^ (prefixWord ++ tailWord_220801).sum := by decide
  have hdescent : baseEnd_220801 < baseStart_220801 := by decide
  rcases family_descends (prefixWord ++ tailWord_220801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220824 : List Nat := [2, 1, 2, 4, 1, 2, 3, 3, 5]
def baseStart_220824 : Nat := 118140960795 + 220824 * 2 ^ 59
def prefixEnd_220824 : Nat := 4983230072969 + 3 ^ 40 * 220824 * 2
def baseEnd_220824 : Nat := 12598761338727695420495

theorem tailTrace_220824 : CollatzResearch.WordTrace tailWord_220824 prefixEnd_220824 12598761338727695420495 := by
  unfold tailWord_220824
  simp only [CollatzResearch.WordTrace]
  refine ⟨4027056475999918290882763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5369408634666557721177017 4027056475999918290882763)
  ·
    refine ⟨6040584713999877436324145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4027056475999918290882763 6040584713999877436324145)
    ·
      refine ⟨4530438535499908077243109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6040584713999877436324145 4530438535499908077243109)
      ·
        refine ⟨849457225406232764483083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4530438535499908077243109 849457225406232764483083)
        ·
          refine ⟨1274185838109349146724625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849457225406232764483083 1274185838109349146724625)
          ·
            refine ⟨955639378582011860043469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1274185838109349146724625 955639378582011860043469)
            ·
              refine ⟨358364766968254447516301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 955639378582011860043469 358364766968254447516301)
              ·
                refine ⟨134386787613095417818613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 358364766968254447516301 134386787613095417818613)
                ·
                  refine ⟨12598761338727695420495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134386787613095417818613 12598761338727695420495)
                  ·
                    rfl

theorem cell23_220824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3, 5].length) (baseStart_220824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220824 prefixEnd_220824 := by exact prefixLift 220824
  have htrace : WordTrace (prefixWord ++ tailWord_220824) baseStart_220824 baseEnd_220824 := by
    simpa [prefixWord, tailWord_220824, baseEnd_220824] using wordTrace_append hprefix tailTrace_220824
  have hstable : (prefixWord ++ tailWord_220824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220824).length < 2 ^ (prefixWord ++ tailWord_220824).sum := by decide
  have hdescent : baseEnd_220824 < baseStart_220824 := by decide
  rcases family_descends (prefixWord ++ tailWord_220824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220880 : List Nat := [2, 1, 1, 1, 1, 2, 1, 6, 8]
def baseStart_220880 : Nat := 118140960795 + 220880 * 2 ^ 59
def prefixEnd_220880 : Nat := 4983230072969 + 3 ^ 40 * 220880 * 2
def baseEnd_220880 : Nat := 12601956329466782187133

theorem tailTrace_220880 : CollatzResearch.WordTrace tailWord_220880 prefixEnd_220880 12601956329466782187133 := by
  unfold tailWord_220880
  simp only [CollatzResearch.WordTrace]
  refine ⟨4028077719898479072902047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5370770293197972097202729 4028077719898479072902047)
  ·
    refine ⟨6042116579847718609353071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4028077719898479072902047 6042116579847718609353071)
    ·
      refine ⟨9063174869771577914029607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6042116579847718609353071 9063174869771577914029607)
      ·
        refine ⟨13594762304657366871044411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9063174869771577914029607 13594762304657366871044411)
        ·
          refine ⟨20392143456986050306566617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13594762304657366871044411 20392143456986050306566617)
          ·
            refine ⟨15294107592739537729924963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20392143456986050306566617 15294107592739537729924963)
            ·
              refine ⟨22941161389109306594887445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15294107592739537729924963 22941161389109306594887445)
              ·
                refine ⟨1075366940114498746635349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22941161389109306594887445 1075366940114498746635349)
                ·
                  refine ⟨12601956329466782187133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1075366940114498746635349 12601956329466782187133)
                  ·
                    rfl

theorem cell23_220880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 8].length) (baseStart_220880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220880 prefixEnd_220880 := by exact prefixLift 220880
  have htrace : WordTrace (prefixWord ++ tailWord_220880) baseStart_220880 baseEnd_220880 := by
    simpa [prefixWord, tailWord_220880, baseEnd_220880] using wordTrace_append hprefix tailTrace_220880
  have hstable : (prefixWord ++ tailWord_220880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220880).length < 2 ^ (prefixWord ++ tailWord_220880).sum := by decide
  have hdescent : baseEnd_220880 < baseStart_220880 := by decide
  rcases family_descends (prefixWord ++ tailWord_220880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220901 : List Nat := [1, 3, 1, 4, 1, 1, 3, 4, 1, 4]
def baseStart_220901 : Nat := 118140960795 + 220901 * 2 ^ 59
def prefixEnd_220901 : Nat := 4983230072969 + 3 ^ 40 * 220901 * 2
def baseEnd_220901 : Nat := 37809463352981819173867

theorem tailTrace_220901 : CollatzResearch.WordTrace tailWord_220901 prefixEnd_220901 37809463352981819173867 := by
  unfold tailWord_220901
  simp only [CollatzResearch.WordTrace]
  refine ⟨8056921372720878732318557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5371280915147252488212371 8056921372720878732318557)
  ·
    refine ⟨3021345514770329524619459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8056921372720878732318557 3021345514770329524619459)
    ·
      refine ⟨4532018272155494286929189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3021345514770329524619459 4532018272155494286929189)
      ·
        refine ⟨849753426029155178799223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4532018272155494286929189 849753426029155178799223)
        ·
          refine ⟨1274630139043732768198835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849753426029155178799223 1274630139043732768198835)
          ·
            refine ⟨1911945208565599152298253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1274630139043732768198835 1911945208565599152298253)
            ·
              refine ⟨716979453212099682111845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1911945208565599152298253 716979453212099682111845)
              ·
                refine ⟨134433647477268690395971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 716979453212099682111845 134433647477268690395971)
                ·
                  refine ⟨201650471215903035593957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134433647477268690395971 201650471215903035593957)
                  ·
                    refine ⟨37809463352981819173867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 201650471215903035593957 37809463352981819173867)
                    ·
                      rfl

theorem cell23_220901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4, 1, 4].length) (baseStart_220901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220901 prefixEnd_220901 := by exact prefixLift 220901
  have htrace : WordTrace (prefixWord ++ tailWord_220901) baseStart_220901 baseEnd_220901 := by
    simpa [prefixWord, tailWord_220901, baseEnd_220901] using wordTrace_append hprefix tailTrace_220901
  have hstable : (prefixWord ++ tailWord_220901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220901).length < 2 ^ (prefixWord ++ tailWord_220901).sum := by decide
  have hdescent : baseEnd_220901 < baseStart_220901 := by decide
  rcases family_descends (prefixWord ++ tailWord_220901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220927 : List Nat := [1, 1, 2, 2, 1, 3, 4, 1, 3, 5]
def baseStart_220927 : Nat := 118140960795 + 220927 * 2 ^ 59
def prefixEnd_220927 : Nat := 4983230072969 + 3 ^ 40 * 220927 * 2
def baseEnd_220927 : Nat := 37813913518654118598827

theorem tailTrace_220927 : CollatzResearch.WordTrace tailWord_220927 prefixEnd_220927 37813913518654118598827 := by
  unfold tailWord_220927
  simp only [CollatzResearch.WordTrace]
  refine ⟨8057869670626685172765035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5371913113751123448510023 8057869670626685172765035)
  ·
    refine ⟨12086804505940027759147553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8057869670626685172765035 12086804505940027759147553)
    ·
      refine ⟨9065103379455020819360665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12086804505940027759147553 9065103379455020819360665)
      ·
        refine ⟨6798827534591265614520499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9065103379455020819360665 6798827534591265614520499)
        ·
          refine ⟨10198241301886898421780749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6798827534591265614520499 10198241301886898421780749)
          ·
            refine ⟨3824340488207586908167781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10198241301886898421780749 3824340488207586908167781)
            ·
              refine ⟨717063841538922545281459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3824340488207586908167781 717063841538922545281459)
              ·
                refine ⟨1075595762308383817922189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 717063841538922545281459 1075595762308383817922189)
                ·
                  refine ⟨403348410865643931720821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075595762308383817922189 403348410865643931720821)
                  ·
                    refine ⟨37813913518654118598827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 403348410865643931720821 37813913518654118598827)
                    ·
                      rfl

theorem cell23_220927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 5].length) (baseStart_220927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220927 prefixEnd_220927 := by exact prefixLift 220927
  have htrace : WordTrace (prefixWord ++ tailWord_220927) baseStart_220927 baseEnd_220927 := by
    simpa [prefixWord, tailWord_220927, baseEnd_220927] using wordTrace_append hprefix tailTrace_220927
  have hstable : (prefixWord ++ tailWord_220927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220927).length < 2 ^ (prefixWord ++ tailWord_220927).sum := by decide
  have hdescent : baseEnd_220927 < baseStart_220927 := by decide
  rcases family_descends (prefixWord ++ tailWord_220927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220947 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 4]
def baseStart_220947 : Nat := 118140960795 + 220947 * 2 ^ 59
def prefixEnd_220947 : Nat := 4983230072969 + 3 ^ 40 * 220947 * 2
def baseEnd_220947 : Nat := 113452010169052277546389

theorem tailTrace_220947 : CollatzResearch.WordTrace tailWord_220947 prefixEnd_220947 113452010169052277546389 := by
  unfold tailWord_220947
  simp only [CollatzResearch.WordTrace]
  refine ⟨8058599130554228588493095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5372399420369485725662063 8058599130554228588493095)
  ·
    refine ⟨12087898695831342882739643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8058599130554228588493095 12087898695831342882739643)
    ·
      refine ⟨18131848043747014324109465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12087898695831342882739643 18131848043747014324109465)
      ·
        refine ⟨13598886032810260743082099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18131848043747014324109465 13598886032810260743082099)
        ·
          refine ⟨20398329049215391114623149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13598886032810260743082099 20398329049215391114623149)
          ·
            refine ⟨7649373393455771667983681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20398329049215391114623149 7649373393455771667983681)
            ·
              refine ⟨5737030045091828750987761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7649373393455771667983681 5737030045091828750987761)
              ·
                refine ⟨4302772533818871563240821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5737030045091828750987761 4302772533818871563240821)
                ·
                  refine ⟨403384925045519209053827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4302772533818871563240821 403384925045519209053827)
                  ·
                    refine ⟨605077387568278813580741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 403384925045519209053827 605077387568278813580741)
                    ·
                      refine ⟨113452010169052277546389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 605077387568278813580741 113452010169052277546389)
                      ·
                        rfl

theorem cell23_220947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 4].length) (baseStart_220947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220947 prefixEnd_220947 := by exact prefixLift 220947
  have htrace : WordTrace (prefixWord ++ tailWord_220947) baseStart_220947 baseEnd_220947 := by
    simpa [prefixWord, tailWord_220947, baseEnd_220947] using wordTrace_append hprefix tailTrace_220947
  have hstable : (prefixWord ++ tailWord_220947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220947).length < 2 ^ (prefixWord ++ tailWord_220947).sum := by decide
  have hdescent : baseEnd_220947 < baseStart_220947 := by decide
  rcases family_descends (prefixWord ++ tailWord_220947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220948 : List Nat := [2, 4, 4, 1, 1, 1, 1, 1, 8]
def baseStart_220948 : Nat := 118140960795 + 220948 * 2 ^ 59
def prefixEnd_220948 : Nat := 4983230072969 + 3 ^ 40 * 220948 * 2
def baseEnd_220948 : Nat := 12605835961078530403765

theorem tailTrace_220948 : CollatzResearch.WordTrace tailWord_220948 prefixEnd_220948 12605835961078530403765 := by
  unfold tailWord_220948
  simp only [CollatzResearch.WordTrace]
  refine ⟨4029317801775302879639749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5372423735700403839519665 4029317801775302879639749)
  ·
    refine ⟨755497087832869289932453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4029317801775302879639749 755497087832869289932453)
    ·
      refine ⟨141655703968662991862335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 755497087832869289932453 141655703968662991862335)
      ·
        refine ⟨212483555952994487793503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141655703968662991862335 212483555952994487793503)
        ·
          refine ⟨318725333929491731690255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212483555952994487793503 318725333929491731690255)
          ·
            refine ⟨478088000894237597535383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318725333929491731690255 478088000894237597535383)
            ·
              refine ⟨717132001341356396303075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478088000894237597535383 717132001341356396303075)
              ·
                refine ⟨1075698002012034594454613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 717132001341356396303075 1075698002012034594454613)
                ·
                  refine ⟨12605835961078530403765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1075698002012034594454613 12605835961078530403765)
                  ·
                    rfl

theorem cell23_220948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_220948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_220948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_220948 prefixEnd_220948 := by exact prefixLift 220948
  have htrace : WordTrace (prefixWord ++ tailWord_220948) baseStart_220948 baseEnd_220948 := by
    simpa [prefixWord, tailWord_220948, baseEnd_220948] using wordTrace_append hprefix tailTrace_220948
  have hstable : (prefixWord ++ tailWord_220948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220948).length < 2 ^ (prefixWord ++ tailWord_220948).sum := by decide
  have hdescent : baseEnd_220948 < baseStart_220948 := by decide
  rcases family_descends (prefixWord ++ tailWord_220948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221004 : List Nat := [2, 2, 1, 3, 4, 2, 9]
def baseStart_221004 : Nat := 118140960795 + 221004 * 2 ^ 59
def prefixEnd_221004 : Nat := 4983230072969 + 3 ^ 40 * 221004 * 2
def baseEnd_221004 : Nat := 1401003439090846352267

theorem tailTrace_221004 : CollatzResearch.WordTrace tailWord_221004 prefixEnd_221004 1401003439090846352267 := by
  unfold tailWord_221004
  simp only [CollatzResearch.WordTrace]
  refine ⟨4030339045673863661659033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5373785394231818215545377 4030339045673863661659033)
  ·
    refine ⟨3022754284255397746244275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4030339045673863661659033 3022754284255397746244275)
    ·
      refine ⟨4534131426383096619366413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3022754284255397746244275 4534131426383096619366413)
      ·
        refine ⟨1700299284893661232262405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4534131426383096619366413 1700299284893661232262405)
        ·
          refine ⟨318806115917561481049201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1700299284893661232262405 318806115917561481049201)
          ·
            refine ⟨239104586938171110786901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318806115917561481049201 239104586938171110786901)
            ·
              refine ⟨1401003439090846352267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 239104586938171110786901 1401003439090846352267)
              ·
                rfl

theorem cell23_221004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 9].length) (baseStart_221004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221004 prefixEnd_221004 := by exact prefixLift 221004
  have htrace : WordTrace (prefixWord ++ tailWord_221004) baseStart_221004 baseEnd_221004 := by
    simpa [prefixWord, tailWord_221004, baseEnd_221004] using wordTrace_append hprefix tailTrace_221004
  have hstable : (prefixWord ++ tailWord_221004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221004).length < 2 ^ (prefixWord ++ tailWord_221004).sum := by decide
  have hdescent : baseEnd_221004 < baseStart_221004 := by decide
  rcases family_descends (prefixWord ++ tailWord_221004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221015 : List Nat := [1, 1, 3, 2, 5, 2, 1, 1, 3, 2, 2]
def baseStart_221015 : Nat := 118140960795 + 221015 * 2 ^ 59
def prefixEnd_221015 : Nat := 4983230072969 + 3 ^ 40 * 221015 * 2
def baseEnd_221015 : Nat := 113486926853558011496077

theorem tailTrace_221015 : CollatzResearch.WordTrace tailWord_221015 prefixEnd_221015 113486926853558011496077 := by
  unfold tailWord_221015
  simp only [CollatzResearch.WordTrace]
  refine ⟨8061079294307876201968499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5374052862871917467978999 8061079294307876201968499)
  ·
    refine ⟨12091618941461814302952749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8061079294307876201968499 12091618941461814302952749)
    ·
      refine ⟨4534357103048180363607281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12091618941461814302952749 4534357103048180363607281)
      ·
        refine ⟨3400767827286135272705461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4534357103048180363607281 3400767827286135272705461)
        ·
          refine ⟨318821983808075181816137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3400767827286135272705461 318821983808075181816137)
          ·
            refine ⟨239116487856056386362103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318821983808075181816137 239116487856056386362103)
            ·
              refine ⟨358674731784084579543155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239116487856056386362103 358674731784084579543155)
              ·
                refine ⟨538012097676126869314733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 358674731784084579543155 538012097676126869314733)
                ·
                  refine ⟨201754536628547575993025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 538012097676126869314733 201754536628547575993025)
                  ·
                    refine ⟨151315902471410681994769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 201754536628547575993025 151315902471410681994769)
                    ·
                      refine ⟨113486926853558011496077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 151315902471410681994769 113486926853558011496077)
                      ·
                        rfl

theorem cell23_221015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3, 2, 2].length) (baseStart_221015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221015 prefixEnd_221015 := by exact prefixLift 221015
  have htrace : WordTrace (prefixWord ++ tailWord_221015) baseStart_221015 baseEnd_221015 := by
    simpa [prefixWord, tailWord_221015, baseEnd_221015] using wordTrace_append hprefix tailTrace_221015
  have hstable : (prefixWord ++ tailWord_221015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221015).length < 2 ^ (prefixWord ++ tailWord_221015).sum := by decide
  have hdescent : baseEnd_221015 < baseStart_221015 := by decide
  rcases family_descends (prefixWord ++ tailWord_221015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221017 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 2, 7]
def baseStart_221017 : Nat := 118140960795 + 221017 * 2 ^ 59
def prefixEnd_221017 : Nat := 4983230072969 + 3 ^ 40 * 221017 * 2
def baseEnd_221017 : Nat := 37829317938289001223689

theorem tailTrace_221017 : CollatzResearch.WordTrace tailWord_221017 prefixEnd_221017 37829317938289001223689 := by
  unfold tailWord_221017
  simp only [CollatzResearch.WordTrace]
  refine ⟨8061152240300630543541305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5374101493533753695694203 8061152240300630543541305)
  ·
    refine ⟨6045864180225472907655979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8061152240300630543541305 6045864180225472907655979)
    ·
      refine ⟨9068796270338209361483969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6045864180225472907655979 9068796270338209361483969)
      ·
        refine ⟨6801597202753657021112977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9068796270338209361483969 6801597202753657021112977)
        ·
          refine ⟨5101197902065242765834733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6801597202753657021112977 5101197902065242765834733)
          ·
            refine ⟨1912949213274466037188025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5101197902065242765834733 1912949213274466037188025)
            ·
              refine ⟨1434711909955849527891019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1912949213274466037188025 1434711909955849527891019)
              ·
                refine ⟨2152067864933774291836529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1434711909955849527891019 2152067864933774291836529)
                ·
                  refine ⟨1614050898700330718877397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2152067864933774291836529 1614050898700330718877397)
                  ·
                    refine ⟨37829317938289001223689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1614050898700330718877397 37829317938289001223689)
                    ·
                      rfl

theorem cell23_221017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 7].length) (baseStart_221017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221017 prefixEnd_221017 := by exact prefixLift 221017
  have htrace : WordTrace (prefixWord ++ tailWord_221017) baseStart_221017 baseEnd_221017 := by
    simpa [prefixWord, tailWord_221017, baseEnd_221017] using wordTrace_append hprefix tailTrace_221017
  have hstable : (prefixWord ++ tailWord_221017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221017).length < 2 ^ (prefixWord ++ tailWord_221017).sum := by decide
  have hdescent : baseEnd_221017 < baseStart_221017 := by decide
  rcases family_descends (prefixWord ++ tailWord_221017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221041 : List Nat := [1, 2, 2, 2, 1, 3, 3, 1, 3, 3, 2]
def baseStart_221041 : Nat := 118140960795 + 221041 * 2 ^ 59
def prefixEnd_221041 : Nat := 4983230072969 + 3 ^ 40 * 221041 * 2
def baseEnd_221041 : Nat := 113500277350574909770957

theorem tailTrace_221041 : CollatzResearch.WordTrace tailWord_221041 prefixEnd_221041 113500277350574909770957 := by
  unfold tailWord_221041
  simp only [CollatzResearch.WordTrace]
  refine ⟨8062027592213682642414977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5374685061475788428276651 8062027592213682642414977)
  ·
    refine ⟨6046520694160261981811233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8062027592213682642414977 6046520694160261981811233)
    ·
      refine ⟨4534890520620196486358425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6046520694160261981811233 4534890520620196486358425)
      ·
        refine ⟨3401167890465147364768819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4534890520620196486358425 3401167890465147364768819)
        ·
          refine ⟨5101751835697721047153229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3401167890465147364768819 5101751835697721047153229)
          ·
            refine ⟨1913156938386645392682461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5101751835697721047153229 1913156938386645392682461)
            ·
              refine ⟨717433851894992022255923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1913156938386645392682461 717433851894992022255923)
              ·
                refine ⟨1076150777842488033383885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 717433851894992022255923 1076150777842488033383885)
                ·
                  refine ⟨403556541690933012518957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1076150777842488033383885 403556541690933012518957)
                  ·
                    refine ⟨151333703134099879694609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 403556541690933012518957 151333703134099879694609)
                    ·
                      refine ⟨113500277350574909770957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 151333703134099879694609 113500277350574909770957)
                      ·
                        rfl

theorem cell23_221041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 3, 2].length) (baseStart_221041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221041 prefixEnd_221041 := by exact prefixLift 221041
  have htrace : WordTrace (prefixWord ++ tailWord_221041) baseStart_221041 baseEnd_221041 := by
    simpa [prefixWord, tailWord_221041, baseEnd_221041] using wordTrace_append hprefix tailTrace_221041
  have hstable : (prefixWord ++ tailWord_221041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221041).length < 2 ^ (prefixWord ++ tailWord_221041).sum := by decide
  have hdescent : baseEnd_221041 < baseStart_221041 := by decide
  rcases family_descends (prefixWord ++ tailWord_221041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221047 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 6, 6]
def baseStart_221047 : Nat := 118140960795 + 221047 * 2 ^ 59
def prefixEnd_221047 : Nat := 4983230072969 + 3 ^ 40 * 221047 * 2
def baseEnd_221047 : Nat := 37834452744833962098643

theorem tailTrace_221047 : CollatzResearch.WordTrace tailWord_221047 prefixEnd_221047 37834452744833962098643 := by
  unfold tailWord_221047
  simp only [CollatzResearch.WordTrace]
  refine ⟨8062246430191945667133395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5374830953461297111422263 8062246430191945667133395)
  ·
    refine ⟨12093369645287918500700093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8062246430191945667133395 12093369645287918500700093)
    ·
      refine ⟨4535013616982969437762535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12093369645287918500700093 4535013616982969437762535)
      ·
        refine ⟨6802520425474454156643803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4535013616982969437762535 6802520425474454156643803)
        ·
          refine ⟨10203780638211681234965705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6802520425474454156643803 10203780638211681234965705)
          ·
            refine ⟨7652835478658760926224279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10203780638211681234965705 7652835478658760926224279)
            ·
              refine ⟨11479253217988141389336419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7652835478658760926224279 11479253217988141389336419)
              ·
                refine ⟨17218879826982212084004629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11479253217988141389336419 17218879826982212084004629)
                ·
                  refine ⟨807134991889791191437717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17218879826982212084004629 807134991889791191437717)
                  ·
                    refine ⟨37834452744833962098643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 807134991889791191437717 37834452744833962098643)
                    ·
                      rfl

theorem cell23_221047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 6].length) (baseStart_221047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221047 prefixEnd_221047 := by exact prefixLift 221047
  have htrace : WordTrace (prefixWord ++ tailWord_221047) baseStart_221047 baseEnd_221047 := by
    simpa [prefixWord, tailWord_221047, baseEnd_221047] using wordTrace_append hprefix tailTrace_221047
  have hstable : (prefixWord ++ tailWord_221047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221047).length < 2 ^ (prefixWord ++ tailWord_221047).sum := by decide
  have hdescent : baseEnd_221047 < baseStart_221047 := by decide
  rcases family_descends (prefixWord ++ tailWord_221047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221066 : List Nat := [3, 1, 2, 4, 3, 1, 2, 2, 1, 2, 2]
def baseStart_221066 : Nat := 118140960795 + 221066 * 2 ^ 59
def prefixEnd_221066 : Nat := 4983230072969 + 3 ^ 40 * 221066 * 2
def baseEnd_221066 : Nat := 113513114366937311958343

theorem tailTrace_221066 : CollatzResearch.WordTrace tailWord_221066 prefixEnd_221066 113513114366937311958343 := by
  unfold tailWord_221066
  simp only [CollatzResearch.WordTrace]
  refine ⟨2015734854280777978018763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5375292944748741274716701 2015734854280777978018763)
  ·
    refine ⟨3023602281421166967028145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2015734854280777978018763 3023602281421166967028145)
    ·
      refine ⟨2267701711065875225271109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3023602281421166967028145 2267701711065875225271109)
      ·
        refine ⟨425194070824851604738333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2267701711065875225271109 425194070824851604738333)
        ·
          refine ⟨159447776559319351776875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 425194070824851604738333 159447776559319351776875)
          ·
            refine ⟨239171664838979027665313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159447776559319351776875 239171664838979027665313)
            ·
              refine ⟨179378748629234270748985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239171664838979027665313 179378748629234270748985)
              ·
                refine ⟨134534061471925703061739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179378748629234270748985 134534061471925703061739)
                ·
                  refine ⟨201801092207888554592609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134534061471925703061739 201801092207888554592609)
                  ·
                    refine ⟨151350819155916415944457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 201801092207888554592609 151350819155916415944457)
                    ·
                      refine ⟨113513114366937311958343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 151350819155916415944457 113513114366937311958343)
                      ·
                        rfl

theorem cell23_221066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_221066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221066 prefixEnd_221066 := by exact prefixLift 221066
  have htrace : WordTrace (prefixWord ++ tailWord_221066) baseStart_221066 baseEnd_221066 := by
    simpa [prefixWord, tailWord_221066, baseEnd_221066] using wordTrace_append hprefix tailTrace_221066
  have hstable : (prefixWord ++ tailWord_221066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221066).length < 2 ^ (prefixWord ++ tailWord_221066).sum := by decide
  have hdescent : baseEnd_221066 < baseStart_221066 := by decide
  rcases family_descends (prefixWord ++ tailWord_221066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221067 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 6]
def baseStart_221067 : Nat := 118140960795 + 221067 * 2 ^ 59
def prefixEnd_221067 : Nat := 4983230072969 + 3 ^ 40 * 221067 * 2
def baseEnd_221067 : Nat := 113513627847591808045837

theorem tailTrace_221067 : CollatzResearch.WordTrace tailWord_221067 prefixEnd_221067 113513627847591808045837 := by
  unfold tailWord_221067
  simp only [CollatzResearch.WordTrace]
  refine ⟨8062975890119489082861455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5375317260079659388574303 8062975890119489082861455)
  ·
    refine ⟨12094463835179233624292183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8062975890119489082861455 12094463835179233624292183)
    ·
      refine ⟨18141695752768850436438275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12094463835179233624292183 18141695752768850436438275)
      ·
        refine ⟨27212543629153275654657413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18141695752768850436438275 27212543629153275654657413)
        ·
          refine ⟨5102351930466239185248265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27212543629153275654657413 5102351930466239185248265)
          ·
            refine ⟨3826763947849679388936199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5102351930466239185248265 3826763947849679388936199)
            ·
              refine ⟨5740145921774519083404299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3826763947849679388936199 5740145921774519083404299)
              ·
                refine ⟨8610218882661778625106449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5740145921774519083404299 8610218882661778625106449)
                ·
                  refine ⟨6457664161996333968829837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8610218882661778625106449 6457664161996333968829837)
                  ·
                    refine ⟨2421624060748625238311189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6457664161996333968829837 2421624060748625238311189)
                    ·
                      refine ⟨113513627847591808045837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2421624060748625238311189 113513627847591808045837)
                      ·
                        rfl

theorem cell23_221067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 6].length) (baseStart_221067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221067 prefixEnd_221067 := by exact prefixLift 221067
  have htrace : WordTrace (prefixWord ++ tailWord_221067) baseStart_221067 baseEnd_221067 := by
    simpa [prefixWord, tailWord_221067, baseEnd_221067] using wordTrace_append hprefix tailTrace_221067
  have hstable : (prefixWord ++ tailWord_221067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221067).length < 2 ^ (prefixWord ++ tailWord_221067).sum := by decide
  have hdescent : baseEnd_221067 < baseStart_221067 := by decide
  rcases family_descends (prefixWord ++ tailWord_221067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221071 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 10, 2, 2]
def baseStart_221071 : Nat := 118140960795 + 221071 * 2 ^ 59
def prefixEnd_221071 : Nat := 4983230072969 + 3 ^ 40 * 221071 * 2
def baseEnd_221071 : Nat := 113515681770209792395819

theorem tailTrace_221071 : CollatzResearch.WordTrace tailWord_221071 prefixEnd_221071 113515681770209792395819 := by
  unfold tailWord_221071
  simp only [CollatzResearch.WordTrace]
  refine ⟨8063121782104997766007067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5375414521403331844004711 8063121782104997766007067)
  ·
    refine ⟨12094682673157496649010601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8063121782104997766007067 12094682673157496649010601)
    ·
      refine ⟨9071012004868122486757951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12094682673157496649010601 9071012004868122486757951)
      ·
        refine ⟨13606518007302183730136927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9071012004868122486757951 13606518007302183730136927)
        ·
          refine ⟨20409777010953275595205391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13606518007302183730136927 20409777010953275595205391)
          ·
            refine ⟨30614665516429913392808087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20409777010953275595205391 30614665516429913392808087)
            ·
              refine ⟨45921998274644870089212131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30614665516429913392808087 45921998274644870089212131)
              ·
                refine ⟨68882997411967305133818197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45921998274644870089212131 68882997411967305133818197)
                ·
                  refine ⟨201805656480372964259233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 68882997411967305133818197 201805656480372964259233)
                  ·
                    refine ⟨151354242360279723194425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 201805656480372964259233 151354242360279723194425)
                    ·
                      refine ⟨113515681770209792395819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 151354242360279723194425 113515681770209792395819)
                      ·
                        rfl

theorem cell23_221071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10, 2, 2].length) (baseStart_221071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221071 prefixEnd_221071 := by exact prefixLift 221071
  have htrace : WordTrace (prefixWord ++ tailWord_221071) baseStart_221071 baseEnd_221071 := by
    simpa [prefixWord, tailWord_221071, baseEnd_221071] using wordTrace_append hprefix tailTrace_221071
  have hstable : (prefixWord ++ tailWord_221071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221071).length < 2 ^ (prefixWord ++ tailWord_221071).sum := by decide
  have hdescent : baseEnd_221071 < baseStart_221071 := by decide
  rcases family_descends (prefixWord ++ tailWord_221071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221134 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7]
def baseStart_221134 : Nat := 118140960795 + 221134 * 2 ^ 59
def prefixEnd_221134 : Nat := 4983230072969 + 3 ^ 40 * 221134 * 2
def baseEnd_221134 : Nat := 113548031051443045908029

theorem tailTrace_221134 : CollatzResearch.WordTrace tailWord_221134 prefixEnd_221134 113548031051443045908029 := by
  unfold tailWord_221134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1008177447609594940693807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5376946387251173017033637 1008177447609594940693807)
  ·
    refine ⟨1512266171414392411040711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1008177447609594940693807 1512266171414392411040711)
    ·
      refine ⟨2268399257121588616561067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1512266171414392411040711 2268399257121588616561067)
      ·
        refine ⟨3402598885682382924841601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2268399257121588616561067 3402598885682382924841601)
        ·
          refine ⟨2551949164261787193631201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3402598885682382924841601 2551949164261787193631201)
          ·
            refine ⟨1913961873196340395223401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2551949164261787193631201 1913961873196340395223401)
            ·
              refine ⟨1435471404897255296417551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1913961873196340395223401 1435471404897255296417551)
              ·
                refine ⟨2153207107345882944626327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1435471404897255296417551 2153207107345882944626327)
                ·
                  refine ⟨3229810661018824416939491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2153207107345882944626327 3229810661018824416939491)
                  ·
                    refine ⟨4844715991528236625409237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3229810661018824416939491 4844715991528236625409237)
                    ·
                      refine ⟨113548031051443045908029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 4844715991528236625409237 113548031051443045908029)
                      ·
                        rfl

theorem cell23_221134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_221134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221134 prefixEnd_221134 := by exact prefixLift 221134
  have htrace : WordTrace (prefixWord ++ tailWord_221134) baseStart_221134 baseEnd_221134 := by
    simpa [prefixWord, tailWord_221134, baseEnd_221134] using wordTrace_append hprefix tailTrace_221134
  have hstable : (prefixWord ++ tailWord_221134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221134).length < 2 ^ (prefixWord ++ tailWord_221134).sum := by decide
  have hdescent : baseEnd_221134 < baseStart_221134 := by decide
  rcases family_descends (prefixWord ++ tailWord_221134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221144 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 3, 3, 4]
def baseStart_221144 : Nat := 118140960795 + 221144 * 2 ^ 59
def prefixEnd_221144 : Nat := 4983230072969 + 3 ^ 40 * 221144 * 2
def baseEnd_221144 : Nat := 113553165857988006782983

theorem tailTrace_221144 : CollatzResearch.WordTrace tailWord_221144 prefixEnd_221144 113553165857988006782983 := by
  unfold tailWord_221144
  simp only [CollatzResearch.WordTrace]
  refine ⟨4032892155420265616707243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5377189540560354155609657 4032892155420265616707243)
  ·
    refine ⟨6049338233130398425060865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4032892155420265616707243 6049338233130398425060865)
    ·
      refine ⟨4537003674847798818795649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6049338233130398425060865 4537003674847798818795649)
      ·
        refine ⟨3402752756135849114096737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4537003674847798818795649 3402752756135849114096737)
        ·
          refine ⟨2552064567101886835572553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3402752756135849114096737 2552064567101886835572553)
          ·
            refine ⟨1914048425326415126679415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2552064567101886835572553 1914048425326415126679415)
            ·
              refine ⟨2871072637989622690019123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1914048425326415126679415 2871072637989622690019123)
              ·
                refine ⟨4306608956984434035028685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2871072637989622690019123 4306608956984434035028685)
                ·
                  refine ⟨1614978358869162763135757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4306608956984434035028685 1614978358869162763135757)
                  ·
                    refine ⟨605616884575936036175909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1614978358869162763135757 605616884575936036175909)
                    ·
                      refine ⟨113553165857988006782983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 605616884575936036175909 113553165857988006782983)
                      ·
                        rfl

theorem cell23_221144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_221144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221144 prefixEnd_221144 := by exact prefixLift 221144
  have htrace : WordTrace (prefixWord ++ tailWord_221144) baseStart_221144 baseEnd_221144 := by
    simpa [prefixWord, tailWord_221144, baseEnd_221144] using wordTrace_append hprefix tailTrace_221144
  have hstable : (prefixWord ++ tailWord_221144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221144).length < 2 ^ (prefixWord ++ tailWord_221144).sum := by decide
  have hdescent : baseEnd_221144 < baseStart_221144 := by decide
  rcases family_descends (prefixWord ++ tailWord_221144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221181 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 4, 2, 3]
def baseStart_221181 : Nat := 118140960795 + 221181 * 2 ^ 59
def prefixEnd_221181 : Nat := 4983230072969 + 3 ^ 40 * 221181 * 2
def baseEnd_221181 : Nat := 113572164642204362020313

theorem tailTrace_221181 : CollatzResearch.WordTrace tailWord_221181 prefixEnd_221181 113572164642204362020313 := by
  unfold tailWord_221181
  simp only [CollatzResearch.WordTrace]
  refine ⟨8067133811706486552511397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5378089207804324368340931 8067133811706486552511397)
  ·
    refine ⟨1512587589694966228595887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8067133811706486552511397 1512587589694966228595887)
    ·
      refine ⟨2268881384542449342893831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1512587589694966228595887 2268881384542449342893831)
      ·
        refine ⟨3403322076813674014340747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2268881384542449342893831 3403322076813674014340747)
        ·
          refine ⟨5104983115220511021511121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3403322076813674014340747 5104983115220511021511121)
          ·
            refine ⟨3828737336415383266133341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5104983115220511021511121 3828737336415383266133341)
            ·
              refine ⟨1435776501155768724800003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3828737336415383266133341 1435776501155768724800003)
              ·
                refine ⟨2153664751733653087200005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1435776501155768724800003 2153664751733653087200005)
                ·
                  refine ⟨403812140950059953850001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2153664751733653087200005 403812140950059953850001)
                  ·
                    refine ⟨302859105712544965387501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 403812140950059953850001 302859105712544965387501)
                    ·
                      refine ⟨113572164642204362020313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 302859105712544965387501 113572164642204362020313)
                      ·
                        rfl

theorem cell23_221181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_221181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221181 prefixEnd_221181 := by exact prefixLift 221181
  have htrace : WordTrace (prefixWord ++ tailWord_221181) baseStart_221181 baseEnd_221181 := by
    simpa [prefixWord, tailWord_221181, baseEnd_221181] using wordTrace_append hprefix tailTrace_221181
  have hstable : (prefixWord ++ tailWord_221181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221181).length < 2 ^ (prefixWord ++ tailWord_221181).sum := by decide
  have hdescent : baseEnd_221181 < baseStart_221181 := by decide
  rcases family_descends (prefixWord ++ tailWord_221181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221190 : List Nat := [6, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2]
def baseStart_221190 : Nat := 118140960795 + 221190 * 2 ^ 59
def prefixEnd_221190 : Nat := 4983230072969 + 3 ^ 40 * 221190 * 2
def baseEnd_221190 : Nat := 113576785968094826807773

theorem tailTrace_221190 : CollatzResearch.WordTrace tailWord_221190 prefixEnd_221190 113576785968094826807773 := by
  unfold tailWord_221190
  simp only [CollatzResearch.WordTrace]
  refine ⟨252108189646058784049657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5378308045782587393059349 252108189646058784049657)
  ·
    refine ⟨189081142234544088037243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252108189646058784049657 189081142234544088037243)
    ·
      refine ⟨283621713351816132055865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189081142234544088037243 283621713351816132055865)
      ·
        refine ⟨212716285013862099041899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283621713351816132055865 212716285013862099041899)
        ·
          refine ⟨319074427520793148562849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212716285013862099041899 319074427520793148562849)
          ·
            refine ⟨239305820640594861422137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319074427520793148562849 239305820640594861422137)
            ·
              refine ⟨179479365480446146066603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239305820640594861422137 179479365480446146066603)
              ·
                refine ⟨269219048220669219099905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179479365480446146066603 269219048220669219099905)
                ·
                  refine ⟨201914286165501914324929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 269219048220669219099905 201914286165501914324929)
                  ·
                    refine ⟨151435714624126435743697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 201914286165501914324929 151435714624126435743697)
                    ·
                      refine ⟨113576785968094826807773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 151435714624126435743697 113576785968094826807773)
                      ·
                        rfl

theorem cell23_221190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_221190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221190 prefixEnd_221190 := by exact prefixLift 221190
  have htrace : WordTrace (prefixWord ++ tailWord_221190) baseStart_221190 baseEnd_221190 := by
    simpa [prefixWord, tailWord_221190, baseEnd_221190] using wordTrace_append hprefix tailTrace_221190
  have hstable : (prefixWord ++ tailWord_221190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221190).length < 2 ^ (prefixWord ++ tailWord_221190).sum := by decide
  have hdescent : baseEnd_221190 < baseStart_221190 := by decide
  rcases family_descends (prefixWord ++ tailWord_221190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221268 : List Nat := [2, 4, 1, 1, 1, 1, 1, 6, 1, 1, 4]
def baseStart_221268 : Nat := 118140960795 + 221268 * 2 ^ 59
def prefixEnd_221268 : Nat := 4983230072969 + 3 ^ 40 * 221268 * 2
def baseEnd_221268 : Nat := 113616837459145521632413

theorem tailTrace_221268 : CollatzResearch.WordTrace tailWord_221268 prefixEnd_221268 113616837459145521632413 := by
  unfold tailWord_221268
  simp only [CollatzResearch.WordTrace]
  refine ⟨4035153481195650205464229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5380204641594200273952305 4035153481195650205464229)
  ·
    refine ⟨756591277724184413524543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4035153481195650205464229 756591277724184413524543)
    ·
      refine ⟨1134886916586276620286815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 756591277724184413524543 1134886916586276620286815)
      ·
        refine ⟨1702330374879414930430223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1134886916586276620286815 1702330374879414930430223)
        ·
          refine ⟨2553495562319122395645335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1702330374879414930430223 2553495562319122395645335)
          ·
            refine ⟨3830243343478683593468003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2553495562319122395645335 3830243343478683593468003)
            ·
              refine ⟨5745365015218025390202005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3830243343478683593468003 5745365015218025390202005)
              ·
                refine ⟨269313985088344940165719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5745365015218025390202005 269313985088344940165719)
                ·
                  refine ⟨403970977632517410248579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 269313985088344940165719 403970977632517410248579)
                  ·
                    refine ⟨605956466448776115372869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 403970977632517410248579 605956466448776115372869)
                    ·
                      refine ⟨113616837459145521632413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 605956466448776115372869 113616837459145521632413)
                      ·
                        rfl

theorem cell23_221268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_221268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221268 prefixEnd_221268 := by exact prefixLift 221268
  have htrace : WordTrace (prefixWord ++ tailWord_221268) baseStart_221268 baseEnd_221268 := by
    simpa [prefixWord, tailWord_221268, baseEnd_221268] using wordTrace_append hprefix tailTrace_221268
  have hstable : (prefixWord ++ tailWord_221268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221268).length < 2 ^ (prefixWord ++ tailWord_221268).sum := by decide
  have hdescent : baseEnd_221268 < baseStart_221268 := by decide
  rcases family_descends (prefixWord ++ tailWord_221268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221285 : List Nat := [1, 3, 1, 3, 2, 2, 4, 1, 1, 1, 4]
def baseStart_221285 : Nat := 118140960795 + 221285 * 2 ^ 59
def prefixEnd_221285 : Nat := 4983230072969 + 3 ^ 40 * 221285 * 2
def baseEnd_221285 : Nat := 113625566630271955119835

theorem tailTrace_221285 : CollatzResearch.WordTrace tailWord_221285 prefixEnd_221285 113625566630271955119835 := by
  unfold tailWord_221285
  simp only [CollatzResearch.WordTrace]
  refine ⟨8070927003329712314297309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5380618002219808209531539 8070927003329712314297309)
  ·
    refine ⟨3026597626248642117861491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8070927003329712314297309 3026597626248642117861491)
    ·
      refine ⟨4539896439372963176792237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3026597626248642117861491 4539896439372963176792237)
      ·
        refine ⟨1702461164764861191297089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4539896439372963176792237 1702461164764861191297089)
        ·
          refine ⟨1276845873573645893472817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1702461164764861191297089 1276845873573645893472817)
          ·
            refine ⟨957634405180234420104613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1276845873573645893472817 957634405180234420104613)
            ·
              refine ⟨179556450971293953769615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 957634405180234420104613 179556450971293953769615)
              ·
                refine ⟨269334676456940930654423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179556450971293953769615 269334676456940930654423)
                ·
                  refine ⟨404002014685411395981635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 269334676456940930654423 404002014685411395981635)
                  ·
                    refine ⟨606003022028117093972453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 404002014685411395981635 606003022028117093972453)
                    ·
                      refine ⟨113625566630271955119835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 606003022028117093972453 113625566630271955119835)
                      ·
                        rfl

theorem cell23_221285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_221285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221285 prefixEnd_221285 := by exact prefixLift 221285
  have htrace : WordTrace (prefixWord ++ tailWord_221285) baseStart_221285 baseEnd_221285 := by
    simpa [prefixWord, tailWord_221285, baseEnd_221285] using wordTrace_append hprefix tailTrace_221285
  have hstable : (prefixWord ++ tailWord_221285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221285).length < 2 ^ (prefixWord ++ tailWord_221285).sum := by decide
  have hdescent : baseEnd_221285 < baseStart_221285 := by decide
  rcases family_descends (prefixWord ++ tailWord_221285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221295 : List Nat := [1, 1, 2, 1, 3, 6, 1, 2, 2, 4]
def baseStart_221295 : Nat := 118140960795 + 221295 * 2 ^ 59
def prefixEnd_221295 : Nat := 4983230072969 + 3 ^ 40 * 221295 * 2
def baseEnd_221295 : Nat := 37876900478938971998263

theorem tailTrace_221295 : CollatzResearch.WordTrace tailWord_221295 prefixEnd_221295 37876900478938971998263 := by
  unfold tailWord_221295
  simp only [CollatzResearch.WordTrace]
  refine ⟨8071291733293484022161339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5380861155528989348107559 8071291733293484022161339)
  ·
    refine ⟨12106937599940226033242009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8071291733293484022161339 12106937599940226033242009)
    ·
      refine ⟨9080203199955169524931507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12106937599940226033242009 9080203199955169524931507)
      ·
        refine ⟨13620304799932754287397261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9080203199955169524931507 13620304799932754287397261)
        ·
          refine ⟨5107614299974782857773973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13620304799932754287397261 5107614299974782857773973)
          ·
            refine ⟨239419420311317946458155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5107614299974782857773973 239419420311317946458155)
            ·
              refine ⟨359129130466976919687233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239419420311317946458155 359129130466976919687233)
              ·
                refine ⟨269346847850232689765425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359129130466976919687233 269346847850232689765425)
                ·
                  refine ⟨202010135887674517324069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 269346847850232689765425 202010135887674517324069)
                  ·
                    refine ⟨37876900478938971998263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 202010135887674517324069 37876900478938971998263)
                    ·
                      rfl

theorem cell23_221295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2, 4].length) (baseStart_221295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221295 prefixEnd_221295 := by exact prefixLift 221295
  have htrace : WordTrace (prefixWord ++ tailWord_221295) baseStart_221295 baseEnd_221295 := by
    simpa [prefixWord, tailWord_221295, baseEnd_221295] using wordTrace_append hprefix tailTrace_221295
  have hstable : (prefixWord ++ tailWord_221295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221295).length < 2 ^ (prefixWord ++ tailWord_221295).sum := by decide
  have hdescent : baseEnd_221295 < baseStart_221295 := by decide
  rcases family_descends (prefixWord ++ tailWord_221295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221302 : List Nat := [5, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2]
def baseStart_221302 : Nat := 118140960795 + 221302 * 2 ^ 59
def prefixEnd_221302 : Nat := 4983230072969 + 3 ^ 40 * 221302 * 2
def baseEnd_221302 : Nat := 113634295801398388607257

theorem tailTrace_221302 : CollatzResearch.WordTrace tailWord_221302 prefixEnd_221302 113634295801398388607257 := by
  unfold tailWord_221302
  simp only [CollatzResearch.WordTrace]
  refine ⟨504471690266757763604135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5381031362845416145110773 504471690266757763604135)
  ·
    refine ⟨756707535400136645406203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 504471690266757763604135 756707535400136645406203)
    ·
      refine ⟨1135061303100204968109305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 756707535400136645406203 1135061303100204968109305)
      ·
        refine ⟨851295977325153726081979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1135061303100204968109305 851295977325153726081979)
        ·
          refine ⟨1276943965987730589122969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851295977325153726081979 1276943965987730589122969)
          ·
            refine ⟨957707974490797941842227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1276943965987730589122969 957707974490797941842227)
            ·
              refine ⟨1436561961736196912763341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 957707974490797941842227 1436561961736196912763341)
              ·
                refine ⟨538710735651073842286253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1436561961736196912763341 538710735651073842286253)
                ·
                  refine ⟨202016525869152690857345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 538710735651073842286253 202016525869152690857345)
                  ·
                    refine ⟨151512394401864518143009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 202016525869152690857345 151512394401864518143009)
                    ·
                      refine ⟨113634295801398388607257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 151512394401864518143009 113634295801398388607257)
                      ·
                        rfl

theorem cell23_221302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_221302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221302 prefixEnd_221302 := by exact prefixLift 221302
  have htrace : WordTrace (prefixWord ++ tailWord_221302) baseStart_221302 baseEnd_221302 := by
    simpa [prefixWord, tailWord_221302, baseEnd_221302] using wordTrace_append hprefix tailTrace_221302
  have hstable : (prefixWord ++ tailWord_221302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221302).length < 2 ^ (prefixWord ++ tailWord_221302).sum := by decide
  have hdescent : baseEnd_221302 < baseStart_221302 := by decide
  rcases family_descends (prefixWord ++ tailWord_221302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221336 : List Nat := [2, 1, 2, 4, 3, 2, 1, 3, 1, 2, 2]
def baseStart_221336 : Nat := 118140960795 + 221336 * 2 ^ 59
def prefixEnd_221336 : Nat := 4983230072969 + 3 ^ 40 * 221336 * 2
def baseEnd_221336 : Nat := 113651754143651255582101

theorem tailTrace_221336 : CollatzResearch.WordTrace tailWord_221336 prefixEnd_221336 113651754143651255582101 := by
  unfold tailWord_221336
  simp only [CollatzResearch.WordTrace]
  refine ⟨4036393563072474012201931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5381858084096632016269241 4036393563072474012201931)
  ·
    refine ⟨6054590344608711018302897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4036393563072474012201931 6054590344608711018302897)
    ·
      refine ⟨4540942758456533263727173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6054590344608711018302897 4540942758456533263727173)
      ·
        refine ⟨851426767210599986948845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4540942758456533263727173 851426767210599986948845)
        ·
          refine ⟨319285037703974995105817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 851426767210599986948845 319285037703974995105817)
          ·
            refine ⟨239463778277981246329363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319285037703974995105817 239463778277981246329363)
            ·
              refine ⟨359195667416971869494045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239463778277981246329363 359195667416971869494045)
              ·
                refine ⟨134698375281364451060267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 359195667416971869494045 134698375281364451060267)
                ·
                  refine ⟨202047562922046676590401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134698375281364451060267 202047562922046676590401)
                  ·
                    refine ⟨151535672191535007442801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 202047562922046676590401 151535672191535007442801)
                    ·
                      refine ⟨113651754143651255582101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 151535672191535007442801 113651754143651255582101)
                      ·
                        rfl

theorem cell23_221336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_221336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221336 prefixEnd_221336 := by exact prefixLift 221336
  have htrace : WordTrace (prefixWord ++ tailWord_221336) baseStart_221336 baseEnd_221336 := by
    simpa [prefixWord, tailWord_221336, baseEnd_221336] using wordTrace_append hprefix tailTrace_221336
  have hstable : (prefixWord ++ tailWord_221336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221336).length < 2 ^ (prefixWord ++ tailWord_221336).sum := by decide
  have hdescent : baseEnd_221336 < baseStart_221336 := by decide
  rcases family_descends (prefixWord ++ tailWord_221336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221371 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 4]
def baseStart_221371 : Nat := 118140960795 + 221371 * 2 ^ 59
def prefixEnd_221371 : Nat := 4983230072969 + 3 ^ 40 * 221371 * 2
def baseEnd_221371 : Nat := 113669725966558618644439

theorem tailTrace_221371 : CollatzResearch.WordTrace tailWord_221371 prefixEnd_221371 113669725966558618644439 := by
  unfold tailWord_221371
  simp only [CollatzResearch.WordTrace]
  refine ⟨8074063681018149001927967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5382709120678766001285311 8074063681018149001927967)
  ·
    refine ⟨12111095521527223502891951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8074063681018149001927967 12111095521527223502891951)
    ·
      refine ⟨18166643282290835254337927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12111095521527223502891951 18166643282290835254337927)
      ·
        refine ⟨27249964923436252881506891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18166643282290835254337927 27249964923436252881506891)
        ·
          refine ⟨40874947385154379322260337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27249964923436252881506891 40874947385154379322260337)
          ·
            refine ⟨30656210538865784491695253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40874947385154379322260337 30656210538865784491695253)
            ·
              refine ⟨1437009869009333648048215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30656210538865784491695253 1437009869009333648048215)
              ·
                refine ⟨2155514803514000472072323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1437009869009333648048215 2155514803514000472072323)
                ·
                  refine ⟨3233272205271000708108485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2155514803514000472072323 3233272205271000708108485)
                  ·
                    refine ⟨606238538488312632770341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3233272205271000708108485 606238538488312632770341)
                    ·
                      refine ⟨113669725966558618644439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 606238538488312632770341 113669725966558618644439)
                      ·
                        rfl

theorem cell23_221371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 4].length) (baseStart_221371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221371 prefixEnd_221371 := by exact prefixLift 221371
  have htrace : WordTrace (prefixWord ++ tailWord_221371) baseStart_221371 baseEnd_221371 := by
    simpa [prefixWord, tailWord_221371, baseEnd_221371] using wordTrace_append hprefix tailTrace_221371
  have hstable : (prefixWord ++ tailWord_221371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221371).length < 2 ^ (prefixWord ++ tailWord_221371).sum := by decide
  have hdescent : baseEnd_221371 < baseStart_221371 := by decide
  rcases family_descends (prefixWord ++ tailWord_221371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221381 : List Nat := [1, 3, 1, 1, 1, 1, 4, 4, 7]
def baseStart_221381 : Nat := 118140960795 + 221381 * 2 ^ 59
def prefixEnd_221381 : Nat := 4983230072969 + 3 ^ 40 * 221381 * 2
def baseEnd_221381 : Nat := 12630540085900397724377

theorem tailTrace_221381 : CollatzResearch.WordTrace tailWord_221381 prefixEnd_221381 12630540085900397724377 := by
  unfold tailWord_221381
  simp only [CollatzResearch.WordTrace]
  refine ⟨8074428410981920709791997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5382952273987947139861331 8074428410981920709791997)
  ·
    refine ⟨3027910654118220266171999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8074428410981920709791997 3027910654118220266171999)
    ·
      refine ⟨4541865981177330399257999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3027910654118220266171999 4541865981177330399257999)
      ·
        refine ⟨6812798971765995598886999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4541865981177330399257999 6812798971765995598886999)
        ·
          refine ⟨10219198457648993398330499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6812798971765995598886999 10219198457648993398330499)
          ·
            refine ⟨15328797686473490097495749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10219198457648993398330499 15328797686473490097495749)
            ·
              refine ⟨2874149566213779393280453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15328797686473490097495749 2874149566213779393280453)
              ·
                refine ⟨538903043665083636240085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2874149566213779393280453 538903043665083636240085)
                ·
                  refine ⟨12630540085900397724377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 538903043665083636240085 12630540085900397724377)
                  ·
                    rfl

theorem cell23_221381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 7].length) (baseStart_221381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221381 prefixEnd_221381 := by exact prefixLift 221381
  have htrace : WordTrace (prefixWord ++ tailWord_221381) baseStart_221381 baseEnd_221381 := by
    simpa [prefixWord, tailWord_221381, baseEnd_221381] using wordTrace_append hprefix tailTrace_221381
  have hstable : (prefixWord ++ tailWord_221381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221381).length < 2 ^ (prefixWord ++ tailWord_221381).sum := by decide
  have hdescent : baseEnd_221381 < baseStart_221381 := by decide
  rcases family_descends (prefixWord ++ tailWord_221381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221408 : List Nat := [2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 3]
def baseStart_221408 : Nat := 118140960795 + 221408 * 2 ^ 59
def prefixEnd_221408 : Nat := 4983230072969 + 3 ^ 40 * 221408 * 2
def baseEnd_221408 : Nat := 113688724750774973881769

theorem tailTrace_221408 : CollatzResearch.WordTrace tailWord_221408 prefixEnd_221408 113688724750774973881769 := by
  unfold tailWord_221408
  simp only [CollatzResearch.WordTrace]
  refine ⟨4037706590942052160512439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5383608787922736214016585 4037706590942052160512439)
  ·
    refine ⟨6056559886413078240768659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4037706590942052160512439 6056559886413078240768659)
    ·
      refine ⟨9084839829619617361152989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6056559886413078240768659 9084839829619617361152989)
      ·
        refine ⟨3406814936107356510432371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9084839829619617361152989 3406814936107356510432371)
        ·
          refine ⟨5110222404161034765648557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3406814936107356510432371 5110222404161034765648557)
          ·
            refine ⟨1916333401560388037118209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5110222404161034765648557 1916333401560388037118209)
            ·
              refine ⟨1437250051170291027838657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1916333401560388037118209 1437250051170291027838657)
              ·
                refine ⟨1077937538377718270878993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1437250051170291027838657 1077937538377718270878993)
                ·
                  refine ⟨808453153783288703159245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1077937538377718270878993 808453153783288703159245)
                  ·
                    refine ⟨303169932668733263684717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 808453153783288703159245 303169932668733263684717)
                    ·
                      refine ⟨113688724750774973881769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 303169932668733263684717 113688724750774973881769)
                      ·
                        rfl

theorem cell23_221408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_221408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221408 prefixEnd_221408 := by exact prefixLift 221408
  have htrace : WordTrace (prefixWord ++ tailWord_221408) baseStart_221408 baseEnd_221408 := by
    simpa [prefixWord, tailWord_221408, baseEnd_221408] using wordTrace_append hprefix tailTrace_221408
  have hstable : (prefixWord ++ tailWord_221408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221408).length < 2 ^ (prefixWord ++ tailWord_221408).sum := by decide
  have hdescent : baseEnd_221408 < baseStart_221408 := by decide
  rcases family_descends (prefixWord ++ tailWord_221408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221475 : List Nat := [1, 1, 1, 4, 2, 2, 4, 1, 3, 4]
def baseStart_221475 : Nat := 118140960795 + 221475 * 2 ^ 59
def prefixEnd_221475 : Nat := 4983230072969 + 3 ^ 40 * 221475 * 2
def baseEnd_221475 : Nat := 37907709318208737247987

theorem tailTrace_221475 : CollatzResearch.WordTrace tailWord_221475 prefixEnd_221475 37907709318208737247987 := by
  unfold tailWord_221475
  simp only [CollatzResearch.WordTrace]
  refine ⟨8077856872641374763713879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5385237915094249842475919 8077856872641374763713879)
  ·
    refine ⟨12116785308962062145570819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8077856872641374763713879 12116785308962062145570819)
    ·
      refine ⟨18175177963443093218356229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12116785308962062145570819 18175177963443093218356229)
      ·
        refine ⟨3407845868145579978441793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18175177963443093218356229 3407845868145579978441793)
        ·
          refine ⟨2555884401109184983831345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3407845868145579978441793 2555884401109184983831345)
          ·
            refine ⟨1916913300831888737873509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2555884401109184983831345 1916913300831888737873509)
            ·
              refine ⟨359421243905979138351283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1916913300831888737873509 359421243905979138351283)
              ·
                refine ⟨539131865858968707526925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359421243905979138351283 539131865858968707526925)
                ·
                  refine ⟨202174449697113265322597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 539131865858968707526925 202174449697113265322597)
                  ·
                    refine ⟨37907709318208737247987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 202174449697113265322597 37907709318208737247987)
                    ·
                      rfl

theorem cell23_221475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3, 4].length) (baseStart_221475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221475 prefixEnd_221475 := by exact prefixLift 221475
  have htrace : WordTrace (prefixWord ++ tailWord_221475) baseStart_221475 baseEnd_221475 := by
    simpa [prefixWord, tailWord_221475, baseEnd_221475] using wordTrace_append hprefix tailTrace_221475
  have hstable : (prefixWord ++ tailWord_221475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221475).length < 2 ^ (prefixWord ++ tailWord_221475).sum := by decide
  have hdescent : baseEnd_221475 < baseStart_221475 := by decide
  rcases family_descends (prefixWord ++ tailWord_221475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221492 : List Nat := [2, 5, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_221492 : Nat := 118140960795 + 221492 * 2 ^ 59
def prefixEnd_221492 : Nat := 4983230072969 + 3 ^ 40 * 221492 * 2
def baseEnd_221492 : Nat := 37910619041917548410461

theorem tailTrace_221492 : CollatzResearch.WordTrace tailWord_221492 prefixEnd_221492 37910619041917548410461 := by
  unfold tailWord_221492
  simp only [CollatzResearch.WordTrace]
  refine ⟨4039238456789893333541365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5385651275719857778055153 4039238456789893333541365)
  ·
    refine ⟨378678605324052500019503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4039238456789893333541365 378678605324052500019503)
    ·
      refine ⟨568017907986078750029255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378678605324052500019503 568017907986078750029255)
      ·
        refine ⟨852026861979118125043883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568017907986078750029255 852026861979118125043883)
        ·
          refine ⟨1278040292968677187565825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 852026861979118125043883 1278040292968677187565825)
          ·
            refine ⟨958530219726507890674369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1278040292968677187565825 958530219726507890674369)
            ·
              refine ⟨718897664794880918005777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 958530219726507890674369 718897664794880918005777)
              ·
                refine ⟨539173248596160688504333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 718897664794880918005777 539173248596160688504333)
                ·
                  refine ⟨202189968223560258189125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 539173248596160688504333 202189968223560258189125)
                  ·
                    refine ⟨37910619041917548410461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 202189968223560258189125 37910619041917548410461)
                    ·
                      rfl

theorem cell23_221492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_221492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221492 prefixEnd_221492 := by exact prefixLift 221492
  have htrace : WordTrace (prefixWord ++ tailWord_221492) baseStart_221492 baseEnd_221492 := by
    simpa [prefixWord, tailWord_221492, baseEnd_221492] using wordTrace_append hprefix tailTrace_221492
  have hstable : (prefixWord ++ tailWord_221492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221492).length < 2 ^ (prefixWord ++ tailWord_221492).sum := by decide
  have hdescent : baseEnd_221492 < baseStart_221492 := by decide
  rcases family_descends (prefixWord ++ tailWord_221492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221552 : List Nat := [2, 1, 1, 1, 4, 5, 1, 2, 1, 5]
def baseStart_221552 : Nat := 118140960795 + 221552 * 2 ^ 59
def prefixEnd_221552 : Nat := 4983230072969 + 3 ^ 40 * 221552 * 2
def baseEnd_221552 : Nat := 37920888655007470160369

theorem tailTrace_221552 : CollatzResearch.WordTrace tailWord_221552 prefixEnd_221552 37920888655007470160369 := by
  unfold tailWord_221552
  simp only [CollatzResearch.WordTrace]
  refine ⟨4040332646681208457133455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5387110195574944609511273 4040332646681208457133455)
  ·
    refine ⟨6060498970021812685700183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4040332646681208457133455 6060498970021812685700183)
    ·
      refine ⟨9090748455032719028550275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6060498970021812685700183 9090748455032719028550275)
      ·
        refine ⟨13636122682549078542825413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9090748455032719028550275 13636122682549078542825413)
        ·
          refine ⟨2556773002977952226779765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13636122682549078542825413 2556773002977952226779765)
          ·
            refine ⟨239697469029183021260603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2556773002977952226779765 239697469029183021260603)
            ·
              refine ⟨359546203543774531890905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239697469029183021260603 359546203543774531890905)
              ·
                refine ⟨269659652657830898918179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359546203543774531890905 269659652657830898918179)
                ·
                  refine ⟨404489478986746348377269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 269659652657830898918179 404489478986746348377269)
                  ·
                    refine ⟨37920888655007470160369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 404489478986746348377269 37920888655007470160369)
                    ·
                      rfl

theorem cell23_221552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 1, 5].length) (baseStart_221552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221552 prefixEnd_221552 := by exact prefixLift 221552
  have htrace : WordTrace (prefixWord ++ tailWord_221552) baseStart_221552 baseEnd_221552 := by
    simpa [prefixWord, tailWord_221552, baseEnd_221552] using wordTrace_append hprefix tailTrace_221552
  have hstable : (prefixWord ++ tailWord_221552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221552).length < 2 ^ (prefixWord ++ tailWord_221552).sum := by decide
  have hdescent : baseEnd_221552 < baseStart_221552 := by decide
  rcases family_descends (prefixWord ++ tailWord_221552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221565 : List Nat := [1, 4, 1, 1, 2, 4, 1, 2, 1, 6]
def baseStart_221565 : Nat := 118140960795 + 221565 * 2 ^ 59
def prefixEnd_221565 : Nat := 4983230072969 + 3 ^ 40 * 221565 * 2
def baseEnd_221565 : Nat := 37923113737843619872849

theorem tailTrace_221565 : CollatzResearch.WordTrace tailWord_221565 prefixEnd_221565 37923113737843619872849 := by
  unfold tailWord_221565
  simp only [CollatzResearch.WordTrace]
  refine ⟨8081139442315320134490149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5387426294876880089660099 8081139442315320134490149)
  ·
    refine ⟨1515213645434122525216903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8081139442315320134490149 1515213645434122525216903)
    ·
      refine ⟨2272820468151183787825355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1515213645434122525216903 2272820468151183787825355)
      ·
        refine ⟨3409230702226775681738033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2272820468151183787825355 3409230702226775681738033)
        ·
          refine ⟨2556923026670081761303525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3409230702226775681738033 2556923026670081761303525)
          ·
            refine ⟨479423067500640330244411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2556923026670081761303525 479423067500640330244411)
            ·
              refine ⟨719134601250960495366617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479423067500640330244411 719134601250960495366617)
              ·
                refine ⟨539350950938220371524963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 719134601250960495366617 539350950938220371524963)
                ·
                  refine ⟨809026426407330557287445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 539350950938220371524963 809026426407330557287445)
                  ·
                    refine ⟨37923113737843619872849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 809026426407330557287445 37923113737843619872849)
                    ·
                      rfl

theorem cell23_221565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_221565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221565 prefixEnd_221565 := by exact prefixLift 221565
  have htrace : WordTrace (prefixWord ++ tailWord_221565) baseStart_221565 baseEnd_221565 := by
    simpa [prefixWord, tailWord_221565, baseEnd_221565] using wordTrace_append hprefix tailTrace_221565
  have hstable : (prefixWord ++ tailWord_221565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221565).length < 2 ^ (prefixWord ++ tailWord_221565).sum := by decide
  have hdescent : baseEnd_221565 < baseStart_221565 := by decide
  rcases family_descends (prefixWord ++ tailWord_221565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221569 : List Nat := [1, 2, 4, 3, 1, 2, 3, 1, 1, 5]
def baseStart_221569 : Nat := 118140960795 + 221569 * 2 ^ 59
def prefixEnd_221569 : Nat := 4983230072969 + 3 ^ 40 * 221569 * 2
def baseEnd_221569 : Nat := 37923798378716281322843

theorem tailTrace_221569 : CollatzResearch.WordTrace tailWord_221569 prefixEnd_221569 37923798378716281322843 := by
  unfold tailWord_221569
  simp only [CollatzResearch.WordTrace]
  refine ⟨8081285334300828817635761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5387523556200552545090507 8081285334300828817635761)
  ·
    refine ⟨6060964000725621613226821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8081285334300828817635761 6060964000725621613226821)
    ·
      refine ⟨1136430750136054052480029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6060964000725621613226821 1136430750136054052480029)
      ·
        refine ⟨426161531301020269680011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1136430750136054052480029 426161531301020269680011)
        ·
          refine ⟨639242296951530404520017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426161531301020269680011 639242296951530404520017)
          ·
            refine ⟨479431722713647803390013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 639242296951530404520017 479431722713647803390013)
            ·
              refine ⟨179786896017617926271255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 479431722713647803390013 179786896017617926271255)
              ·
                refine ⟨269680344026426889406883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179786896017617926271255 269680344026426889406883)
                ·
                  refine ⟨404520516039640334110325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 269680344026426889406883 404520516039640334110325)
                  ·
                    refine ⟨37923798378716281322843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 404520516039640334110325 37923798378716281322843)
                    ·
                      rfl

theorem cell23_221569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_221569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221569 prefixEnd_221569 := by exact prefixLift 221569
  have htrace : WordTrace (prefixWord ++ tailWord_221569) baseStart_221569 baseEnd_221569 := by
    simpa [prefixWord, tailWord_221569, baseEnd_221569] using wordTrace_append hprefix tailTrace_221569
  have hstable : (prefixWord ++ tailWord_221569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221569).length < 2 ^ (prefixWord ++ tailWord_221569).sum := by decide
  have hdescent : baseEnd_221569 < baseStart_221569 := by decide
  rcases family_descends (prefixWord ++ tailWord_221569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221592 : List Nat := [2, 1, 2, 5, 1, 1, 1, 2, 3, 2, 3]
def baseStart_221592 : Nat := 118140960795 + 221592 * 2 ^ 59
def prefixEnd_221592 : Nat := 4983230072969 + 3 ^ 40 * 221592 * 2
def baseEnd_221592 : Nat := 113783205191202253980923

theorem tailTrace_221592 : CollatzResearch.WordTrace tailWord_221592 prefixEnd_221592 113783205191202253980923 := by
  unfold tailWord_221592
  simp only [CollatzResearch.WordTrace]
  refine ⟨4041062106608751872861515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5388082808811669163815353 4041062106608751872861515)
  ·
    refine ⟨6061593159913127809292273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4041062106608751872861515 6061593159913127809292273)
    ·
      refine ⟨4546194869934845856969205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6061593159913127809292273 4546194869934845856969205)
      ·
        refine ⟨426205769056391799090863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4546194869934845856969205 426205769056391799090863)
        ·
          refine ⟨639308653584587698636295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426205769056391799090863 639308653584587698636295)
          ·
            refine ⟨958962980376881547954443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 639308653584587698636295 958962980376881547954443)
            ·
              refine ⟨1438444470565322321931665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 958962980376881547954443 1438444470565322321931665)
              ·
                refine ⟨1078833352923991741448749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1438444470565322321931665 1078833352923991741448749)
                ·
                  refine ⟨404562507346496903043281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1078833352923991741448749 404562507346496903043281)
                  ·
                    refine ⟨303421880509872677282461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 404562507346496903043281 303421880509872677282461)
                    ·
                      refine ⟨113783205191202253980923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 303421880509872677282461 113783205191202253980923)
                      ·
                        rfl

theorem cell23_221592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_221592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221592 prefixEnd_221592 := by exact prefixLift 221592
  have htrace : WordTrace (prefixWord ++ tailWord_221592) baseStart_221592 baseEnd_221592 := by
    simpa [prefixWord, tailWord_221592, baseEnd_221592] using wordTrace_append hprefix tailTrace_221592
  have hstable : (prefixWord ++ tailWord_221592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221592).length < 2 ^ (prefixWord ++ tailWord_221592).sum := by decide
  have hdescent : baseEnd_221592 < baseStart_221592 := by decide
  rcases family_descends (prefixWord ++ tailWord_221592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221602 : List Nat := [3, 3, 1, 2, 1, 1, 4, 1, 1, 2, 4]
def baseStart_221602 : Nat := 118140960795 + 221602 * 2 ^ 59
def prefixEnd_221602 : Nat := 4983230072969 + 3 ^ 40 * 221602 * 2
def baseEnd_221602 : Nat := 113788339997747214855877

theorem tailTrace_221602 : CollatzResearch.WordTrace tailWord_221602 prefixEnd_221602 113788339997747214855877 := by
  unfold tailWord_221602
  simp only [CollatzResearch.WordTrace]
  refine ⟨2020622235795318863396765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5388325962120850302391373 2020622235795318863396765)
  ·
    refine ⟨757733338423244573773787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2020622235795318863396765 757733338423244573773787)
    ·
      refine ⟨1136600007634866860660681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 757733338423244573773787 1136600007634866860660681)
      ·
        refine ⟨852450005726150145495511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1136600007634866860660681 852450005726150145495511)
        ·
          refine ⟨1278675008589225218243267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 852450005726150145495511 1278675008589225218243267)
          ·
            refine ⟨1918012512883837827364901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1278675008589225218243267 1918012512883837827364901)
            ·
              refine ⟨359627346165719592630919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1918012512883837827364901 359627346165719592630919)
              ·
                refine ⟨539441019248579388946379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359627346165719592630919 539441019248579388946379)
                ·
                  refine ⟨809161528872869083419569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 539441019248579388946379 809161528872869083419569)
                  ·
                    refine ⟨606871146654651812564677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 809161528872869083419569 606871146654651812564677)
                    ·
                      refine ⟨113788339997747214855877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 606871146654651812564677 113788339997747214855877)
                      ·
                        rfl

theorem cell23_221602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_221602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221602 prefixEnd_221602 := by exact prefixLift 221602
  have htrace : WordTrace (prefixWord ++ tailWord_221602) baseStart_221602 baseEnd_221602 := by
    simpa [prefixWord, tailWord_221602, baseEnd_221602] using wordTrace_append hprefix tailTrace_221602
  have hstable : (prefixWord ++ tailWord_221602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221602).length < 2 ^ (prefixWord ++ tailWord_221602).sum := by decide
  have hdescent : baseEnd_221602 < baseStart_221602 := by decide
  rcases family_descends (prefixWord ++ tailWord_221602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221610 : List Nat := [3, 1, 6, 1, 1, 2, 1, 1, 2, 3, 2]
def baseStart_221610 : Nat := 118140960795 + 221610 * 2 ^ 59
def prefixEnd_221610 : Nat := 4983230072969 + 3 ^ 40 * 221610 * 2
def baseEnd_221610 : Nat := 113792447842983183555841

theorem tailTrace_221610 : CollatzResearch.WordTrace tailWord_221610 prefixEnd_221610 113792447842983183555841 := by
  unfold tailWord_221610
  simp only [CollatzResearch.WordTrace]
  refine ⟨2020695181788073204969571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5388520484768195213252189 2020695181788073204969571)
  ·
    refine ⟨3031042772682109807454357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2020695181788073204969571 3031042772682109807454357)
    ·
      refine ⟨142080129969473897224423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3031042772682109807454357 142080129969473897224423)
      ·
        refine ⟨213120194954210845836635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142080129969473897224423 213120194954210845836635)
        ·
          refine ⟨319680292431316268754953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213120194954210845836635 319680292431316268754953)
          ·
            refine ⟨239760219323487201566215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319680292431316268754953 239760219323487201566215)
            ·
              refine ⟨359640328985230802349323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239760219323487201566215 359640328985230802349323)
              ·
                refine ⟨539460493477846203523985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359640328985230802349323 539460493477846203523985)
                ·
                  refine ⟨404595370108384652642989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 539460493477846203523985 404595370108384652642989)
                  ·
                    refine ⟨151723263790644244741121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 404595370108384652642989 151723263790644244741121)
                    ·
                      refine ⟨113792447842983183555841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 151723263790644244741121 113792447842983183555841)
                      ·
                        rfl

theorem cell23_221610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_221610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221610 prefixEnd_221610 := by exact prefixLift 221610
  have htrace : WordTrace (prefixWord ++ tailWord_221610) baseStart_221610 baseEnd_221610 := by
    simpa [prefixWord, tailWord_221610, baseEnd_221610] using wordTrace_append hprefix tailTrace_221610
  have hstable : (prefixWord ++ tailWord_221610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221610).length < 2 ^ (prefixWord ++ tailWord_221610).sum := by decide
  have hdescent : baseEnd_221610 < baseStart_221610 := by decide
  rcases family_descends (prefixWord ++ tailWord_221610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221620 : List Nat := [2, 5, 2, 2, 2, 1, 2, 1, 1, 5]
def baseStart_221620 : Nat := 118140960795 + 221620 * 2 ^ 59
def prefixEnd_221620 : Nat := 4983230072969 + 3 ^ 40 * 221620 * 2
def baseEnd_221620 : Nat := 37932527549842714810265

theorem tailTrace_221620 : CollatzResearch.WordTrace tailWord_221620 prefixEnd_221620 37932527549842714810265 := by
  unfold tailWord_221620
  simp only [CollatzResearch.WordTrace]
  refine ⟨4041572728558032263871157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5388763638077376351828209 4041572728558032263871157)
  ·
    refine ⟨378897443302315524737921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4041572728558032263871157 378897443302315524737921)
    ·
      refine ⟨284173082476736643553441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378897443302315524737921 284173082476736643553441)
      ·
        refine ⟨213129811857552482665081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284173082476736643553441 213129811857552482665081)
        ·
          refine ⟨159847358893164361998811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213129811857552482665081 159847358893164361998811)
          ·
            refine ⟨239771038339746542998217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159847358893164361998811 239771038339746542998217)
            ·
              refine ⟨179828278754809907248663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239771038339746542998217 179828278754809907248663)
              ·
                refine ⟨269742418132214860872995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179828278754809907248663 269742418132214860872995)
                ·
                  refine ⟨404613627198322291309493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 269742418132214860872995 404613627198322291309493)
                  ·
                    refine ⟨37932527549842714810265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 404613627198322291309493 37932527549842714810265)
                    ·
                      rfl

theorem cell23_221620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_221620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221620 prefixEnd_221620 := by exact prefixLift 221620
  have htrace : WordTrace (prefixWord ++ tailWord_221620) baseStart_221620 baseEnd_221620 := by
    simpa [prefixWord, tailWord_221620, baseEnd_221620] using wordTrace_append hprefix tailTrace_221620
  have hstable : (prefixWord ++ tailWord_221620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221620).length < 2 ^ (prefixWord ++ tailWord_221620).sum := by decide
  have hdescent : baseEnd_221620 < baseStart_221620 := by decide
  rcases family_descends (prefixWord ++ tailWord_221620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221639 : List Nat := [1, 1, 4, 1, 1, 4, 3, 2, 2, 1, 3]
def baseStart_221639 : Nat := 118140960795 + 221639 * 2 ^ 59
def prefixEnd_221639 : Nat := 4983230072969 + 3 ^ 40 * 221639 * 2
def baseEnd_221639 : Nat := 113807338781963570093207

theorem tailTrace_221639 : CollatzResearch.WordTrace tailWord_221639 prefixEnd_221639 113807338781963570093207 := by
  unfold tailWord_221639
  simp only [CollatzResearch.WordTrace]
  refine ⟨8083838444047230772683971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5389225629364820515122647 8083838444047230772683971)
  ·
    refine ⟨12125757666070846159025957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8083838444047230772683971 12125757666070846159025957)
    ·
      refine ⟨2273579562388283654817367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12125757666070846159025957 2273579562388283654817367)
      ·
        refine ⟨3410369343582425482226051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2273579562388283654817367 3410369343582425482226051)
        ·
          refine ⟨5115554015373638223339077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3410369343582425482226051 5115554015373638223339077)
          ·
            refine ⟨959166377882557166876077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5115554015373638223339077 959166377882557166876077)
            ·
              refine ⟨359687391705958937578529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 959166377882557166876077 359687391705958937578529)
              ·
                refine ⟨269765543779469203183897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359687391705958937578529 269765543779469203183897)
                ·
                  refine ⟨202324157834601902387923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 269765543779469203183897 202324157834601902387923)
                  ·
                    refine ⟨303486236751902853581885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 202324157834601902387923 303486236751902853581885)
                    ·
                      refine ⟨113807338781963570093207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 303486236751902853581885 113807338781963570093207)
                      ·
                        rfl

theorem cell23_221639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_221639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221639 prefixEnd_221639 := by exact prefixLift 221639
  have htrace : WordTrace (prefixWord ++ tailWord_221639) baseStart_221639 baseEnd_221639 := by
    simpa [prefixWord, tailWord_221639, baseEnd_221639] using wordTrace_append hprefix tailTrace_221639
  have hstable : (prefixWord ++ tailWord_221639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221639).length < 2 ^ (prefixWord ++ tailWord_221639).sum := by decide
  have hdescent : baseEnd_221639 < baseStart_221639 := by decide
  rcases family_descends (prefixWord ++ tailWord_221639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221665 : List Nat := [1, 2, 3, 1, 2, 2, 2, 2, 2, 1, 5]
def baseStart_221665 : Nat := 118140960795 + 221665 * 2 ^ 59
def prefixEnd_221665 : Nat := 4983230072969 + 3 ^ 40 * 221665 * 2
def baseEnd_221665 : Nat := 113820689278980468368087

theorem tailTrace_221665 : CollatzResearch.WordTrace tailWord_221665 prefixEnd_221665 113820689278980468368087 := by
  unfold tailWord_221665
  simp only [CollatzResearch.WordTrace]
  refine ⟨8084786741953037213130449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5389857827968691475420299 8084786741953037213130449)
  ·
    refine ⟨6063590056464777909847837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8084786741953037213130449 6063590056464777909847837)
    ·
      refine ⟨2273846271174291716192939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6063590056464777909847837 2273846271174291716192939)
      ·
        refine ⟨3410769406761437574289409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2273846271174291716192939 3410769406761437574289409)
        ·
          refine ⟨2558077055071078180717057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3410769406761437574289409 2558077055071078180717057)
          ·
            refine ⟨1918557791303308635537793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2558077055071078180717057 1918557791303308635537793)
            ·
              refine ⟨1438918343477481476653345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1918557791303308635537793 1438918343477481476653345)
              ·
                refine ⟨1079188757608111107490009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1438918343477481476653345 1079188757608111107490009)
                ·
                  refine ⟨809391568206083330617507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1079188757608111107490009 809391568206083330617507)
                  ·
                    refine ⟨1214087352309124995926261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 809391568206083330617507 1214087352309124995926261)
                    ·
                      refine ⟨113820689278980468368087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1214087352309124995926261 113820689278980468368087)
                      ·
                        rfl

theorem cell23_221665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_221665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221665 prefixEnd_221665 := by exact prefixLift 221665
  have htrace : WordTrace (prefixWord ++ tailWord_221665) baseStart_221665 baseEnd_221665 := by
    simpa [prefixWord, tailWord_221665, baseEnd_221665] using wordTrace_append hprefix tailTrace_221665
  have hstable : (prefixWord ++ tailWord_221665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221665).length < 2 ^ (prefixWord ++ tailWord_221665).sum := by decide
  have hdescent : baseEnd_221665 < baseStart_221665 := by decide
  rcases family_descends (prefixWord ++ tailWord_221665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221715 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 4, 5]
def baseStart_221715 : Nat := 118140960795 + 221715 * 2 ^ 59
def prefixEnd_221715 : Nat := 4983230072969 + 3 ^ 40 * 221715 * 2
def baseEnd_221715 : Nat := 37948787770568424247619

theorem tailTrace_221715 : CollatzResearch.WordTrace tailWord_221715 prefixEnd_221715 37948787770568424247619 := by
  unfold tailWord_221715
  simp only [CollatzResearch.WordTrace]
  refine ⟨8086610391771895752450599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5391073594514597168300399 8086610391771895752450599)
  ·
    refine ⟨12129915587657843628675899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8086610391771895752450599 12129915587657843628675899)
    ·
      refine ⟨18194873381486765443013849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12129915587657843628675899 18194873381486765443013849)
      ·
        refine ⟨13646155036115074082260387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18194873381486765443013849 13646155036115074082260387)
        ·
          refine ⟨20469232554172611123390581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13646155036115074082260387 20469232554172611123390581)
          ·
            refine ⟨1918990551953682292817867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20469232554172611123390581 1918990551953682292817867)
            ·
              refine ⟨2878485827930523439226801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1918990551953682292817867 2878485827930523439226801)
              ·
                refine ⟨2158864370947892579420101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2878485827930523439226801 2158864370947892579420101)
                ·
                  refine ⟨404787069552729858641269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2158864370947892579420101 404787069552729858641269)
                  ·
                    refine ⟨37948787770568424247619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 404787069552729858641269 37948787770568424247619)
                    ·
                      rfl

theorem cell23_221715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 5].length) (baseStart_221715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221715 prefixEnd_221715 := by exact prefixLift 221715
  have htrace : WordTrace (prefixWord ++ tailWord_221715) baseStart_221715 baseEnd_221715 := by
    simpa [prefixWord, tailWord_221715, baseEnd_221715] using wordTrace_append hprefix tailTrace_221715
  have hstable : (prefixWord ++ tailWord_221715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221715).length < 2 ^ (prefixWord ++ tailWord_221715).sum := by decide
  have hdescent : baseEnd_221715 < baseStart_221715 := by decide
  rcases family_descends (prefixWord ++ tailWord_221715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221752 : List Nat := [2, 1, 2, 1, 4, 1, 1, 4, 2, 1, 4]
def baseStart_221752 : Nat := 118140960795 + 221752 * 2 ^ 59
def prefixEnd_221752 : Nat := 4983230072969 + 3 ^ 40 * 221752 * 2
def baseEnd_221752 : Nat := 113865362095921627980187

theorem tailTrace_221752 : CollatzResearch.WordTrace tailWord_221752 prefixEnd_221752 113865362095921627980187 := by
  unfold tailWord_221752
  simp only [CollatzResearch.WordTrace]
  refine ⟨4043979946318925535773755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5391973261758567381031673 4043979946318925535773755)
  ·
    refine ⟨6065969919478388303660633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4043979946318925535773755 6065969919478388303660633)
    ·
      refine ⟨4549477439608791227745475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6065969919478388303660633 4549477439608791227745475)
      ·
        refine ⟨6824216159413186841618213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4549477439608791227745475 6824216159413186841618213)
        ·
          refine ⟨1279540529889972532803415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6824216159413186841618213 1279540529889972532803415)
          ·
            refine ⟨1919310794834958799205123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279540529889972532803415 1919310794834958799205123)
            ·
              refine ⟨2878966192252438198807685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1919310794834958799205123 2878966192252438198807685)
              ·
                refine ⟨539806161047332162276441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2878966192252438198807685 539806161047332162276441)
                ·
                  refine ⟨404854620785499121707331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 539806161047332162276441 404854620785499121707331)
                  ·
                    refine ⟨607281931178248682560997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 404854620785499121707331 607281931178248682560997)
                    ·
                      refine ⟨113865362095921627980187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 607281931178248682560997 113865362095921627980187)
                      ·
                        rfl

theorem cell23_221752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_221752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221752 prefixEnd_221752 := by exact prefixLift 221752
  have htrace : WordTrace (prefixWord ++ tailWord_221752) baseStart_221752 baseEnd_221752 := by
    simpa [prefixWord, tailWord_221752, baseEnd_221752] using wordTrace_append hprefix tailTrace_221752
  have hstable : (prefixWord ++ tailWord_221752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221752).length < 2 ^ (prefixWord ++ tailWord_221752).sum := by decide
  have hdescent : baseEnd_221752 < baseStart_221752 := by decide
  rcases family_descends (prefixWord ++ tailWord_221752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221772 : List Nat := [2, 2, 1, 3, 1, 2, 2, 2, 1, 4, 3]
def baseStart_221772 : Nat := 118140960795 + 221772 * 2 ^ 59
def prefixEnd_221772 : Nat := 4983230072969 + 3 ^ 40 * 221772 * 2
def baseEnd_221772 : Nat := 113875631709011549730095

theorem tailTrace_221772 : CollatzResearch.WordTrace tailWord_221772 prefixEnd_221772 113875631709011549730095 := by
  unfold tailWord_221772
  simp only [CollatzResearch.WordTrace]
  refine ⟨4044344676282697243637785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5392459568376929658183713 4044344676282697243637785)
  ·
    refine ⟨3033258507212022932728339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4044344676282697243637785 3033258507212022932728339)
    ·
      refine ⟨4549887760818034399092509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3033258507212022932728339 4549887760818034399092509)
      ·
        refine ⟨1706207910306762899659691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4549887760818034399092509 1706207910306762899659691)
        ·
          refine ⟨2559311865460144349489537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1706207910306762899659691 2559311865460144349489537)
          ·
            refine ⟨1919483899095108262117153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2559311865460144349489537 1919483899095108262117153)
            ·
              refine ⟨1439612924321331196587865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1919483899095108262117153 1439612924321331196587865)
              ·
                refine ⟨1079709693240998397440899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1439612924321331196587865 1079709693240998397440899)
                ·
                  refine ⟨1619564539861497596161349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1079709693240998397440899 1619564539861497596161349)
                  ·
                    refine ⟨303668351224030799280253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1619564539861497596161349 303668351224030799280253)
                    ·
                      refine ⟨113875631709011549730095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 303668351224030799280253 113875631709011549730095)
                      ·
                        rfl

theorem cell23_221772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_221772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221772 prefixEnd_221772 := by exact prefixLift 221772
  have htrace : WordTrace (prefixWord ++ tailWord_221772) baseStart_221772 baseEnd_221772 := by
    simpa [prefixWord, tailWord_221772, baseEnd_221772] using wordTrace_append hprefix tailTrace_221772
  have hstable : (prefixWord ++ tailWord_221772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221772).length < 2 ^ (prefixWord ++ tailWord_221772).sum := by decide
  have hdescent : baseEnd_221772 < baseStart_221772 := by decide
  rcases family_descends (prefixWord ++ tailWord_221772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221796 : List Nat := [2, 3, 1, 1, 2, 2, 4, 3, 1, 4]
def baseStart_221796 : Nat := 118140960795 + 221796 * 2 ^ 59
def prefixEnd_221796 : Nat := 4983230072969 + 3 ^ 40 * 221796 * 2
def baseEnd_221796 : Nat := 37962651748239818609995

theorem tailTrace_221796 : CollatzResearch.WordTrace tailWord_221796 prefixEnd_221796 37962651748239818609995 := by
  unfold tailWord_221796
  simp only [CollatzResearch.WordTrace]
  refine ⟨4044782352239223293074621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5393043136318964390766161 4044782352239223293074621)
  ·
    refine ⟨1516793382089708734902983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4044782352239223293074621 1516793382089708734902983)
    ·
      refine ⟨2275190073134563102354475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1516793382089708734902983 2275190073134563102354475)
      ·
        refine ⟨3412785109701844653531713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2275190073134563102354475 3412785109701844653531713)
        ·
          refine ⟨2559588832276383490148785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3412785109701844653531713 2559588832276383490148785)
          ·
            refine ⟨1919691624207287617611589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2559588832276383490148785 1919691624207287617611589)
            ·
              refine ⟨359942179538866428302173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1919691624207287617611589 359942179538866428302173)
              ·
                refine ⟨134978317327074910613315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 359942179538866428302173 134978317327074910613315)
                ·
                  refine ⟨202467475990612365919973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134978317327074910613315 202467475990612365919973)
                  ·
                    refine ⟨37962651748239818609995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 202467475990612365919973 37962651748239818609995)
                    ·
                      rfl

theorem cell23_221796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_221796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221796 prefixEnd_221796 := by exact prefixLift 221796
  have htrace : WordTrace (prefixWord ++ tailWord_221796) baseStart_221796 baseEnd_221796 := by
    simpa [prefixWord, tailWord_221796, baseEnd_221796] using wordTrace_append hprefix tailTrace_221796
  have hstable : (prefixWord ++ tailWord_221796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221796).length < 2 ^ (prefixWord ++ tailWord_221796).sum := by decide
  have hdescent : baseEnd_221796 < baseStart_221796 := by decide
  rcases family_descends (prefixWord ++ tailWord_221796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221829 : List Nat := [1, 3, 1, 1, 4, 2, 1, 2, 1, 5, 2]
def baseStart_221829 : Nat := 118140960795 + 221829 * 2 ^ 59
def prefixEnd_221829 : Nat := 4983230072969 + 3 ^ 40 * 221829 * 2
def baseEnd_221829 : Nat := 113904900106317826717333

theorem tailTrace_221829 : CollatzResearch.WordTrace tailWord_221829 prefixEnd_221829 113904900106317826717333 := by
  unfold tailWord_221829
  simp only [CollatzResearch.WordTrace]
  refine ⟨8090768313358893222100541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5393845542239262148067027 8090768313358893222100541)
  ·
    refine ⟨3034038117509584958287703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8090768313358893222100541 3034038117509584958287703)
    ·
      refine ⟨4551057176264377437431555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3034038117509584958287703 4551057176264377437431555)
      ·
        refine ⟨6826585764396566156147333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4551057176264377437431555 6826585764396566156147333)
        ·
          refine ⟨1279984830824356154277625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6826585764396566156147333 1279984830824356154277625)
          ·
            refine ⟨959988623118267115708219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1279984830824356154277625 959988623118267115708219)
            ·
              refine ⟨1439982934677400673562329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 959988623118267115708219 1439982934677400673562329)
              ·
                refine ⟨1079987201008050505171747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1439982934677400673562329 1079987201008050505171747)
                ·
                  refine ⟨1619980801512075757757621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1079987201008050505171747 1619980801512075757757621)
                  ·
                    refine ⟨151873200141757102289777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1619980801512075757757621 151873200141757102289777)
                    ·
                      refine ⟨113904900106317826717333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 151873200141757102289777 113904900106317826717333)
                      ·
                        rfl

theorem cell23_221829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 5, 2].length) (baseStart_221829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221829 prefixEnd_221829 := by exact prefixLift 221829
  have htrace : WordTrace (prefixWord ++ tailWord_221829) baseStart_221829 baseEnd_221829 := by
    simpa [prefixWord, tailWord_221829, baseEnd_221829] using wordTrace_append hprefix tailTrace_221829
  have hstable : (prefixWord ++ tailWord_221829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221829).length < 2 ^ (prefixWord ++ tailWord_221829).sum := by decide
  have hdescent : baseEnd_221829 < baseStart_221829 := by decide
  rcases family_descends (prefixWord ++ tailWord_221829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221853 : List Nat := [1, 4, 2, 1, 1, 1, 5, 3, 1, 1, 3]
def baseStart_221853 : Nat := 118140960795 + 221853 * 2 ^ 59
def prefixEnd_221853 : Nat := 4983230072969 + 3 ^ 40 * 221853 * 2
def baseEnd_221853 : Nat := 113917223642025732817223

theorem tailTrace_221853 : CollatzResearch.WordTrace tailWord_221853 prefixEnd_221853 113917223642025732817223 := by
  unfold tailWord_221853
  simp only [CollatzResearch.WordTrace]
  refine ⟨8091643665271945320974213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5394429110181296880649475 8091643665271945320974213)
  ·
    refine ⟨1517183187238489747682665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8091643665271945320974213 1517183187238489747682665)
    ·
      refine ⟨1137887390428867310761999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1517183187238489747682665 1137887390428867310761999)
      ·
        refine ⟨1706831085643300966142999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1137887390428867310761999 1706831085643300966142999)
        ·
          refine ⟨2560246628464951449214499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1706831085643300966142999 2560246628464951449214499)
          ·
            refine ⟨3840369942697427173821749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2560246628464951449214499 3840369942697427173821749)
            ·
              refine ⟨360034682127883797545789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3840369942697427173821749 360034682127883797545789)
              ·
                refine ⟨135013005797956424079671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 360034682127883797545789 135013005797956424079671)
                ·
                  refine ⟨202519508696934636119507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135013005797956424079671 202519508696934636119507)
                  ·
                    refine ⟨303779263045401954179261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 202519508696934636119507 303779263045401954179261)
                    ·
                      refine ⟨113917223642025732817223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 303779263045401954179261 113917223642025732817223)
                      ·
                        rfl

theorem cell23_221853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_221853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221853 prefixEnd_221853 := by exact prefixLift 221853
  have htrace : WordTrace (prefixWord ++ tailWord_221853) baseStart_221853 baseEnd_221853 := by
    simpa [prefixWord, tailWord_221853, baseEnd_221853] using wordTrace_append hprefix tailTrace_221853
  have hstable : (prefixWord ++ tailWord_221853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221853).length < 2 ^ (prefixWord ++ tailWord_221853).sum := by decide
  have hdescent : baseEnd_221853 < baseStart_221853 := by decide
  rcases family_descends (prefixWord ++ tailWord_221853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221870 : List Nat := [4, 1, 4, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_221870 : Nat := 118140960795 + 221870 * 2 ^ 59
def prefixEnd_221870 : Nat := 4983230072969 + 3 ^ 40 * 221870 * 2
def baseEnd_221870 : Nat := 113925952813152166304645

theorem tailTrace_221870 : CollatzResearch.WordTrace tailWord_221870 prefixEnd_221870 113925952813152166304645 := by
  unfold tailWord_221870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1011532963276294653042883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5394842470806904816228709 1011532963276294653042883)
  ·
    refine ⟨1517299444914441979564325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1011532963276294653042883 1517299444914441979564325)
    ·
      refine ⟨284493645921457871168311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1517299444914441979564325 284493645921457871168311)
      ·
        refine ⟨426740468882186806752467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284493645921457871168311 426740468882186806752467)
        ·
          refine ⟨640110703323280210128701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426740468882186806752467 640110703323280210128701)
          ·
            refine ⟨240041513746230078798263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 640110703323280210128701 240041513746230078798263)
            ·
              refine ⟨360062270619345118197395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240041513746230078798263 360062270619345118197395)
              ·
                refine ⟨540093405929017677296093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360062270619345118197395 540093405929017677296093)
                ·
                  refine ⟨202535027223381628986035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 540093405929017677296093 202535027223381628986035)
                  ·
                    refine ⟨303802540835072443479053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 202535027223381628986035 303802540835072443479053)
                    ·
                      refine ⟨113925952813152166304645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 303802540835072443479053 113925952813152166304645)
                      ·
                        rfl

theorem cell23_221870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_221870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221870 prefixEnd_221870 := by exact prefixLift 221870
  have htrace : WordTrace (prefixWord ++ tailWord_221870) baseStart_221870 baseEnd_221870 := by
    simpa [prefixWord, tailWord_221870, baseEnd_221870] using wordTrace_append hprefix tailTrace_221870
  have hstable : (prefixWord ++ tailWord_221870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221870).length < 2 ^ (prefixWord ++ tailWord_221870).sum := by decide
  have hdescent : baseEnd_221870 < baseStart_221870 := by decide
  rcases family_descends (prefixWord ++ tailWord_221870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221882 : List Nat := [3, 1, 1, 1, 2, 3, 4, 8]
def baseStart_221882 : Nat := 118140960795 + 221882 * 2 ^ 59
def prefixEnd_221882 : Nat := 4983230072969 + 3 ^ 40 * 221882 * 2
def baseEnd_221882 : Nat := 4219707947444671087207

theorem tailTrace_221882 : CollatzResearch.WordTrace tailWord_221882 prefixEnd_221882 4219707947444671087207 := by
  unfold tailWord_221882
  simp only [CollatzResearch.WordTrace]
  refine ⟨2023175345541720818444975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5395134254777922182519933 2023175345541720818444975)
  ·
    refine ⟨3034763018312581227667463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2023175345541720818444975 3034763018312581227667463)
    ·
      refine ⟨4552144527468871841501195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3034763018312581227667463 4552144527468871841501195)
      ·
        refine ⟨6828216791203307762251793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4552144527468871841501195 6828216791203307762251793)
        ·
          refine ⟨5121162593402480821688845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6828216791203307762251793 5121162593402480821688845)
          ·
            refine ⟨1920435972525930308133317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5121162593402480821688845 1920435972525930308133317)
            ·
              refine ⟨360081744848611932774997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1920435972525930308133317 360081744848611932774997)
              ·
                refine ⟨4219707947444671087207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 360081744848611932774997 4219707947444671087207)
                ·
                  rfl

theorem cell23_221882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 8].length) (baseStart_221882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221882 prefixEnd_221882 := by exact prefixLift 221882
  have htrace : WordTrace (prefixWord ++ tailWord_221882) baseStart_221882 baseEnd_221882 := by
    simpa [prefixWord, tailWord_221882, baseEnd_221882] using wordTrace_append hprefix tailTrace_221882
  have hstable : (prefixWord ++ tailWord_221882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221882).length < 2 ^ (prefixWord ++ tailWord_221882).sum := by decide
  have hdescent : baseEnd_221882 < baseStart_221882 := by decide
  rcases family_descends (prefixWord ++ tailWord_221882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221886 : List Nat := [4, 2, 1, 1, 2, 1, 3, 3, 2, 4]
def baseStart_221886 : Nat := 118140960795 + 221886 * 2 ^ 59
def prefixEnd_221886 : Nat := 4983230072969 + 3 ^ 40 * 221886 * 2
def baseEnd_221886 : Nat := 37978056167874701234857

theorem tailTrace_221886 : CollatzResearch.WordTrace tailWord_221886 prefixEnd_221886 37978056167874701234857 := by
  unfold tailWord_221886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1011605909269048994615689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5395231516101594637950341 1011605909269048994615689)
  ·
    refine ⟨758704431951786745961767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1011605909269048994615689 758704431951786745961767)
    ·
      refine ⟨1138056647927680118942651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 758704431951786745961767 1138056647927680118942651)
      ·
        refine ⟨1707084971891520178413977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1138056647927680118942651 1707084971891520178413977)
        ·
          refine ⟨1280313728918640133810483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1707084971891520178413977 1280313728918640133810483)
          ·
            refine ⟨1920470593377960200715725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1280313728918640133810483 1920470593377960200715725)
            ·
              refine ⟨720176472516735075268397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1920470593377960200715725 720176472516735075268397)
              ·
                refine ⟨270066177193775653225649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 720176472516735075268397 270066177193775653225649)
                ·
                  refine ⟨202549632895331739919237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270066177193775653225649 202549632895331739919237)
                  ·
                    refine ⟨37978056167874701234857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 202549632895331739919237 37978056167874701234857)
                    ·
                      rfl

theorem cell23_221886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_221886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221886 prefixEnd_221886 := by exact prefixLift 221886
  have htrace : WordTrace (prefixWord ++ tailWord_221886) baseStart_221886 baseEnd_221886 := by
    simpa [prefixWord, tailWord_221886, baseEnd_221886] using wordTrace_append hprefix tailTrace_221886
  have hstable : (prefixWord ++ tailWord_221886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221886).length < 2 ^ (prefixWord ++ tailWord_221886).sum := by decide
  have hdescent : baseEnd_221886 < baseStart_221886 := by decide
  rcases family_descends (prefixWord ++ tailWord_221886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221896 : List Nat := [2, 1, 3, 1, 2, 3, 3, 2, 1, 2, 3]
def baseStart_221896 : Nat := 118140960795 + 221896 * 2 ^ 59
def prefixEnd_221896 : Nat := 4983230072969 + 3 ^ 40 * 221896 * 2
def baseEnd_221896 : Nat := 113939303310169064579525

theorem tailTrace_221896 : CollatzResearch.WordTrace tailWord_221896 prefixEnd_221896 113939303310169064579525 := by
  unfold tailWord_221896
  simp only [CollatzResearch.WordTrace]
  refine ⟨4046606002058081832394771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5395474669410775776526361 4046606002058081832394771)
  ·
    refine ⟨6069909003087122748592157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4046606002058081832394771 6069909003087122748592157)
    ·
      refine ⟨2276215876157671030722059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6069909003087122748592157 2276215876157671030722059)
      ·
        refine ⟨3414323814236506546083089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2276215876157671030722059 3414323814236506546083089)
        ·
          refine ⟨2560742860677379909562317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3414323814236506546083089 2560742860677379909562317)
          ·
            refine ⟨960278572754017466085869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2560742860677379909562317 960278572754017466085869)
            ·
              refine ⟨360104464782756549782201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 960278572754017466085869 360104464782756549782201)
              ·
                refine ⟨270078348587067412336651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360104464782756549782201 270078348587067412336651)
                ·
                  refine ⟨405117522880601118504977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270078348587067412336651 405117522880601118504977)
                  ·
                    refine ⟨303838142160450838878733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 405117522880601118504977 303838142160450838878733)
                    ·
                      refine ⟨113939303310169064579525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 303838142160450838878733 113939303310169064579525)
                      ·
                        rfl

theorem cell23_221896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_221896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221896 prefixEnd_221896 := by exact prefixLift 221896
  have htrace : WordTrace (prefixWord ++ tailWord_221896) baseStart_221896 baseEnd_221896 := by
    simpa [prefixWord, tailWord_221896, baseEnd_221896] using wordTrace_append hprefix tailTrace_221896
  have hstable : (prefixWord ++ tailWord_221896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221896).length < 2 ^ (prefixWord ++ tailWord_221896).sum := by decide
  have hdescent : baseEnd_221896 < baseStart_221896 := by decide
  rcases family_descends (prefixWord ++ tailWord_221896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221906 : List Nat := [3, 2, 2, 2, 3, 1, 1, 2, 1, 2, 4]
def baseStart_221906 : Nat := 118140960795 + 221906 * 2 ^ 59
def prefixEnd_221906 : Nat := 4983230072969 + 3 ^ 40 * 221906 * 2
def baseEnd_221906 : Nat := 113944438116714025454479

theorem tailTrace_221906 : CollatzResearch.WordTrace tailWord_221906 prefixEnd_221906 113944438116714025454479 := by
  unfold tailWord_221906
  simp only [CollatzResearch.WordTrace]
  refine ⟨2023394183519983843163393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5395717822719956915102381 2023394183519983843163393)
  ·
    refine ⟨1517545637639987882372545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2023394183519983843163393 1517545637639987882372545)
    ·
      refine ⟨1138159228229990911779409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1517545637639987882372545 1138159228229990911779409)
      ·
        refine ⟨853619421172493183834557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1138159228229990911779409 853619421172493183834557)
        ·
          refine ⟨320107282939684943937959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 853619421172493183834557 320107282939684943937959)
          ·
            refine ⟨480160924409527415906939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320107282939684943937959 480160924409527415906939)
            ·
              refine ⟨720241386614291123860409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480160924409527415906939 720241386614291123860409)
              ·
                refine ⟨540181039960718342895307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 720241386614291123860409 540181039960718342895307)
                ·
                  refine ⟨810271559941077514342961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 540181039960718342895307 810271559941077514342961)
                  ·
                    refine ⟨607703669955808135757221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 810271559941077514342961 607703669955808135757221)
                    ·
                      refine ⟨113944438116714025454479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 607703669955808135757221 113944438116714025454479)
                      ·
                        rfl

theorem cell23_221906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_221906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221906 prefixEnd_221906 := by exact prefixLift 221906
  have htrace : WordTrace (prefixWord ++ tailWord_221906) baseStart_221906 baseEnd_221906 := by
    simpa [prefixWord, tailWord_221906, baseEnd_221906] using wordTrace_append hprefix tailTrace_221906
  have hstable : (prefixWord ++ tailWord_221906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221906).length < 2 ^ (prefixWord ++ tailWord_221906).sum := by decide
  have hdescent : baseEnd_221906 < baseStart_221906 := by decide
  rcases family_descends (prefixWord ++ tailWord_221906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221940 : List Nat := [2, 6, 1, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_221940 : Nat := 118140960795 + 221940 * 2 ^ 59
def prefixEnd_221940 : Nat := 4983230072969 + 3 ^ 40 * 221940 * 2
def baseEnd_221940 : Nat := 113961896458966892429323

theorem tailTrace_221940 : CollatzResearch.WordTrace tailWord_221940 prefixEnd_221940 113961896458966892429323 := by
  unfold tailWord_221940
  simp only [CollatzResearch.WordTrace]
  refine ⟨4047408407978379589695637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5396544543971172786260849 4047408407978379589695637)
  ·
    refine ⟨189722269123986543266983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4047408407978379589695637 189722269123986543266983)
    ·
      refine ⟨284583403685979814900475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189722269123986543266983 284583403685979814900475)
      ·
        refine ⟨426875105528969722350713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284583403685979814900475 426875105528969722350713)
        ·
          refine ⟨320156329146727291763035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426875105528969722350713 320156329146727291763035)
          ·
            refine ⟨480234493720090937644553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320156329146727291763035 480234493720090937644553)
            ·
              refine ⟨360175870290068203233415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480234493720090937644553 360175870290068203233415)
              ·
                refine ⟨540263805435102304850123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360175870290068203233415 540263805435102304850123)
                ·
                  refine ⟨810395708152653457275185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 540263805435102304850123 810395708152653457275185)
                  ·
                    refine ⟨607796781114490092956389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 810395708152653457275185 607796781114490092956389)
                    ·
                      refine ⟨113961896458966892429323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 607796781114490092956389 113961896458966892429323)
                      ·
                        rfl

theorem cell23_221940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_221940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221940 prefixEnd_221940 := by exact prefixLift 221940
  have htrace : WordTrace (prefixWord ++ tailWord_221940) baseStart_221940 baseEnd_221940 := by
    simpa [prefixWord, tailWord_221940, baseEnd_221940] using wordTrace_append hprefix tailTrace_221940
  have hstable : (prefixWord ++ tailWord_221940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221940).length < 2 ^ (prefixWord ++ tailWord_221940).sum := by decide
  have hdescent : baseEnd_221940 < baseStart_221940 := by decide
  rcases family_descends (prefixWord ++ tailWord_221940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221983 : List Nat := [1, 1, 2, 4, 2, 3, 1, 1, 4, 2, 2]
def baseStart_221983 : Nat := 118140960795 + 221983 * 2 ^ 59
def prefixEnd_221983 : Nat := 4983230072969 + 3 ^ 40 * 221983 * 2
def baseEnd_221983 : Nat := 113983976127110224191625

theorem tailTrace_221983 : CollatzResearch.WordTrace tailWord_221983 prefixEnd_221983 113983976127110224191625 := by
  unfold tailWord_221983
  simp only [CollatzResearch.WordTrace]
  refine ⟨8096385154800977523206603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5397590103200651682137735 8096385154800977523206603)
  ·
    refine ⟨12144577732201466284809905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8096385154800977523206603 12144577732201466284809905)
    ·
      refine ⟨9108433299151099713607429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12144577732201466284809905 9108433299151099713607429)
      ·
        refine ⟨1707831243590831196301393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9108433299151099713607429 1707831243590831196301393)
        ·
          refine ⟨1280873432693123397226045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1707831243590831196301393 1280873432693123397226045)
          ·
            refine ⟨480327537259921273959767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1280873432693123397226045 480327537259921273959767)
            ·
              refine ⟨720491305889881910939651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480327537259921273959767 720491305889881910939651)
              ·
                refine ⟨1080736958834822866409477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 720491305889881910939651 1080736958834822866409477)
                ·
                  refine ⟨202638179781529287451777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1080736958834822866409477 202638179781529287451777)
                  ·
                    refine ⟨151978634836146965588833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 202638179781529287451777 151978634836146965588833)
                    ·
                      refine ⟨113983976127110224191625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 151978634836146965588833 113983976127110224191625)
                      ·
                        rfl

theorem cell23_221983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_221983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221983 prefixEnd_221983 := by exact prefixLift 221983
  have htrace : WordTrace (prefixWord ++ tailWord_221983) baseStart_221983 baseEnd_221983 := by
    simpa [prefixWord, tailWord_221983, baseEnd_221983] using wordTrace_append hprefix tailTrace_221983
  have hstable : (prefixWord ++ tailWord_221983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221983).length < 2 ^ (prefixWord ++ tailWord_221983).sum := by decide
  have hdescent : baseEnd_221983 < baseStart_221983 := by decide
  rcases family_descends (prefixWord ++ tailWord_221983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221989 : List Nat := [1, 3, 1, 2, 3, 1, 4, 1, 7]
def baseStart_221989 : Nat := 118140960795 + 221989 * 2 ^ 59
def prefixEnd_221989 : Nat := 4983230072969 + 3 ^ 40 * 221989 * 2
def baseEnd_221989 : Nat := 12665228556781911190733

theorem tailTrace_221989 : CollatzResearch.WordTrace tailWord_221989 prefixEnd_221989 12665228556781911190733 := by
  unfold tailWord_221989
  simp only [CollatzResearch.WordTrace]
  refine ⟨8096603992779240547925021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5397735995186160365283347 8096603992779240547925021)
  ·
    refine ⟨3036226497292215205471883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8096603992779240547925021 3036226497292215205471883)
    ·
      refine ⟨4554339745938322808207825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3036226497292215205471883 4554339745938322808207825)
      ·
        refine ⟨3415754809453742106155869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4554339745938322808207825 3415754809453742106155869)
        ·
          refine ⟨1280908053545153289808451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3415754809453742106155869 1280908053545153289808451)
          ·
            refine ⟨1921362080317729934712677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1280908053545153289808451 1921362080317729934712677)
            ·
              refine ⟨360255390059574362758627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1921362080317729934712677 360255390059574362758627)
              ·
                refine ⟨540383085089361544137941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360255390059574362758627 540383085089361544137941)
                ·
                  refine ⟨12665228556781911190733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 540383085089361544137941 12665228556781911190733)
                  ·
                    rfl

theorem cell23_221989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 7].length) (baseStart_221989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_221989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_221989 prefixEnd_221989 := by exact prefixLift 221989
  have htrace : WordTrace (prefixWord ++ tailWord_221989) baseStart_221989 baseEnd_221989 := by
    simpa [prefixWord, tailWord_221989, baseEnd_221989] using wordTrace_append hprefix tailTrace_221989
  have hstable : (prefixWord ++ tailWord_221989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221989).length < 2 ^ (prefixWord ++ tailWord_221989).sum := by decide
  have hdescent : baseEnd_221989 < baseStart_221989 := by decide
  rcases family_descends (prefixWord ++ tailWord_221989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222019 : List Nat := [1, 1, 1, 3, 1, 4, 2, 3, 2, 5]
def baseStart_222019 : Nat := 118140960795 + 222019 * 2 ^ 59
def prefixEnd_222019 : Nat := 4983230072969 + 3 ^ 40 * 222019 * 2
def baseEnd_222019 : Nat := 38000820476890694447153

theorem tailTrace_222019 : CollatzResearch.WordTrace tailWord_222019 prefixEnd_222019 38000820476890694447153 := by
  unfold tailWord_222019
  simp only [CollatzResearch.WordTrace]
  refine ⟨8097698182670555671517111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5398465455113703781011407 8097698182670555671517111)
  ·
    refine ⟨12146547274005833507275667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8097698182670555671517111 12146547274005833507275667)
    ·
      refine ⟨18219820911008750260913501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12146547274005833507275667 18219820911008750260913501)
      ·
        refine ⟨6832432841628281347842563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18219820911008750260913501 6832432841628281347842563)
        ·
          refine ⟨10248649262442422021763845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6832432841628281347842563 10248649262442422021763845)
          ·
            refine ⟨1921621736707954129080721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10248649262442422021763845 1921621736707954129080721)
            ·
              refine ⟨1441216302530965596810541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1921621736707954129080721 1441216302530965596810541)
              ·
                refine ⟨540456113449112098803953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1441216302530965596810541 540456113449112098803953)
                ·
                  refine ⟨405342085086834074102965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540456113449112098803953 405342085086834074102965)
                  ·
                    refine ⟨38000820476890694447153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 405342085086834074102965 38000820476890694447153)
                    ·
                      rfl

theorem cell23_222019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 5].length) (baseStart_222019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222019 prefixEnd_222019 := by exact prefixLift 222019
  have htrace : WordTrace (prefixWord ++ tailWord_222019) baseStart_222019 baseEnd_222019 := by
    simpa [prefixWord, tailWord_222019, baseEnd_222019] using wordTrace_append hprefix tailTrace_222019
  have hstable : (prefixWord ++ tailWord_222019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222019).length < 2 ^ (prefixWord ++ tailWord_222019).sum := by decide
  have hdescent : baseEnd_222019 < baseStart_222019 := by decide
  rcases family_descends (prefixWord ++ tailWord_222019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222059 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 3, 4, 3]
def baseStart_222059 : Nat := 118140960795 + 222059 * 2 ^ 59
def prefixEnd_222059 : Nat := 4983230072969 + 3 ^ 40 * 222059 * 2
def baseEnd_222059 : Nat := 114023000656851926841275

theorem tailTrace_222059 : CollatzResearch.WordTrace tailWord_222059 prefixEnd_222059 114023000656851926841275 := by
  unfold tailWord_222059
  simp only [CollatzResearch.WordTrace]
  refine ⟨8099157102525642502973231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5399438068350428335315487 8099157102525642502973231)
  ·
    refine ⟨12148735653788463754459847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8099157102525642502973231 12148735653788463754459847)
    ·
      refine ⟨18223103480682695631689771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12148735653788463754459847 18223103480682695631689771)
      ·
        refine ⟨27334655221024043447534657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18223103480682695631689771 27334655221024043447534657)
        ·
          refine ⟨20500991415768032585650993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27334655221024043447534657 20500991415768032585650993)
          ·
            refine ⟨15375743561826024439238245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20500991415768032585650993 15375743561826024439238245)
            ·
              refine ⟨2882951917842379582357171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15375743561826024439238245 2882951917842379582357171)
              ·
                refine ⟨4324427876763569373535757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2882951917842379582357171 4324427876763569373535757)
                ·
                  refine ⟨1621660453786338515075909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4324427876763569373535757 1621660453786338515075909)
                  ·
                    refine ⟨304061335084938471576733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1621660453786338515075909 304061335084938471576733)
                    ·
                      refine ⟨114023000656851926841275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 304061335084938471576733 114023000656851926841275)
                      ·
                        rfl

theorem cell23_222059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4, 3].length) (baseStart_222059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222059 prefixEnd_222059 := by exact prefixLift 222059
  have htrace : WordTrace (prefixWord ++ tailWord_222059) baseStart_222059 baseEnd_222059 := by
    simpa [prefixWord, tailWord_222059, baseEnd_222059] using wordTrace_append hprefix tailTrace_222059
  have hstable : (prefixWord ++ tailWord_222059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222059).length < 2 ^ (prefixWord ++ tailWord_222059).sum := by decide
  have hdescent : baseEnd_222059 < baseStart_222059 := by decide
  rcases family_descends (prefixWord ++ tailWord_222059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222066 : List Nat := [3, 2, 1, 2, 1, 1, 2, 4, 3, 4]
def baseStart_222066 : Nat := 118140960795 + 222066 * 2 ^ 59
def prefixEnd_222066 : Nat := 4983230072969 + 3 ^ 40 * 222066 * 2
def baseEnd_222066 : Nat := 38008865007144466484581

theorem tailTrace_222066 : CollatzResearch.WordTrace tailWord_222066 prefixEnd_222066 38008865007144466484581 := by
  unfold tailWord_222066
  simp only [CollatzResearch.WordTrace]
  refine ⟨2024853103375070674619513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5399608275666855132318701 2024853103375070674619513)
  ·
    refine ⟨1518639827531303005964635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2024853103375070674619513 1518639827531303005964635)
    ·
      refine ⟨2277959741296954508946953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1518639827531303005964635 2277959741296954508946953)
      ·
        refine ⟨1708469805972715881710215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2277959741296954508946953 1708469805972715881710215)
        ·
          refine ⟨2562704708959073822565323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1708469805972715881710215 2562704708959073822565323)
          ·
            refine ⟨3844057063438610733847985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2562704708959073822565323 3844057063438610733847985)
            ·
              refine ⟨2883042797578958050385989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3844057063438610733847985 2883042797578958050385989)
              ·
                refine ⟨540570524546054634447373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2883042797578958050385989 540570524546054634447373)
                ·
                  refine ⟨202713946704770487917765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 540570524546054634447373 202713946704770487917765)
                  ·
                    refine ⟨38008865007144466484581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 202713946704770487917765 38008865007144466484581)
                    ·
                      rfl

theorem cell23_222066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_222066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222066 prefixEnd_222066 := by exact prefixLift 222066
  have htrace : WordTrace (prefixWord ++ tailWord_222066) baseStart_222066 baseEnd_222066 := by
    simpa [prefixWord, tailWord_222066, baseEnd_222066] using wordTrace_append hprefix tailTrace_222066
  have hstable : (prefixWord ++ tailWord_222066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222066).length < 2 ^ (prefixWord ++ tailWord_222066).sum := by decide
  have hdescent : baseEnd_222066 < baseStart_222066 := by decide
  rcases family_descends (prefixWord ++ tailWord_222066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222083 : List Nat := [1, 1, 1, 3, 4, 1, 2, 5, 1, 4]
def baseStart_222083 : Nat := 118140960795 + 222083 * 2 ^ 59
def prefixEnd_222083 : Nat := 4983230072969 + 3 ^ 40 * 222083 * 2
def baseEnd_222083 : Nat := 38011774730853277647055

theorem tailTrace_222083 : CollatzResearch.WordTrace tailWord_222083 prefixEnd_222083 38011774730853277647055 := by
  unfold tailWord_222083
  simp only [CollatzResearch.WordTrace]
  refine ⟨8100032454438694601846903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5400021636292463067897935 8100032454438694601846903)
  ·
    refine ⟨12150048681658041902770355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8100032454438694601846903 12150048681658041902770355)
    ·
      refine ⟨18225073022487062854155533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12150048681658041902770355 18225073022487062854155533)
      ·
        refine ⟨6834402383432648570308325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18225073022487062854155533 6834402383432648570308325)
        ·
          refine ⟨1281450446893621606932811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6834402383432648570308325 1281450446893621606932811)
          ·
            refine ⟨1922175670340432410399217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1281450446893621606932811 1922175670340432410399217)
            ·
              refine ⟨1441631752755324307799413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1922175670340432410399217 1441631752755324307799413)
              ·
                refine ⟨135152976820811653856195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1441631752755324307799413 135152976820811653856195)
                ·
                  refine ⟨202729465231217480784293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135152976820811653856195 202729465231217480784293)
                  ·
                    refine ⟨38011774730853277647055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 202729465231217480784293 38011774730853277647055)
                    ·
                      rfl

theorem cell23_222083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5, 1, 4].length) (baseStart_222083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222083 prefixEnd_222083 := by exact prefixLift 222083
  have htrace : WordTrace (prefixWord ++ tailWord_222083) baseStart_222083 baseEnd_222083 := by
    simpa [prefixWord, tailWord_222083, baseEnd_222083] using wordTrace_append hprefix tailTrace_222083
  have hstable : (prefixWord ++ tailWord_222083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222083).length < 2 ^ (prefixWord ++ tailWord_222083).sum := by decide
  have hdescent : baseEnd_222083 < baseStart_222083 := by decide
  rcases family_descends (prefixWord ++ tailWord_222083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222100 : List Nat := [2, 4, 2, 1, 1, 1, 3, 4, 1, 4]
def baseStart_222100 : Nat := 118140960795 + 222100 * 2 ^ 59
def prefixEnd_222100 : Nat := 4983230072969 + 3 ^ 40 * 222100 * 2
def baseEnd_222100 : Nat := 38014684454562088809529

theorem tailTrace_222100 : CollatzResearch.WordTrace tailWord_222100 prefixEnd_222100 38014684454562088809529 := by
  unfold tailWord_222100
  simp only [CollatzResearch.WordTrace]
  refine ⟨4050326247688553252607877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5400434996918071003477169 4050326247688553252607877)
  ·
    refine ⟨759436171441603734863977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4050326247688553252607877 759436171441603734863977)
    ·
      refine ⟨569577128581202801147983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 759436171441603734863977 569577128581202801147983)
      ·
        refine ⟨854365692871804201721975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 569577128581202801147983 854365692871804201721975)
        ·
          refine ⟨1281548539307706302582963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 854365692871804201721975 1281548539307706302582963)
          ·
            refine ⟨1922322808961559453874445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1281548539307706302582963 1922322808961559453874445)
            ·
              refine ⟨720871053360584795202917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1922322808961559453874445 720871053360584795202917)
              ·
                refine ⟨135163322505109649100547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 720871053360584795202917 135163322505109649100547)
                ·
                  refine ⟨202744983757664473650821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135163322505109649100547 202744983757664473650821)
                  ·
                    refine ⟨38014684454562088809529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 202744983757664473650821 38014684454562088809529)
                    ·
                      rfl

theorem cell23_222100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_222100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222100 prefixEnd_222100 := by exact prefixLift 222100
  have htrace : WordTrace (prefixWord ++ tailWord_222100) baseStart_222100 baseEnd_222100 := by
    simpa [prefixWord, tailWord_222100, baseEnd_222100] using wordTrace_append hprefix tailTrace_222100
  have hstable : (prefixWord ++ tailWord_222100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222100).length < 2 ^ (prefixWord ++ tailWord_222100).sum := by decide
  have hdescent : baseEnd_222100 < baseStart_222100 := by decide
  rcases family_descends (prefixWord ++ tailWord_222100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222133 : List Nat := [1, 3, 3, 2, 1, 1, 3, 1, 1, 5, 2]
def baseStart_222133 : Nat := 118140960795 + 222133 * 2 ^ 59
def prefixEnd_222133 : Nat := 4983230072969 + 3 ^ 40 * 222133 * 2
def baseEnd_222133 : Nat := 114060998225284637315935

theorem tailTrace_222133 : CollatzResearch.WordTrace tailWord_222133 prefixEnd_222133 114060998225284637315935 := by
  unfold tailWord_222133
  simp only [CollatzResearch.WordTrace]
  refine ⟨8101856104257553141167053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5401237402838368760778035 8101856104257553141167053)
  ·
    refine ⟨3038196039096582427937645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8101856104257553141167053 3038196039096582427937645)
    ·
      refine ⟨1139323514661218410476617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3038196039096582427937645 1139323514661218410476617)
      ·
        refine ⟨854492635995913807857463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1139323514661218410476617 854492635995913807857463)
        ·
          refine ⟨1281738953993870711786195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 854492635995913807857463 1281738953993870711786195)
          ·
            refine ⟨1922608430990806067679293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1281738953993870711786195 1922608430990806067679293)
            ·
              refine ⟨720978161621552275379735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1922608430990806067679293 720978161621552275379735)
              ·
                refine ⟨1081467242432328413069603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 720978161621552275379735 1081467242432328413069603)
                ·
                  refine ⟨1622200863648492619604405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1081467242432328413069603 1622200863648492619604405)
                  ·
                    refine ⟨152081330967046183087913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1622200863648492619604405 152081330967046183087913)
                    ·
                      refine ⟨114060998225284637315935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 152081330967046183087913 114060998225284637315935)
                      ·
                        rfl

theorem cell23_222133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_222133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222133 prefixEnd_222133 := by exact prefixLift 222133
  have htrace : WordTrace (prefixWord ++ tailWord_222133) baseStart_222133 baseEnd_222133 := by
    simpa [prefixWord, tailWord_222133, baseEnd_222133] using wordTrace_append hprefix tailTrace_222133
  have hstable : (prefixWord ++ tailWord_222133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222133).length < 2 ^ (prefixWord ++ tailWord_222133).sum := by decide
  have hdescent : baseEnd_222133 < baseStart_222133 := by decide
  rcases family_descends (prefixWord ++ tailWord_222133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222173 : List Nat := [1, 4, 3, 1, 2, 1, 3, 1, 1, 6]
def baseStart_222173 : Nat := 118140960795 + 222173 * 2 ^ 59
def prefixEnd_222173 : Nat := 4983230072969 + 3 ^ 40 * 222173 * 2
def baseEnd_222173 : Nat := 38027179150488160271917

theorem tailTrace_222173 : CollatzResearch.WordTrace tailWord_222173 prefixEnd_222173 38027179150488160271917 := by
  unfold tailWord_222173
  simp only [CollatzResearch.WordTrace]
  refine ⟨8103315024112639972623173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5402210016075093315082115 8103315024112639972623173)
  ·
    refine ⟨1519371567021119994866845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8103315024112639972623173 1519371567021119994866845)
    ·
      refine ⟨569764337632919998075067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1519371567021119994866845 569764337632919998075067)
      ·
        refine ⟨854646506449379997112601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 569764337632919998075067 854646506449379997112601)
        ·
          refine ⟨640984879837034997834451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 854646506449379997112601 640984879837034997834451)
          ·
            refine ⟨961477319755552496751677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640984879837034997834451 961477319755552496751677)
            ·
              refine ⟨360553994908332186281879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 961477319755552496751677 360553994908332186281879)
              ·
                refine ⟨540830992362498279422819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360553994908332186281879 540830992362498279422819)
                ·
                  refine ⟨811246488543747419134229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 540830992362498279422819 811246488543747419134229)
                  ·
                    refine ⟨38027179150488160271917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 811246488543747419134229 38027179150488160271917)
                    ·
                      rfl

theorem cell23_222173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_222173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222173 prefixEnd_222173 := by exact prefixLift 222173
  have htrace : WordTrace (prefixWord ++ tailWord_222173) baseStart_222173 baseEnd_222173 := by
    simpa [prefixWord, tailWord_222173, baseEnd_222173] using wordTrace_append hprefix tailTrace_222173
  have hstable : (prefixWord ++ tailWord_222173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222173).length < 2 ^ (prefixWord ++ tailWord_222173).sum := by decide
  have hdescent : baseEnd_222173 < baseStart_222173 := by decide
  rcases family_descends (prefixWord ++ tailWord_222173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222186 : List Nat := [3, 1, 3, 1, 2, 3, 1, 9]
def baseStart_222186 : Nat := 118140960795 + 222186 * 2 ^ 59
def prefixEnd_222186 : Nat := 4983230072969 + 3 ^ 40 * 222186 * 2
def baseEnd_222186 : Nat := 4225489359258256664933

theorem tailTrace_222186 : CollatzResearch.WordTrace tailWord_222186 prefixEnd_222186 4225489359258256664933 := by
  unfold tailWord_222186
  simp only [CollatzResearch.WordTrace]
  refine ⟨2025947293266385798211603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5402526115377028795230941 2025947293266385798211603)
  ·
    refine ⟨3038920939899578697317405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2025947293266385798211603 3038920939899578697317405)
    ·
      refine ⟨1139595352462342011494027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3038920939899578697317405 1139595352462342011494027)
      ·
        refine ⟨1709393028693513017241041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1139595352462342011494027 1709393028693513017241041)
        ·
          refine ⟨1282044771520134762930781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1709393028693513017241041 1282044771520134762930781)
          ·
            refine ⟨480766789320050536099043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1282044771520134762930781 480766789320050536099043)
            ·
              refine ⟨721150183980075804148565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480766789320050536099043 721150183980075804148565)
              ·
                refine ⟨4225489359258256664933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 721150183980075804148565 4225489359258256664933)
                ·
                  rfl

theorem cell23_222186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 9].length) (baseStart_222186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222186 prefixEnd_222186 := by exact prefixLift 222186
  have htrace : WordTrace (prefixWord ++ tailWord_222186) baseStart_222186 baseEnd_222186 := by
    simpa [prefixWord, tailWord_222186, baseEnd_222186] using wordTrace_append hprefix tailTrace_222186
  have hstable : (prefixWord ++ tailWord_222186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222186).length < 2 ^ (prefixWord ++ tailWord_222186).sum := by decide
  have hdescent : baseEnd_222186 < baseStart_222186 := by decide
  rcases family_descends (prefixWord ++ tailWord_222186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222213 : List Nat := [1, 3, 1, 1, 2, 3, 1, 3, 4, 1, 3]
def baseStart_222213 : Nat := 118140960795 + 222213 * 2 ^ 59
def prefixEnd_222213 : Nat := 4983230072969 + 3 ^ 40 * 222213 * 2
def baseEnd_222213 : Nat := 114102076677644324315567

theorem tailTrace_222213 : CollatzResearch.WordTrace tailWord_222213 prefixEnd_222213 114102076677644324315567 := by
  unfold tailWord_222213
  simp only [CollatzResearch.WordTrace]
  refine ⟨8104773943967726804079293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5403182629311817869386195 8104773943967726804079293)
  ·
    refine ⟨3039290228987897551529735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8104773943967726804079293 3039290228987897551529735)
    ·
      refine ⟨4558935343481846327294603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3039290228987897551529735 4558935343481846327294603)
      ·
        refine ⟨6838403015222769490941905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4558935343481846327294603 6838403015222769490941905)
        ·
          refine ⟨5128802261417077118206429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6838403015222769490941905 5128802261417077118206429)
          ·
            refine ⟨1923300848031403919327411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5128802261417077118206429 1923300848031403919327411)
            ·
              refine ⟨2884951272047105878991117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1923300848031403919327411 2884951272047105878991117)
              ·
                refine ⟨1081856727017664704621669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2884951272047105878991117 1081856727017664704621669)
                ·
                  refine ⟨202848136315812132116563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1081856727017664704621669 202848136315812132116563)
                  ·
                    refine ⟨304272204473718198174845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 202848136315812132116563 304272204473718198174845)
                    ·
                      refine ⟨114102076677644324315567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 304272204473718198174845 114102076677644324315567)
                      ·
                        rfl

theorem cell23_222213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4, 1, 3].length) (baseStart_222213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222213 prefixEnd_222213 := by exact prefixLift 222213
  have htrace : WordTrace (prefixWord ++ tailWord_222213) baseStart_222213 baseEnd_222213 := by
    simpa [prefixWord, tailWord_222213, baseEnd_222213] using wordTrace_append hprefix tailTrace_222213
  have hstable : (prefixWord ++ tailWord_222213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222213).length < 2 ^ (prefixWord ++ tailWord_222213).sum := by decide
  have hdescent : baseEnd_222213 < baseStart_222213 := by decide
  rcases family_descends (prefixWord ++ tailWord_222213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222256 : List Nat := [2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 5]
def baseStart_222256 : Nat := 118140960795 + 222256 * 2 ^ 59
def prefixEnd_222256 : Nat := 4983230072969 + 3 ^ 40 * 222256 * 2
def baseEnd_222256 : Nat := 114124156345787656077869

theorem tailTrace_222256 : CollatzResearch.WordTrace tailWord_222256 prefixEnd_222256 114124156345787656077869 := by
  unfold tailWord_222256
  simp only [CollatzResearch.WordTrace]
  refine ⟨4053171141405972573947311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5404228188541296765263081 4053171141405972573947311)
  ·
    refine ⟨6079756712108958860920967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4053171141405972573947311 6079756712108958860920967)
    ·
      refine ⟨9119635068163438291381451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6079756712108958860920967 9119635068163438291381451)
      ·
        refine ⟨13679452602245157437072177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9119635068163438291381451 13679452602245157437072177)
        ·
          refine ⟨10259589451683868077804133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13679452602245157437072177 10259589451683868077804133)
          ·
            refine ⟨1923673022190725264588275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10259589451683868077804133 1923673022190725264588275)
            ·
              refine ⟨2885509533286087896882413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1923673022190725264588275 2885509533286087896882413)
              ·
                refine ⟨1082066074982282961330905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2885509533286087896882413 1082066074982282961330905)
                ·
                  refine ⟨811549556236712220998179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1082066074982282961330905 811549556236712220998179)
                  ·
                    refine ⟨1217324334355068331497269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 811549556236712220998179 1217324334355068331497269)
                    ·
                      refine ⟨114124156345787656077869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1217324334355068331497269 114124156345787656077869)
                      ·
                        rfl

theorem cell23_222256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 5].length) (baseStart_222256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222256 prefixEnd_222256 := by exact prefixLift 222256
  have htrace : WordTrace (prefixWord ++ tailWord_222256) baseStart_222256 baseEnd_222256 := by
    simpa [prefixWord, tailWord_222256, baseEnd_222256] using wordTrace_append hprefix tailTrace_222256
  have hstable : (prefixWord ++ tailWord_222256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222256).length < 2 ^ (prefixWord ++ tailWord_222256).sum := by decide
  have hdescent : baseEnd_222256 < baseStart_222256 := by decide
  rcases family_descends (prefixWord ++ tailWord_222256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222257 : List Nat := [1, 2, 2, 3, 1, 2, 5, 1, 1, 3, 2]
def baseStart_222257 : Nat := 118140960795 + 222257 * 2 ^ 59
def prefixEnd_222257 : Nat := 4983230072969 + 3 ^ 40 * 222257 * 2
def baseEnd_222257 : Nat := 114124669826442152165365

theorem tailTrace_222257 : CollatzResearch.WordTrace tailWord_222257 prefixEnd_222257 114124669826442152165365 := by
  unfold tailWord_222257
  simp only [CollatzResearch.WordTrace]
  refine ⟨8106378755808322318681025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5404252503872214879120683 8106378755808322318681025)
  ·
    refine ⟨6079784066856241739010769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8106378755808322318681025 6079784066856241739010769)
    ·
      refine ⟨4559838050142181304258077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6079784066856241739010769 4559838050142181304258077)
      ·
        refine ⟨1709939268803317989096779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4559838050142181304258077 1709939268803317989096779)
        ·
          refine ⟨2564908903204976983645169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1709939268803317989096779 2564908903204976983645169)
          ·
            refine ⟨1923681677403732737733877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2564908903204976983645169 1923681677403732737733877)
            ·
              refine ⟨180345157256599944162551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1923681677403732737733877 180345157256599944162551)
              ·
                refine ⟨270517735884899916243827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180345157256599944162551 270517735884899916243827)
                ·
                  refine ⟨405776603827349874365741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270517735884899916243827 405776603827349874365741)
                  ·
                    refine ⟨152166226435256202887153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 405776603827349874365741 152166226435256202887153)
                    ·
                      refine ⟨114124669826442152165365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 152166226435256202887153 114124669826442152165365)
                      ·
                        rfl

theorem cell23_222257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_222257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222257 prefixEnd_222257 := by exact prefixLift 222257
  have htrace : WordTrace (prefixWord ++ tailWord_222257) baseStart_222257 baseEnd_222257 := by
    simpa [prefixWord, tailWord_222257, baseEnd_222257] using wordTrace_append hprefix tailTrace_222257
  have hstable : (prefixWord ++ tailWord_222257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222257).length < 2 ^ (prefixWord ++ tailWord_222257).sum := by decide
  have hdescent : baseEnd_222257 < baseStart_222257 := by decide
  rcases family_descends (prefixWord ++ tailWord_222257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222400 : List Nat := [2, 1, 1, 2, 6, 1, 1, 3, 6]
def baseStart_222400 : Nat := 118140960795 + 222400 * 2 ^ 59
def prefixEnd_222400 : Nat := 4983230072969 + 3 ^ 40 * 222400 * 2
def baseEnd_222400 : Nat := 12688677506670565853023

theorem tailTrace_222400 : CollatzResearch.WordTrace tailWord_222400 prefixEnd_222400 12688677506670565853023 := by
  unfold tailWord_222400
  simp only [CollatzResearch.WordTrace]
  refine ⟨4055797197145128870568327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5407729596193505160757769 4055797197145128870568327)
  ·
    refine ⟨6083695795717693305852491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4055797197145128870568327 6083695795717693305852491)
    ·
      refine ⟨9125543693576539958778737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6083695795717693305852491 9125543693576539958778737)
      ·
        refine ⟨6844157770182404969084053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9125543693576539958778737 6844157770182404969084053)
        ·
          refine ⟨320819895477300232925815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6844157770182404969084053 320819895477300232925815)
          ·
            refine ⟨481229843215950349388723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320819895477300232925815 481229843215950349388723)
            ·
              refine ⟨721844764823925524083085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481229843215950349388723 721844764823925524083085)
              ·
                refine ⟨270691786808972071531157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 721844764823925524083085 270691786808972071531157)
                ·
                  refine ⟨12688677506670565853023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 270691786808972071531157 12688677506670565853023)
                  ·
                    rfl

theorem cell23_222400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 6].length) (baseStart_222400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222400 prefixEnd_222400 := by exact prefixLift 222400
  have htrace : WordTrace (prefixWord ++ tailWord_222400) baseStart_222400 baseEnd_222400 := by
    simpa [prefixWord, tailWord_222400, baseEnd_222400] using wordTrace_append hprefix tailTrace_222400
  have hstable : (prefixWord ++ tailWord_222400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222400).length < 2 ^ (prefixWord ++ tailWord_222400).sum := by decide
  have hdescent : baseEnd_222400 < baseStart_222400 := by decide
  rcases family_descends (prefixWord ++ tailWord_222400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222444 : List Nat := [2, 2, 1, 1, 2, 5, 1, 4, 1, 1, 3]
def baseStart_222444 : Nat := 118140960795 + 222444 * 2 ^ 59
def prefixEnd_222444 : Nat := 4983230072969 + 3 ^ 40 * 222444 * 2
def baseEnd_222444 : Nat := 114220690708832920527005

theorem tailTrace_222444 : CollatzResearch.WordTrace tailWord_222444 prefixEnd_222444 114220690708832920527005 := by
  unfold tailWord_222444
  simp only [CollatzResearch.WordTrace]
  refine ⟨4056599603065426627869193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5408799470753902170492257 4056599603065426627869193)
  ·
    refine ⟨3042449702299069970901895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4056599603065426627869193 3042449702299069970901895)
    ·
      refine ⟨4563674553448604956352843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3042449702299069970901895 4563674553448604956352843)
      ·
        refine ⟨6845511830172907434529265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4563674553448604956352843 6845511830172907434529265)
        ·
          refine ⟨5134133872629680575896949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6845511830172907434529265 5134133872629680575896949)
          ·
            refine ⟨481325050559032553990339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5134133872629680575896949 481325050559032553990339)
            ·
              refine ⟨721987575838548830985509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481325050559032553990339 721987575838548830985509)
              ·
                refine ⟨135372670469727905809783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 721987575838548830985509 135372670469727905809783)
                ·
                  refine ⟨203059005704591858714675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135372670469727905809783 203059005704591858714675)
                  ·
                    refine ⟨304588508556887788072013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 203059005704591858714675 304588508556887788072013)
                    ·
                      refine ⟨114220690708832920527005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 304588508556887788072013 114220690708832920527005)
                      ·
                        rfl

theorem cell23_222444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4, 1, 1, 3].length) (baseStart_222444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222444 prefixEnd_222444 := by exact prefixLift 222444
  have htrace : WordTrace (prefixWord ++ tailWord_222444) baseStart_222444 baseEnd_222444 := by
    simpa [prefixWord, tailWord_222444, baseEnd_222444] using wordTrace_append hprefix tailTrace_222444
  have hstable : (prefixWord ++ tailWord_222444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222444).length < 2 ^ (prefixWord ++ tailWord_222444).sum := by decide
  have hdescent : baseEnd_222444 < baseStart_222444 := by decide
  rcases family_descends (prefixWord ++ tailWord_222444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222467 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 5, 2, 2]
def baseStart_222467 : Nat := 118140960795 + 222467 * 2 ^ 59
def prefixEnd_222467 : Nat := 4983230072969 + 3 ^ 40 * 222467 * 2
def baseEnd_222467 : Nat := 114232500763886330539399

theorem tailTrace_222467 : CollatzResearch.WordTrace tailWord_222467 prefixEnd_222467 114232500763886330539399 := by
  unfold tailWord_222467
  simp only [CollatzResearch.WordTrace]
  refine ⟨8114038085047528183825655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5409358723365018789217103 8114038085047528183825655)
  ·
    refine ⟨12171057127571292275738483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8114038085047528183825655 12171057127571292275738483)
    ·
      refine ⟨18256585691356938413607725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12171057127571292275738483 18256585691356938413607725)
      ·
        refine ⟨6846219634258851905102897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18256585691356938413607725 6846219634258851905102897)
        ·
          refine ⟨5134664725694138928827173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6846219634258851905102897 5134664725694138928827173)
          ·
            refine ⟨962749636067651049155095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5134664725694138928827173 962749636067651049155095)
            ·
              refine ⟨1444124454101476573732643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 962749636067651049155095 1444124454101476573732643)
              ·
                refine ⟨2166186681152214860598965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1444124454101476573732643 2166186681152214860598965)
                ·
                  refine ⟨203080001358020143181153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2166186681152214860598965 203080001358020143181153)
                  ·
                    refine ⟨152310001018515107385865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 203080001358020143181153 152310001018515107385865)
                    ·
                      refine ⟨114232500763886330539399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 152310001018515107385865 114232500763886330539399)
                      ·
                        rfl

theorem cell23_222467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5, 2, 2].length) (baseStart_222467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222467 prefixEnd_222467 := by exact prefixLift 222467
  have htrace : WordTrace (prefixWord ++ tailWord_222467) baseStart_222467 baseEnd_222467 := by
    simpa [prefixWord, tailWord_222467, baseEnd_222467] using wordTrace_append hprefix tailTrace_222467
  have hstable : (prefixWord ++ tailWord_222467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222467).length < 2 ^ (prefixWord ++ tailWord_222467).sum := by decide
  have hdescent : baseEnd_222467 < baseStart_222467 := by decide
  rcases family_descends (prefixWord ++ tailWord_222467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222487 : List Nat := [1, 1, 3, 4, 1, 1, 3, 3, 1, 2, 3]
def baseStart_222487 : Nat := 118140960795 + 222487 * 2 ^ 59
def prefixEnd_222487 : Nat := 4983230072969 + 3 ^ 40 * 222487 * 2
def baseEnd_222487 : Nat := 114242770376976252289307

theorem tailTrace_222487 : CollatzResearch.WordTrace tailWord_222487 prefixEnd_222487 114242770376976252289307 := by
  unfold tailWord_222487
  simp only [CollatzResearch.WordTrace]
  refine ⟨8114767544975071599553715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5409845029983381066369143 8114767544975071599553715)
  ·
    refine ⟨12172151317462607399330573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8114767544975071599553715 12172151317462607399330573)
    ·
      refine ⟨4564556744048477774748965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12172151317462607399330573 4564556744048477774748965)
      ·
        refine ⟨855854389509089582765431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4564556744048477774748965 855854389509089582765431)
        ·
          refine ⟨1283781584263634374148147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 855854389509089582765431 1283781584263634374148147)
          ·
            refine ⟨1925672376395451561222221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1283781584263634374148147 1925672376395451561222221)
            ·
              refine ⟨722127141148294335458333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1925672376395451561222221 722127141148294335458333)
              ·
                refine ⟨270797677930610375796875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 722127141148294335458333 270797677930610375796875)
                ·
                  refine ⟨406196516895915563695313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270797677930610375796875 406196516895915563695313)
                  ·
                    refine ⟨304647387671936672771485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 406196516895915563695313 304647387671936672771485)
                    ·
                      refine ⟨114242770376976252289307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 304647387671936672771485 114242770376976252289307)
                      ·
                        rfl

theorem cell23_222487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_222487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222487 prefixEnd_222487 := by exact prefixLift 222487
  have htrace : WordTrace (prefixWord ++ tailWord_222487) baseStart_222487 baseEnd_222487 := by
    simpa [prefixWord, tailWord_222487, baseEnd_222487] using wordTrace_append hprefix tailTrace_222487
  have hstable : (prefixWord ++ tailWord_222487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222487).length < 2 ^ (prefixWord ++ tailWord_222487).sum := by decide
  have hdescent : baseEnd_222487 < baseStart_222487 := by decide
  rcases family_descends (prefixWord ++ tailWord_222487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222501 : List Nat := [1, 3, 1, 2, 4, 1, 2, 4, 1, 2, 2]
def baseStart_222501 : Nat := 118140960795 + 222501 * 2 ^ 59
def prefixEnd_222501 : Nat := 4983230072969 + 3 ^ 40 * 222501 * 2
def baseEnd_222501 : Nat := 114249959106139197514243

theorem tailTrace_222501 : CollatzResearch.WordTrace tailWord_222501 prefixEnd_222501 114249959106139197514243 := by
  unfold tailWord_222501
  simp only [CollatzResearch.WordTrace]
  refine ⟨8115278166924351990563357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5410185444616234660375571 8115278166924351990563357)
  ·
    refine ⟨3043229312596631996461259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8115278166924351990563357 3043229312596631996461259)
    ·
      refine ⟨4564843968894947994691889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3043229312596631996461259 4564843968894947994691889)
      ·
        refine ⟨3423632976671210996018917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4564843968894947994691889 3423632976671210996018917)
        ·
          refine ⟨641931183125852061753547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3423632976671210996018917 641931183125852061753547)
          ·
            refine ⟨962896774688778092630321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641931183125852061753547 962896774688778092630321)
            ·
              refine ⟨722172581016583569472741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 962896774688778092630321 722172581016583569472741)
              ·
                refine ⟨135407358940609419276139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 722172581016583569472741 135407358940609419276139)
                ·
                  refine ⟨203111038410914128914209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135407358940609419276139 203111038410914128914209)
                  ·
                    refine ⟨152333278808185596685657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 203111038410914128914209 152333278808185596685657)
                    ·
                      refine ⟨114249959106139197514243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 152333278808185596685657 114249959106139197514243)
                      ·
                        rfl

theorem cell23_222501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4, 1, 2, 2].length) (baseStart_222501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222501 prefixEnd_222501 := by exact prefixLift 222501
  have htrace : WordTrace (prefixWord ++ tailWord_222501) baseStart_222501 baseEnd_222501 := by
    simpa [prefixWord, tailWord_222501, baseEnd_222501] using wordTrace_append hprefix tailTrace_222501
  have hstable : (prefixWord ++ tailWord_222501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222501).length < 2 ^ (prefixWord ++ tailWord_222501).sum := by decide
  have hdescent : baseEnd_222501 < baseStart_222501 := by decide
  rcases family_descends (prefixWord ++ tailWord_222501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222517 : List Nat := [1, 3, 3, 1, 2, 2, 3, 1, 1, 3, 3]
def baseStart_222517 : Nat := 118140960795 + 222517 * 2 ^ 59
def prefixEnd_222517 : Nat := 4983230072969 + 3 ^ 40 * 222517 * 2
def baseEnd_222517 : Nat := 114258174796611134914169

theorem tailTrace_222517 : CollatzResearch.WordTrace tailWord_222517 prefixEnd_222517 114258174796611134914169 := by
  unfold tailWord_222517
  simp only [CollatzResearch.WordTrace]
  refine ⟨8115861734866386723145805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5410574489910924482097203 8115861734866386723145805)
  ·
    refine ⟨3043448150574895021179677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8115861734866386723145805 3043448150574895021179677)
    ·
      refine ⟨1141293056465585632942379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3043448150574895021179677 1141293056465585632942379)
      ·
        refine ⟨1711939584698378449413569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1141293056465585632942379 1711939584698378449413569)
        ·
          refine ⟨1283954688523783837060177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1711939584698378449413569 1283954688523783837060177)
          ·
            refine ⟨962966016392837877795133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1283954688523783837060177 962966016392837877795133)
            ·
              refine ⟨361112256147314204173175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 962966016392837877795133 361112256147314204173175)
              ·
                refine ⟨541668384220971306259763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361112256147314204173175 541668384220971306259763)
                ·
                  refine ⟨812502576331456959389645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 541668384220971306259763 812502576331456959389645)
                  ·
                    refine ⟨304688466124296359771117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 812502576331456959389645 304688466124296359771117)
                    ·
                      refine ⟨114258174796611134914169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 304688466124296359771117 114258174796611134914169)
                      ·
                        rfl

theorem cell23_222517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_222517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222517 prefixEnd_222517 := by exact prefixLift 222517
  have htrace : WordTrace (prefixWord ++ tailWord_222517) baseStart_222517 baseEnd_222517 := by
    simpa [prefixWord, tailWord_222517, baseEnd_222517] using wordTrace_append hprefix tailTrace_222517
  have hstable : (prefixWord ++ tailWord_222517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222517).length < 2 ^ (prefixWord ++ tailWord_222517).sum := by decide
  have hdescent : baseEnd_222517 < baseStart_222517 := by decide
  rcases family_descends (prefixWord ++ tailWord_222517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222523 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 4]
def baseStart_222523 : Nat := 118140960795 + 222523 * 2 ^ 59
def prefixEnd_222523 : Nat := 4983230072969 + 3 ^ 40 * 222523 * 2
def baseEnd_222523 : Nat := 114261255680538111439141

theorem tailTrace_222523 : CollatzResearch.WordTrace tailWord_222523 prefixEnd_222523 114261255680538111439141 := by
  unfold tailWord_222523
  simp only [CollatzResearch.WordTrace]
  refine ⟨8116080572844649747864223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5410720381896433165242815 8116080572844649747864223)
  ·
    refine ⟨12174120859266974621796335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8116080572844649747864223 12174120859266974621796335)
    ·
      refine ⟨18261181288900461932694503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12174120859266974621796335 18261181288900461932694503)
      ·
        refine ⟨27391771933350692899041755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18261181288900461932694503 27391771933350692899041755)
        ·
          refine ⟨41087657900026039348562633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27391771933350692899041755 41087657900026039348562633)
          ·
            refine ⟨30815743425019529511421975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41087657900026039348562633 30815743425019529511421975)
            ·
              refine ⟨46223615137529294267132963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30815743425019529511421975 46223615137529294267132963)
              ·
                refine ⟨69335422706293941400699445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46223615137529294267132963 69335422706293941400699445)
                ·
                  refine ⟨6500195878715057006315573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69335422706293941400699445 6500195878715057006315573)
                  ·
                    refine ⟨609393363629536594342085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6500195878715057006315573 609393363629536594342085)
                    ·
                      refine ⟨114261255680538111439141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 609393363629536594342085 114261255680538111439141)
                      ·
                        rfl

theorem cell23_222523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 4].length) (baseStart_222523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222523 prefixEnd_222523 := by exact prefixLift 222523
  have htrace : WordTrace (prefixWord ++ tailWord_222523) baseStart_222523 baseEnd_222523 := by
    simpa [prefixWord, tailWord_222523, baseEnd_222523] using wordTrace_append hprefix tailTrace_222523
  have hstable : (prefixWord ++ tailWord_222523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222523).length < 2 ^ (prefixWord ++ tailWord_222523).sum := by decide
  have hdescent : baseEnd_222523 < baseStart_222523 := by decide
  rcases family_descends (prefixWord ++ tailWord_222523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222533 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 1, 8]
def baseStart_222533 : Nat := 118140960795 + 222533 * 2 ^ 59
def prefixEnd_222533 : Nat := 4983230072969 + 3 ^ 40 * 222533 * 2
def baseEnd_222533 : Nat := 38088796829027690771365

theorem tailTrace_222533 : CollatzResearch.WordTrace tailWord_222533 prefixEnd_222533 38088796829027690771365 := by
  unfold tailWord_222533
  simp only [CollatzResearch.WordTrace]
  refine ⟨8116445302808421455728253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5410963535205614303818835 8116445302808421455728253)
  ·
    refine ⟨3043666988553158045898095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8116445302808421455728253 3043666988553158045898095)
    ·
      refine ⟨4565500482829737068847143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3043666988553158045898095 4565500482829737068847143)
      ·
        refine ⟨6848250724244605603270715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4565500482829737068847143 6848250724244605603270715)
        ·
          refine ⟨10272376086366908404906073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6848250724244605603270715 10272376086366908404906073)
          ·
            refine ⟨7704282064775181303679555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10272376086366908404906073 7704282064775181303679555)
            ·
              refine ⟨11556423097162771955519333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7704282064775181303679555 11556423097162771955519333)
              ·
                refine ⟨2166829330718019741659875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11556423097162771955519333 2166829330718019741659875)
                ·
                  refine ⟨3250243996077029612489813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2166829330718019741659875 3250243996077029612489813)
                  ·
                    refine ⟨38088796829027690771365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3250243996077029612489813 38088796829027690771365)
                    ·
                      rfl

theorem cell23_222533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 8].length) (baseStart_222533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222533 prefixEnd_222533 := by exact prefixLift 222533
  have htrace : WordTrace (prefixWord ++ tailWord_222533) baseStart_222533 baseEnd_222533 := by
    simpa [prefixWord, tailWord_222533, baseEnd_222533] using wordTrace_append hprefix tailTrace_222533
  have hstable : (prefixWord ++ tailWord_222533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222533).length < 2 ^ (prefixWord ++ tailWord_222533).sum := by decide
  have hdescent : baseEnd_222533 < baseStart_222533 := by decide
  rcases family_descends (prefixWord ++ tailWord_222533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222568 : List Nat := [2, 1, 4, 2, 3, 2, 2, 1, 2, 1, 3]
def baseStart_222568 : Nat := 118140960795 + 222568 * 2 ^ 59
def prefixEnd_222568 : Nat := 4983230072969 + 3 ^ 40 * 222568 * 2
def baseEnd_222568 : Nat := 114284362309990435376435

theorem tailTrace_222568 : CollatzResearch.WordTrace tailWord_222568 prefixEnd_222568 114284362309990435376435 := by
  unfold tailWord_222568
  simp only [CollatzResearch.WordTrace]
  refine ⟨4058860928840811216626179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5411814571787748288834905 4058860928840811216626179)
  ·
    refine ⟨6088291393261216824939269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4058860928840811216626179 6088291393261216824939269)
    ·
      refine ⟨1141554636236478154676113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6088291393261216824939269 1141554636236478154676113)
      ·
        refine ⟨856165977177358616007085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1141554636236478154676113 856165977177358616007085)
        ·
          refine ⟨321062241441509481002657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 856165977177358616007085 321062241441509481002657)
          ·
            refine ⟨240796681081132110751993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321062241441509481002657 240796681081132110751993)
            ·
              refine ⟨180597510810849083063995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240796681081132110751993 180597510810849083063995)
              ·
                refine ⟨270896266216273624595993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180597510810849083063995 270896266216273624595993)
                ·
                  refine ⟨203172199662205218446995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270896266216273624595993 203172199662205218446995)
                  ·
                    refine ⟨304758299493307827670493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 203172199662205218446995 304758299493307827670493)
                    ·
                      refine ⟨114284362309990435376435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 304758299493307827670493 114284362309990435376435)
                      ·
                        rfl

theorem cell23_222568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_222568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222568 prefixEnd_222568 := by exact prefixLift 222568
  have htrace : WordTrace (prefixWord ++ tailWord_222568) baseStart_222568 baseEnd_222568 := by
    simpa [prefixWord, tailWord_222568, baseEnd_222568] using wordTrace_append hprefix tailTrace_222568
  have hstable : (prefixWord ++ tailWord_222568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222568).length < 2 ^ (prefixWord ++ tailWord_222568).sum := by decide
  have hdescent : baseEnd_222568 < baseStart_222568 := by decide
  rcases family_descends (prefixWord ++ tailWord_222568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222594 : List Nat := [3, 4, 2, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_222594 : Nat := 118140960795 + 222594 * 2 ^ 59
def prefixEnd_222594 : Nat := 4983230072969 + 3 ^ 40 * 222594 * 2
def baseEnd_222594 : Nat := 114297712807007333651315

theorem tailTrace_222594 : CollatzResearch.WordTrace tailWord_222594 prefixEnd_222594 114297712807007333651315 := by
  unfold tailWord_222594
  simp only [CollatzResearch.WordTrace]
  refine ⟨2029667538896857218424709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5412446770391619249132557 2029667538896857218424709)
  ·
    refine ⟨380562663543160728454633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2029667538896857218424709 380562663543160728454633)
    ·
      refine ⟨285421997657370546340975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380562663543160728454633 285421997657370546340975)
      ·
        refine ⟨428132996486055819511463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285421997657370546340975 428132996486055819511463)
        ·
          refine ⟨642199494729083729267195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428132996486055819511463 642199494729083729267195)
          ·
            refine ⟨963299242093625593900793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642199494729083729267195 963299242093625593900793)
            ·
              refine ⟨722474431570219195425595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 963299242093625593900793 722474431570219195425595)
              ·
                refine ⟨1083711647355328793138393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722474431570219195425595 1083711647355328793138393)
                ·
                  refine ⟨812783735516496594853795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1083711647355328793138393 812783735516496594853795)
                  ·
                    refine ⟨1219175603274744892280693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 812783735516496594853795 1219175603274744892280693)
                    ·
                      refine ⟨114297712807007333651315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1219175603274744892280693 114297712807007333651315)
                      ·
                        rfl

theorem cell23_222594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_222594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222594 prefixEnd_222594 := by exact prefixLift 222594
  have htrace : WordTrace (prefixWord ++ tailWord_222594) baseStart_222594 baseEnd_222594 := by
    simpa [prefixWord, tailWord_222594, baseEnd_222594] using wordTrace_append hprefix tailTrace_222594
  have hstable : (prefixWord ++ tailWord_222594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222594).length < 2 ^ (prefixWord ++ tailWord_222594).sum := by decide
  have hdescent : baseEnd_222594 < baseStart_222594 := by decide
  rcases family_descends (prefixWord ++ tailWord_222594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222617 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 2, 5, 2]
def baseStart_222617 : Nat := 118140960795 + 222617 * 2 ^ 59
def prefixEnd_222617 : Nat := 4983230072969 + 3 ^ 40 * 222617 * 2
def baseEnd_222617 : Nat := 114309522862060743663709

theorem tailTrace_222617 : CollatzResearch.WordTrace tailWord_222617 prefixEnd_222617 114309522862060743663709 := by
  unfold tailWord_222617
  simp only [CollatzResearch.WordTrace]
  refine ⟨8119509034504103801786105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5413006023002735867857403 8119509034504103801786105)
  ·
    refine ⟨6089631775878077851339579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8119509034504103801786105 6089631775878077851339579)
    ·
      refine ⟨9134447663817116777009369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6089631775878077851339579 9134447663817116777009369)
      ·
        refine ⟨6850835747862837582757027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9134447663817116777009369 6850835747862837582757027)
        ·
          refine ⟨10276253621794256374135541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6850835747862837582757027 10276253621794256374135541)
          ·
            refine ⟨963398777043211535075207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10276253621794256374135541 963398777043211535075207)
            ·
              refine ⟨1445098165564817302612811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 963398777043211535075207 1445098165564817302612811)
              ·
                refine ⟨2167647248347225953919217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1445098165564817302612811 2167647248347225953919217)
                ·
                  refine ⟨1625735436260419465439413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2167647248347225953919217 1625735436260419465439413)
                  ·
                    refine ⟨152412697149414324884945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1625735436260419465439413 152412697149414324884945)
                    ·
                      refine ⟨114309522862060743663709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 152412697149414324884945 114309522862060743663709)
                      ·
                        rfl

theorem cell23_222617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 5, 2].length) (baseStart_222617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222617 prefixEnd_222617 := by exact prefixLift 222617
  have htrace : WordTrace (prefixWord ++ tailWord_222617) baseStart_222617 baseEnd_222617 := by
    simpa [prefixWord, tailWord_222617, baseEnd_222617] using wordTrace_append hprefix tailTrace_222617
  have hstable : (prefixWord ++ tailWord_222617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222617).length < 2 ^ (prefixWord ++ tailWord_222617).sum := by decide
  have hdescent : baseEnd_222617 < baseStart_222617 := by decide
  rcases family_descends (prefixWord ++ tailWord_222617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222647 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 1, 6, 2]
def baseStart_222647 : Nat := 118140960795 + 222647 * 2 ^ 59
def prefixEnd_222647 : Nat := 4983230072969 + 3 ^ 40 * 222647 * 2
def baseEnd_222647 : Nat := 114324927281695626288571

theorem tailTrace_222647 : CollatzResearch.WordTrace tailWord_222647 prefixEnd_222647 114324927281695626288571 := by
  unfold tailWord_222647
  simp only [CollatzResearch.WordTrace]
  refine ⟨8120603224395418925378195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5413735482930279283585463 8120603224395418925378195)
  ·
    refine ⟨12180904836593128388067293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8120603224395418925378195 12180904836593128388067293)
    ·
      refine ⟨4567839313722423145525235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12180904836593128388067293 4567839313722423145525235)
      ·
        refine ⟨6851758970583634718287853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4567839313722423145525235 6851758970583634718287853)
        ·
          refine ⟨2569409613968863019357945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6851758970583634718287853 2569409613968863019357945)
          ·
            refine ⟨1927057210476647264518459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2569409613968863019357945 1927057210476647264518459)
            ·
              refine ⟨2890585815714970896777689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1927057210476647264518459 2890585815714970896777689)
              ·
                refine ⟨2167939361786228172583267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2890585815714970896777689 2167939361786228172583267)
                ·
                  refine ⟨3251909042679342258874901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2167939361786228172583267 3251909042679342258874901)
                  ·
                    refine ⟨152433236375594168384761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3251909042679342258874901 152433236375594168384761)
                    ·
                      refine ⟨114324927281695626288571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 152433236375594168384761 114324927281695626288571)
                      ·
                        rfl

theorem cell23_222647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 6, 2].length) (baseStart_222647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222647 prefixEnd_222647 := by exact prefixLift 222647
  have htrace : WordTrace (prefixWord ++ tailWord_222647) baseStart_222647 baseEnd_222647 := by
    simpa [prefixWord, tailWord_222647, baseEnd_222647] using wordTrace_append hprefix tailTrace_222647
  have hstable : (prefixWord ++ tailWord_222647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222647).length < 2 ^ (prefixWord ++ tailWord_222647).sum := by decide
  have hdescent : baseEnd_222647 < baseStart_222647 := by decide
  rcases family_descends (prefixWord ++ tailWord_222647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222667 : List Nat := [1, 1, 1, 1, 3, 3, 2, 4, 2, 2, 3]
def baseStart_222667 : Nat := 118140960795 + 222667 * 2 ^ 59
def prefixEnd_222667 : Nat := 4983230072969 + 3 ^ 40 * 222667 * 2
def baseEnd_222667 : Nat := 114335196894785548038479

theorem tailTrace_222667 : CollatzResearch.WordTrace tailWord_222667 prefixEnd_222667 114335196894785548038479 := by
  unfold tailWord_222667
  simp only [CollatzResearch.WordTrace]
  refine ⟨8121332684322962341106255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5414221789548641560737503 8121332684322962341106255)
  ·
    refine ⟨12181999026484443511659383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8121332684322962341106255 12181999026484443511659383)
    ·
      refine ⟨18272998539726665267489075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12181999026484443511659383 18272998539726665267489075)
      ·
        refine ⟨27409497809589997901233613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18272998539726665267489075 27409497809589997901233613)
        ·
          refine ⟨10278561678596249212962605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27409497809589997901233613 10278561678596249212962605)
          ·
            refine ⟨3854460629473593454860977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10278561678596249212962605 3854460629473593454860977)
            ·
              refine ⟨2890845472105195091145733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3854460629473593454860977 2890845472105195091145733)
              ·
                refine ⟨542033526019724079589825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2890845472105195091145733 542033526019724079589825)
                ·
                  refine ⟨406525144514793059692369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 542033526019724079589825 406525144514793059692369)
                  ·
                    refine ⟨304893858386094794769277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 406525144514793059692369 304893858386094794769277)
                    ·
                      refine ⟨114335196894785548038479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 304893858386094794769277 114335196894785548038479)
                      ·
                        rfl

theorem cell23_222667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2, 3].length) (baseStart_222667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222667 prefixEnd_222667 := by exact prefixLift 222667
  have htrace : WordTrace (prefixWord ++ tailWord_222667) baseStart_222667 baseEnd_222667 := by
    simpa [prefixWord, tailWord_222667, baseEnd_222667] using wordTrace_append hprefix tailTrace_222667
  have hstable : (prefixWord ++ tailWord_222667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222667).length < 2 ^ (prefixWord ++ tailWord_222667).sum := by decide
  have hdescent : baseEnd_222667 < baseStart_222667 := by decide
  rcases family_descends (prefixWord ++ tailWord_222667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222718 : List Nat := [4, 2, 2, 3, 1, 1, 1, 2, 2, 2, 3]
def baseStart_222718 : Nat := 118140960795 + 222718 * 2 ^ 59
def prefixEnd_222718 : Nat := 4983230072969 + 3 ^ 40 * 222718 * 2
def baseEnd_222718 : Nat := 114361384408164848500745

theorem tailTrace_222718 : CollatzResearch.WordTrace tailWord_222718 prefixEnd_222718 114361384408164848500745 := by
  unfold tailWord_222718
  simp only [CollatzResearch.WordTrace]
  refine ⟨1015399100892274756401601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5415461871425465367475205 1015399100892274756401601)
  ·
    refine ⟨761549325669206067301201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1015399100892274756401601 761549325669206067301201)
    ·
      refine ⟨571161994251904550475901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 761549325669206067301201 571161994251904550475901)
      ·
        refine ⟨214185747844464206428463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 571161994251904550475901 214185747844464206428463)
        ·
          refine ⟨321278621766696309642695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214185747844464206428463 321278621766696309642695)
          ·
            refine ⟨481917932650044464464043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321278621766696309642695 481917932650044464464043)
            ·
              refine ⟨722876898975066696696065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481917932650044464464043 722876898975066696696065)
              ·
                refine ⟨542157674231300022522049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 722876898975066696696065 542157674231300022522049)
                ·
                  refine ⟨406618255673475016891537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 542157674231300022522049 406618255673475016891537)
                  ·
                    refine ⟨304963691755106262668653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 406618255673475016891537 304963691755106262668653)
                    ·
                      refine ⟨114361384408164848500745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 304963691755106262668653 114361384408164848500745)
                      ·
                        rfl

theorem cell23_222718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_222718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222718 prefixEnd_222718 := by exact prefixLift 222718
  have htrace : WordTrace (prefixWord ++ tailWord_222718) baseStart_222718 baseEnd_222718 := by
    simpa [prefixWord, tailWord_222718, baseEnd_222718] using wordTrace_append hprefix tailTrace_222718
  have hstable : (prefixWord ++ tailWord_222718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222718).length < 2 ^ (prefixWord ++ tailWord_222718).sum := by decide
  have hdescent : baseEnd_222718 < baseStart_222718 := by decide
  rcases family_descends (prefixWord ++ tailWord_222718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222737 : List Nat := [1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 4]
def baseStart_222737 : Nat := 118140960795 + 222737 * 2 ^ 59
def prefixEnd_222737 : Nat := 4983230072969 + 3 ^ 40 * 222737 * 2
def baseEnd_222737 : Nat := 114371140540600274163157

theorem tailTrace_222737 : CollatzResearch.WordTrace tailWord_222737 prefixEnd_222737 114371140540600274163157 := by
  unfold tailWord_222737
  simp only [CollatzResearch.WordTrace]
  refine ⟨8123885794069364296154465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5415923862712909530769643 8123885794069364296154465)
  ·
    refine ⟨6092914345552023222115849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8123885794069364296154465 6092914345552023222115849)
    ·
      refine ⟨4569685759164017416586887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6092914345552023222115849 4569685759164017416586887)
      ·
        refine ⟨6854528638746026124880331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4569685759164017416586887 6854528638746026124880331)
        ·
          refine ⟨10281792958119039187320497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6854528638746026124880331 10281792958119039187320497)
          ·
            refine ⟨7711344718589279390490373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10281792958119039187320497 7711344718589279390490373)
            ·
              refine ⟨1445877134735489885716945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7711344718589279390490373 1445877134735489885716945)
              ·
                refine ⟨1084407851051617414287709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1445877134735489885716945 1084407851051617414287709)
                ·
                  refine ⟨406652944144356530357891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1084407851051617414287709 406652944144356530357891)
                  ·
                    refine ⟨609979416216534795536837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 406652944144356530357891 609979416216534795536837)
                    ·
                      refine ⟨114371140540600274163157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 609979416216534795536837 114371140540600274163157)
                      ·
                        rfl

theorem cell23_222737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_222737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222737 prefixEnd_222737 := by exact prefixLift 222737
  have htrace : WordTrace (prefixWord ++ tailWord_222737) baseStart_222737 baseEnd_222737 := by
    simpa [prefixWord, tailWord_222737, baseEnd_222737] using wordTrace_append hprefix tailTrace_222737
  have hstable : (prefixWord ++ tailWord_222737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222737).length < 2 ^ (prefixWord ++ tailWord_222737).sum := by decide
  have hdescent : baseEnd_222737 < baseStart_222737 := by decide
  rcases family_descends (prefixWord ++ tailWord_222737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222754 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 2, 6, 2]
def baseStart_222754 : Nat := 118140960795 + 222754 * 2 ^ 59
def prefixEnd_222754 : Nat := 4983230072969 + 3 ^ 40 * 222754 * 2
def baseEnd_222754 : Nat := 114379869711726707650579

theorem tailTrace_222754 : CollatzResearch.WordTrace tailWord_222754 prefixEnd_222754 114379869711726707650579 := by
  unfold tailWord_222754
  simp only [CollatzResearch.WordTrace]
  refine ⟨2031126458751944049880829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5416337223338517466348877 2031126458751944049880829)
  ·
    refine ⟨761672422031979018705311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2031126458751944049880829 761672422031979018705311)
    ·
      refine ⟨1142508633047968528057967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 761672422031979018705311 1142508633047968528057967)
      ·
        refine ⟨1713762949571952792086951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1142508633047968528057967 1713762949571952792086951)
        ·
          refine ⟨2570644424357929188130427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1713762949571952792086951 2570644424357929188130427)
          ·
            refine ⟨3855966636536893782195641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2570644424357929188130427 3855966636536893782195641)
            ·
              refine ⟨2891974977402670336646731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3855966636536893782195641 2891974977402670336646731)
              ·
                refine ⟨4337962466104005504970097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2891974977402670336646731 4337962466104005504970097)
                ·
                  refine ⟨3253471849578004128727573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4337962466104005504970097 3253471849578004128727573)
                  ·
                    refine ⟨152506492948968943534105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3253471849578004128727573 152506492948968943534105)
                    ·
                      refine ⟨114379869711726707650579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 152506492948968943534105 114379869711726707650579)
                      ·
                        rfl

theorem cell23_222754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_222754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222754 prefixEnd_222754 := by exact prefixLift 222754
  have htrace : WordTrace (prefixWord ++ tailWord_222754) baseStart_222754 baseEnd_222754 := by
    simpa [prefixWord, tailWord_222754, baseEnd_222754] using wordTrace_append hprefix tailTrace_222754
  have hstable : (prefixWord ++ tailWord_222754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222754).length < 2 ^ (prefixWord ++ tailWord_222754).sum := by decide
  have hdescent : baseEnd_222754 < baseStart_222754 := by decide
  rcases family_descends (prefixWord ++ tailWord_222754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222771 : List Nat := [1, 1, 1, 2, 4, 4, 3, 1, 1, 1, 4]
def baseStart_222771 : Nat := 118140960795 + 222771 * 2 ^ 59
def prefixEnd_222771 : Nat := 4983230072969 + 3 ^ 40 * 222771 * 2
def baseEnd_222771 : Nat := 114388598882853141138001

theorem tailTrace_222771 : CollatzResearch.WordTrace tailWord_222771 prefixEnd_222771 114388598882853141138001 := by
  unfold tailWord_222771
  simp only [CollatzResearch.WordTrace]
  refine ⟨8125125875946188102892167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5416750583964125401928111 8125125875946188102892167)
  ·
    refine ⟨12187688813919282154338251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8125125875946188102892167 12187688813919282154338251)
    ·
      refine ⟨18281533220878923231507377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12187688813919282154338251 18281533220878923231507377)
      ·
        refine ⟨13711149915659192423630533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18281533220878923231507377 13711149915659192423630533)
        ·
          refine ⟨2570840609186098579430725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13711149915659192423630533 2570840609186098579430725)
          ·
            refine ⟨482032614222393483643261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2570840609186098579430725 482032614222393483643261)
            ·
              refine ⟨180762230333397556366223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 482032614222393483643261 180762230333397556366223)
              ·
                refine ⟨271143345500096334549335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180762230333397556366223 271143345500096334549335)
                ·
                  refine ⟨406715018250144501824003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271143345500096334549335 406715018250144501824003)
                  ·
                    refine ⟨610072527375216752736005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 406715018250144501824003 610072527375216752736005)
                    ·
                      refine ⟨114388598882853141138001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 610072527375216752736005 114388598882853141138001)
                      ·
                        rfl

theorem cell23_222771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 1, 1, 4].length) (baseStart_222771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222771 prefixEnd_222771 := by exact prefixLift 222771
  have htrace : WordTrace (prefixWord ++ tailWord_222771) baseStart_222771 baseEnd_222771 := by
    simpa [prefixWord, tailWord_222771, baseEnd_222771] using wordTrace_append hprefix tailTrace_222771
  have hstable : (prefixWord ++ tailWord_222771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222771).length < 2 ^ (prefixWord ++ tailWord_222771).sum := by decide
  have hdescent : baseEnd_222771 < baseStart_222771 := by decide
  rcases family_descends (prefixWord ++ tailWord_222771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222817 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 2, 2, 5]
def baseStart_222817 : Nat := 118140960795 + 222817 * 2 ^ 59
def prefixEnd_222817 : Nat := 4983230072969 + 3 ^ 40 * 222817 * 2
def baseEnd_222817 : Nat := 114412218992959961162789

theorem tailTrace_222817 : CollatzResearch.WordTrace tailWord_222817 prefixEnd_222817 114412218992959961162789 := by
  unfold tailWord_222817
  simp only [CollatzResearch.WordTrace]
  refine ⟨8126803633779537959066705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5417869089186358639377803 8126803633779537959066705)
  ·
    refine ⟨6095102725334653469300029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8126803633779537959066705 6095102725334653469300029)
    ·
      refine ⟨2285663522000495050987511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6095102725334653469300029 2285663522000495050987511)
      ·
        refine ⟨3428495283000742576481267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2285663522000495050987511 3428495283000742576481267)
        ·
          refine ⟨5142742924501113864721901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3428495283000742576481267 5142742924501113864721901)
          ·
            refine ⟨1928528596687917699270713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5142742924501113864721901 1928528596687917699270713)
            ·
              refine ⟨1446396447515938274453035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1928528596687917699270713 1446396447515938274453035)
              ·
                refine ⟨2169594671273907411679553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1446396447515938274453035 2169594671273907411679553)
                ·
                  refine ⟨1627196003455430558759665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2169594671273907411679553 1627196003455430558759665)
                  ·
                    refine ⟨1220397002591572919069749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1627196003455430558759665 1220397002591572919069749)
                    ·
                      refine ⟨114412218992959961162789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1220397002591572919069749 114412218992959961162789)
                      ·
                        rfl

theorem cell23_222817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_222817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222817 prefixEnd_222817 := by exact prefixLift 222817
  have htrace : WordTrace (prefixWord ++ tailWord_222817) baseStart_222817 baseEnd_222817 := by
    simpa [prefixWord, tailWord_222817, baseEnd_222817] using wordTrace_append hprefix tailTrace_222817
  have hstable : (prefixWord ++ tailWord_222817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222817).length < 2 ^ (prefixWord ++ tailWord_222817).sum := by decide
  have hdescent : baseEnd_222817 < baseStart_222817 := by decide
  rcases family_descends (prefixWord ++ tailWord_222817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222838 : List Nat := [5, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3]
def baseStart_222838 : Nat := 118140960795 + 222838 * 2 ^ 59
def prefixEnd_222838 : Nat := 4983230072969 + 3 ^ 40 * 222838 * 2
def baseEnd_222838 : Nat := 114423002086704379000193

theorem tailTrace_222838 : CollatzResearch.WordTrace tailWord_222838 prefixEnd_222838 114423002086704379000193 := by
  unfold tailWord_222838
  simp only [CollatzResearch.WordTrace]
  refine ⟨507973097918966159098823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5418379711135639030387445 507973097918966159098823)
  ·
    refine ⟨761959646878449238648235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 507973097918966159098823 761959646878449238648235)
    ·
      refine ⟨1142939470317673857972353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 761959646878449238648235 1142939470317673857972353)
      ·
        refine ⟨857204602738255393479265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1142939470317673857972353 857204602738255393479265)
        ·
          refine ⟨642903452053691545109449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 857204602738255393479265 642903452053691545109449)
          ·
            refine ⟨482177589040268658832087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 642903452053691545109449 482177589040268658832087)
            ·
              refine ⟨723266383560402988248131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482177589040268658832087 723266383560402988248131)
              ·
                refine ⟨1084899575340604482372197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 723266383560402988248131 1084899575340604482372197)
                ·
                  refine ⟨203418670376363340444787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1084899575340604482372197 203418670376363340444787)
                  ·
                    refine ⟨305128005564545010667181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 203418670376363340444787 305128005564545010667181)
                    ·
                      refine ⟨114423002086704379000193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 305128005564545010667181 114423002086704379000193)
                      ·
                        rfl

theorem cell23_222838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_222838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222838 prefixEnd_222838 := by exact prefixLift 222838
  have htrace : WordTrace (prefixWord ++ tailWord_222838) baseStart_222838 baseEnd_222838 := by
    simpa [prefixWord, tailWord_222838, baseEnd_222838] using wordTrace_append hprefix tailTrace_222838
  have hstable : (prefixWord ++ tailWord_222838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222838).length < 2 ^ (prefixWord ++ tailWord_222838).sum := by decide
  have hdescent : baseEnd_222838 < baseStart_222838 := by decide
  rcases family_descends (prefixWord ++ tailWord_222838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222927 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 2, 8]
def baseStart_222927 : Nat := 118140960795 + 222927 * 2 ^ 59
def prefixEnd_222927 : Nat := 4983230072969 + 3 ^ 40 * 222927 * 2
def baseEnd_222927 : Nat := 38156233954984843595761

theorem tailTrace_222927 : CollatzResearch.WordTrace tailWord_222927 prefixEnd_222927 38156233954984843595761 := by
  unfold tailWord_222927
  simp only [CollatzResearch.WordTrace]
  refine ⟨8130815663381026745571035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5420543775587351163714023 8130815663381026745571035)
  ·
    refine ⟨12196223495071540118356553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8130815663381026745571035 12196223495071540118356553)
    ·
      refine ⟨9147167621303655088767415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12196223495071540118356553 9147167621303655088767415)
      ·
        refine ⟨13720751431955482633151123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9147167621303655088767415 13720751431955482633151123)
        ·
          refine ⟨20581127147933223949726685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13720751431955482633151123 20581127147933223949726685)
          ·
            refine ⟨7717922680474958981147507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20581127147933223949726685 7717922680474958981147507)
            ·
              refine ⟨11576884020712438471721261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7717922680474958981147507 11576884020712438471721261)
              ·
                refine ⟨4341331507767164426895473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11576884020712438471721261 4341331507767164426895473)
                ·
                  refine ⟨3255998630825373320171605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4341331507767164426895473 3255998630825373320171605)
                  ·
                    refine ⟨38156233954984843595761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3255998630825373320171605 38156233954984843595761)
                    ·
                      rfl

theorem cell23_222927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 8].length) (baseStart_222927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222927 prefixEnd_222927 := by exact prefixLift 222927
  have htrace : WordTrace (prefixWord ++ tailWord_222927) baseStart_222927 baseEnd_222927 := by
    simpa [prefixWord, tailWord_222927, baseEnd_222927] using wordTrace_append hprefix tailTrace_222927
  have hstable : (prefixWord ++ tailWord_222927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222927).length < 2 ^ (prefixWord ++ tailWord_222927).sum := by decide
  have hdescent : baseEnd_222927 < baseStart_222927 := by decide
  rcases family_descends (prefixWord ++ tailWord_222927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222978 : List Nat := [3, 4, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_222978 : Nat := 118140960795 + 222978 * 2 ^ 59
def prefixEnd_222978 : Nat := 4983230072969 + 3 ^ 40 * 222978 * 2
def baseEnd_222978 : Nat := 38164963126111277083183

theorem tailTrace_222978 : CollatzResearch.WordTrace tailWord_222978 prefixEnd_222978 38164963126111277083183 := by
  unfold tailWord_222978
  simp only [CollatzResearch.WordTrace]
  refine ⟨2033168946549065613919397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5421783857464174970451725 2033168946549065613919397)
  ·
    refine ⟨381219177477949802609887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2033168946549065613919397 381219177477949802609887)
    ·
      refine ⟨571828766216924703914831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381219177477949802609887 571828766216924703914831)
      ·
        refine ⟨857743149325387055872247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571828766216924703914831 857743149325387055872247)
        ·
          refine ⟨1286614723988080583808371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 857743149325387055872247 1286614723988080583808371)
          ·
            refine ⟨1929922085982120875712557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1286614723988080583808371 1929922085982120875712557)
            ·
              refine ⟨723720782243295328392209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1929922085982120875712557 723720782243295328392209)
              ·
                refine ⟨542790586682471496294157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 723720782243295328392209 542790586682471496294157)
                ·
                  refine ⟨203546470005926811110309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 542790586682471496294157 203546470005926811110309)
                  ·
                    refine ⟨38164963126111277083183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 203546470005926811110309 38164963126111277083183)
                    ·
                      rfl

theorem cell23_222978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_222978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_222978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_222978 prefixEnd_222978 := by exact prefixLift 222978
  have htrace : WordTrace (prefixWord ++ tailWord_222978) baseStart_222978 baseEnd_222978 := by
    simpa [prefixWord, tailWord_222978, baseEnd_222978] using wordTrace_append hprefix tailTrace_222978
  have hstable : (prefixWord ++ tailWord_222978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222978).length < 2 ^ (prefixWord ++ tailWord_222978).sum := by decide
  have hdescent : baseEnd_222978 < baseStart_222978 := by decide
  rcases family_descends (prefixWord ++ tailWord_222978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223038 : List Nat := [4, 2, 1, 2, 2, 1, 1, 4, 1, 5]
def baseStart_223038 : Nat := 118140960795 + 223038 * 2 ^ 59
def prefixEnd_223038 : Nat := 4983230072969 + 3 ^ 40 * 223038 * 2
def baseEnd_223038 : Nat := 38175232739201198833091

theorem tailTrace_223038 : CollatzResearch.WordTrace tailWord_223038 prefixEnd_223038 38175232739201198833091 := by
  unfold tailWord_223038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1016858020747361587857721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5423242777319261801907845 1016858020747361587857721)
  ·
    refine ⟨762643515560521190893291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1016858020747361587857721 762643515560521190893291)
    ·
      refine ⟨1143965273340781786339937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 762643515560521190893291 1143965273340781786339937)
      ·
        refine ⟨857973955005586339754953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1143965273340781786339937 857973955005586339754953)
        ·
          refine ⟨643480466254189754816215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 857973955005586339754953 643480466254189754816215)
          ·
            refine ⟨965220699381284632224323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643480466254189754816215 965220699381284632224323)
            ·
              refine ⟨1447831049071926948336485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965220699381284632224323 1447831049071926948336485)
              ·
                refine ⟨271468321700986302813091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1447831049071926948336485 271468321700986302813091)
                ·
                  refine ⟨407202482551479454219637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271468321700986302813091 407202482551479454219637)
                  ·
                    refine ⟨38175232739201198833091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 407202482551479454219637 38175232739201198833091)
                    ·
                      rfl

theorem cell23_223038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_223038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223038 prefixEnd_223038 := by exact prefixLift 223038
  have htrace : WordTrace (prefixWord ++ tailWord_223038) baseStart_223038 baseEnd_223038 := by
    simpa [prefixWord, tailWord_223038, baseEnd_223038] using wordTrace_append hprefix tailTrace_223038
  have hstable : (prefixWord ++ tailWord_223038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223038).length < 2 ^ (prefixWord ++ tailWord_223038).sum := by decide
  have hdescent : baseEnd_223038 < baseStart_223038 := by decide
  rcases family_descends (prefixWord ++ tailWord_223038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223058 : List Nat := [3, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4]
def baseStart_223058 : Nat := 118140960795 + 223058 * 2 ^ 59
def prefixEnd_223058 : Nat := 4983230072969 + 3 ^ 40 * 223058 * 2
def baseEnd_223058 : Nat := 114535967830693518249181

theorem tailTrace_223058 : CollatzResearch.WordTrace tailWord_223058 prefixEnd_223058 114535967830693518249181 := by
  unfold tailWord_223058
  simp only [CollatzResearch.WordTrace]
  refine ⟨2033898406476609029647457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5423729083937624079059885 2033898406476609029647457)
  ·
    refine ⟨1525423804857456772235593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2033898406476609029647457 1525423804857456772235593)
    ·
      refine ⟨1144067853643092579176695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1525423804857456772235593 1144067853643092579176695)
      ·
        refine ⟨1716101780464638868765043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1144067853643092579176695 1716101780464638868765043)
        ·
          refine ⟨2574152670696958303147565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1716101780464638868765043 2574152670696958303147565)
          ·
            refine ⟨965307251511359363680337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2574152670696958303147565 965307251511359363680337)
            ·
              refine ⟨723980438633519522760253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 965307251511359363680337 723980438633519522760253)
              ·
                refine ⟨271492664487569821035095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 723980438633519522760253 271492664487569821035095)
                ·
                  refine ⟨407238996731354731552643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271492664487569821035095 407238996731354731552643)
                  ·
                    refine ⟨610858495097032097328965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 407238996731354731552643 610858495097032097328965)
                    ·
                      refine ⟨114535967830693518249181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 610858495097032097328965 114535967830693518249181)
                      ·
                        rfl

theorem cell23_223058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_223058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223058 prefixEnd_223058 := by exact prefixLift 223058
  have htrace : WordTrace (prefixWord ++ tailWord_223058) baseStart_223058 baseEnd_223058 := by
    simpa [prefixWord, tailWord_223058, baseEnd_223058] using wordTrace_append hprefix tailTrace_223058
  have hstable : (prefixWord ++ tailWord_223058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223058).length < 2 ^ (prefixWord ++ tailWord_223058).sum := by decide
  have hdescent : baseEnd_223058 < baseStart_223058 := by decide
  rcases family_descends (prefixWord ++ tailWord_223058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223061 : List Nat := [1, 3, 2, 2, 2, 2, 1, 3, 1, 1, 5]
def baseStart_223061 : Nat := 118140960795 + 223061 * 2 ^ 59
def prefixEnd_223061 : Nat := 4983230072969 + 3 ^ 40 * 223061 * 2
def baseEnd_223061 : Nat := 114537508272657006511667

theorem tailTrace_223061 : CollatzResearch.WordTrace tailWord_223061 prefixEnd_223061 114537508272657006511667 := by
  unfold tailWord_223061
  simp only [CollatzResearch.WordTrace]
  refine ⟨8135703044895567630949037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5423802029930378420632691 8135703044895567630949037)
  ·
    refine ⟨3050888641835837861605889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8135703044895567630949037 3050888641835837861605889)
    ·
      refine ⟨2288166481376878396204417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3050888641835837861605889 2288166481376878396204417)
      ·
        refine ⟨1716124861032658797153313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2288166481376878396204417 1716124861032658797153313)
        ·
          refine ⟨1287093645774494097864985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1716124861032658797153313 1287093645774494097864985)
          ·
            refine ⟨965320234330870573398739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1287093645774494097864985 965320234330870573398739)
            ·
              refine ⟨1447980351496305860098109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965320234330870573398739 1447980351496305860098109)
              ·
                refine ⟨542992631811114697536791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1447980351496305860098109 542992631811114697536791)
                ·
                  refine ⟨814488947716672046305187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 542992631811114697536791 814488947716672046305187)
                  ·
                    refine ⟨1221733421575008069457781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 814488947716672046305187 1221733421575008069457781)
                    ·
                      refine ⟨114537508272657006511667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1221733421575008069457781 114537508272657006511667)
                      ·
                        rfl

theorem cell23_223061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_223061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223061 prefixEnd_223061 := by exact prefixLift 223061
  have htrace : WordTrace (prefixWord ++ tailWord_223061) baseStart_223061 baseEnd_223061 := by
    simpa [prefixWord, tailWord_223061, baseEnd_223061] using wordTrace_append hprefix tailTrace_223061
  have hstable : (prefixWord ++ tailWord_223061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223061).length < 2 ^ (prefixWord ++ tailWord_223061).sum := by decide
  have hdescent : baseEnd_223061 < baseStart_223061 := by decide
  rcases family_descends (prefixWord ++ tailWord_223061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223085 : List Nat := [1, 5, 1, 1, 1, 1, 6, 1, 2, 4]
def baseStart_223085 : Nat := 118140960795 + 223085 * 2 ^ 59
def prefixEnd_223085 : Nat := 4983230072969 + 3 ^ 40 * 223085 * 2
def baseEnd_223085 : Nat := 38183277269454970870519

theorem tailTrace_223085 : CollatzResearch.WordTrace tailWord_223085 prefixEnd_223085 38183277269454970870519 := by
  unfold tailWord_223085
  simp only [CollatzResearch.WordTrace]
  refine ⟨8136578396808619729822709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5424385597872413153215139 8136578396808619729822709)
  ·
    refine ⟨762804224700808099670879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8136578396808619729822709 762804224700808099670879)
    ·
      refine ⟨1144206337051212149506319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 762804224700808099670879 1144206337051212149506319)
      ·
        refine ⟨1716309505576818224259479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1144206337051212149506319 1716309505576818224259479)
        ·
          refine ⟨2574464258365227336389219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1716309505576818224259479 2574464258365227336389219)
          ·
            refine ⟨3861696387547841004583829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2574464258365227336389219 3861696387547841004583829)
            ·
              refine ⟨181017018166305047089867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3861696387547841004583829 181017018166305047089867)
              ·
                refine ⟨271525527249457570634801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181017018166305047089867 271525527249457570634801)
                ·
                  refine ⟨203644145437093177976101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 271525527249457570634801 203644145437093177976101)
                  ·
                    refine ⟨38183277269454970870519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 203644145437093177976101 38183277269454970870519)
                    ·
                      rfl

theorem cell23_223085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_223085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223085 prefixEnd_223085 := by exact prefixLift 223085
  have htrace : WordTrace (prefixWord ++ tailWord_223085) baseStart_223085 baseEnd_223085 := by
    simpa [prefixWord, tailWord_223085, baseEnd_223085] using wordTrace_append hprefix tailTrace_223085
  have hstable : (prefixWord ++ tailWord_223085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223085).length < 2 ^ (prefixWord ++ tailWord_223085).sum := by decide
  have hdescent : baseEnd_223085 < baseStart_223085 := by decide
  rcases family_descends (prefixWord ++ tailWord_223085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223091 : List Nat := [1, 1, 1, 2, 2, 1, 3, 5, 1, 3, 3]
def baseStart_223091 : Nat := 118140960795 + 223091 * 2 ^ 59
def prefixEnd_223091 : Nat := 4983230072969 + 3 ^ 40 * 223091 * 2
def baseEnd_223091 : Nat := 114552912692291889136529

theorem tailTrace_223091 : CollatzResearch.WordTrace tailWord_223091 prefixEnd_223091 114552912692291889136529 := by
  unfold tailWord_223091
  simp only [CollatzResearch.WordTrace]
  refine ⟨8136797234786882754541127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5424531489857921836360751 8136797234786882754541127)
  ·
    refine ⟨12205195852180324131811691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8136797234786882754541127 12205195852180324131811691)
    ·
      refine ⟨18307793778270486197717537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12205195852180324131811691 18307793778270486197717537)
      ·
        refine ⟨13730845333702864648288153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18307793778270486197717537 13730845333702864648288153)
        ·
          refine ⟨10298134000277148486216115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13730845333702864648288153 10298134000277148486216115)
          ·
            refine ⟨15447201000415722729324173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10298134000277148486216115 15447201000415722729324173)
            ·
              refine ⟨5792700375155896023496565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15447201000415722729324173 5792700375155896023496565)
              ·
                refine ⟨543065660170865252202803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5792700375155896023496565 543065660170865252202803)
                ·
                  refine ⟨814598490256297878304205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 543065660170865252202803 814598490256297878304205)
                  ·
                    refine ⟨305474433846111704364077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 814598490256297878304205 305474433846111704364077)
                    ·
                      refine ⟨114552912692291889136529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 305474433846111704364077 114552912692291889136529)
                      ·
                        rfl

theorem cell23_223091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3, 3].length) (baseStart_223091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223091 prefixEnd_223091 := by exact prefixLift 223091
  have htrace : WordTrace (prefixWord ++ tailWord_223091) baseStart_223091 baseEnd_223091 := by
    simpa [prefixWord, tailWord_223091, baseEnd_223091] using wordTrace_append hprefix tailTrace_223091
  have hstable : (prefixWord ++ tailWord_223091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223091).length < 2 ^ (prefixWord ++ tailWord_223091).sum := by decide
  have hdescent : baseEnd_223091 < baseStart_223091 := by decide
  rcases family_descends (prefixWord ++ tailWord_223091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223105 : List Nat := [1, 2, 4, 4, 1, 1, 1, 2, 1, 2, 4]
def baseStart_223105 : Nat := 118140960795 + 223105 * 2 ^ 59
def prefixEnd_223105 : Nat := 4983230072969 + 3 ^ 40 * 223105 * 2
def baseEnd_223105 : Nat := 114560101421454834361465

theorem tailTrace_223105 : CollatzResearch.WordTrace tailWord_223105 prefixEnd_223105 114560101421454834361465 := by
  unfold tailWord_223105
  simp only [CollatzResearch.WordTrace]
  refine ⟨8137307856736163145550769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5424871904490775430367179 8137307856736163145550769)
  ·
    refine ⟨6102980892552122359163077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8137307856736163145550769 6102980892552122359163077)
    ·
      refine ⟨1144308917353522942343077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6102980892552122359163077 1144308917353522942343077)
      ·
        refine ⟨214557922003785551689327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1144308917353522942343077 214557922003785551689327)
        ·
          refine ⟨321836883005678327533991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214557922003785551689327 321836883005678327533991)
          ·
            refine ⟨482755324508517491300987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321836883005678327533991 482755324508517491300987)
            ·
              refine ⟨724132986762776236951481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482755324508517491300987 724132986762776236951481)
              ·
                refine ⟨543099740072082177713611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 724132986762776236951481 543099740072082177713611)
                ·
                  refine ⟨814649610108123266570417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 543099740072082177713611 814649610108123266570417)
                  ·
                    refine ⟨610987207581092449927813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 814649610108123266570417 610987207581092449927813)
                    ·
                      refine ⟨114560101421454834361465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 610987207581092449927813 114560101421454834361465)
                      ·
                        rfl

theorem cell23_223105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_223105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223105 prefixEnd_223105 := by exact prefixLift 223105
  have htrace : WordTrace (prefixWord ++ tailWord_223105) baseStart_223105 baseEnd_223105 := by
    simpa [prefixWord, tailWord_223105, baseEnd_223105] using wordTrace_append hprefix tailTrace_223105
  have hstable : (prefixWord ++ tailWord_223105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223105).length < 2 ^ (prefixWord ++ tailWord_223105).sum := by decide
  have hdescent : baseEnd_223105 < baseStart_223105 := by decide
  rcases family_descends (prefixWord ++ tailWord_223105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223108 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 6, 1, 3]
def baseStart_223108 : Nat := 118140960795 + 223108 * 2 ^ 59
def prefixEnd_223108 : Nat := 4983230072969 + 3 ^ 40 * 223108 * 2
def baseEnd_223108 : Nat := 114561641863418322623951

theorem tailTrace_223108 : CollatzResearch.WordTrace tailWord_223108 prefixEnd_223108 114561641863418322623951 := by
  unfold tailWord_223108
  simp only [CollatzResearch.WordTrace]
  refine ⟨4068708637862647328954989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5424944850483529771939985 4068708637862647328954989)
  ·
    refine ⟨1525765739198492748358121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4068708637862647328954989 1525765739198492748358121)
    ·
      refine ⟨1144324304398869561268591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1525765739198492748358121 1144324304398869561268591)
      ·
        refine ⟨1716486456598304341902887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1144324304398869561268591 1716486456598304341902887)
        ·
          refine ⟨2574729684897456512854331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1716486456598304341902887 2574729684897456512854331)
          ·
            refine ⟨3862094527346184769281497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2574729684897456512854331 3862094527346184769281497)
            ·
              refine ⟨2896570895509638576961123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3862094527346184769281497 2896570895509638576961123)
              ·
                refine ⟨4344856343264457865441685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2896570895509638576961123 4344856343264457865441685)
                ·
                  refine ⟨203665141090521462442579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4344856343264457865441685 203665141090521462442579)
                  ·
                    refine ⟨305497711635782193663869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 203665141090521462442579 305497711635782193663869)
                    ·
                      refine ⟨114561641863418322623951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 305497711635782193663869 114561641863418322623951)
                      ·
                        rfl

theorem cell23_223108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_223108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223108 prefixEnd_223108 := by exact prefixLift 223108
  have htrace : WordTrace (prefixWord ++ tailWord_223108) baseStart_223108 baseEnd_223108 := by
    simpa [prefixWord, tailWord_223108, baseEnd_223108] using wordTrace_append hprefix tailTrace_223108
  have hstable : (prefixWord ++ tailWord_223108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223108).length < 2 ^ (prefixWord ++ tailWord_223108).sum := by decide
  have hdescent : baseEnd_223108 < baseStart_223108 := by decide
  rcases family_descends (prefixWord ++ tailWord_223108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223112 : List Nat := [2, 1, 3, 3, 3, 1, 3, 1, 1, 2, 3]
def baseStart_223112 : Nat := 118140960795 + 223112 * 2 ^ 59
def prefixEnd_223112 : Nat := 4983230072969 + 3 ^ 40 * 223112 * 2
def baseEnd_223112 : Nat := 114563695786036306973933

theorem tailTrace_223112 : CollatzResearch.WordTrace tailWord_223112 prefixEnd_223112 114563695786036306973933 := by
  unfold tailWord_223112
  simp only [CollatzResearch.WordTrace]
  refine ⟨4068781583855401670527795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5425042111807202227370393 4068781583855401670527795)
  ·
    refine ⟨6103172375783102505791693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4068781583855401670527795 6103172375783102505791693)
    ·
      refine ⟨2288689640918663439671885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6103172375783102505791693 2288689640918663439671885)
      ·
        refine ⟨858258615344498789876957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2288689640918663439671885 858258615344498789876957)
        ·
          refine ⟨321846980754187046203859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 858258615344498789876957 321846980754187046203859)
          ·
            refine ⟨482770471131280569305789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321846980754187046203859 482770471131280569305789)
            ·
              refine ⟨181038926674230213489671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 482770471131280569305789 181038926674230213489671)
              ·
                refine ⟨271558390011345320234507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181038926674230213489671 271558390011345320234507)
                ·
                  refine ⟨407337585017017980351761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271558390011345320234507 407337585017017980351761)
                  ·
                    refine ⟨305503188762763485263821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 407337585017017980351761 305503188762763485263821)
                    ·
                      refine ⟨114563695786036306973933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 305503188762763485263821 114563695786036306973933)
                      ·
                        rfl

theorem cell23_223112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_223112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223112 prefixEnd_223112 := by exact prefixLift 223112
  have htrace : WordTrace (prefixWord ++ tailWord_223112) baseStart_223112 baseEnd_223112 := by
    simpa [prefixWord, tailWord_223112, baseEnd_223112] using wordTrace_append hprefix tailTrace_223112
  have hstable : (prefixWord ++ tailWord_223112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223112).length < 2 ^ (prefixWord ++ tailWord_223112).sum := by decide
  have hdescent : baseEnd_223112 < baseStart_223112 := by decide
  rcases family_descends (prefixWord ++ tailWord_223112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223125 : List Nat := [1, 3, 2, 1, 1, 3, 4, 2, 2, 1, 3]
def baseStart_223125 : Nat := 118140960795 + 223125 * 2 ^ 59
def prefixEnd_223125 : Nat := 4983230072969 + 3 ^ 40 * 223125 * 2
def baseEnd_223125 : Nat := 114570371034544756111373

theorem tailTrace_223125 : CollatzResearch.WordTrace tailWord_223125 prefixEnd_223125 114570371034544756111373 := by
  unfold tailWord_223125
  simp only [CollatzResearch.WordTrace]
  refine ⟨8138037316663706561278829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5425358211109137707519219 8138037316663706561278829)
  ·
    refine ⟨3051763993748889960479561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8138037316663706561278829 3051763993748889960479561)
    ·
      refine ⟨2288822995311667470359671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3051763993748889960479561 2288822995311667470359671)
      ·
        refine ⟨3433234492967501205539507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2288822995311667470359671 3433234492967501205539507)
        ·
          refine ⟨5149851739451251808309261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3433234492967501205539507 5149851739451251808309261)
          ·
            refine ⟨1931194402294219428115973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5149851739451251808309261 1931194402294219428115973)
            ·
              refine ⟨362098950430166142771745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1931194402294219428115973 362098950430166142771745)
              ·
                refine ⟨271574212822624607078809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362098950430166142771745 271574212822624607078809)
                ·
                  refine ⟨203680659616968455309107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 271574212822624607078809 203680659616968455309107)
                  ·
                    refine ⟨305520989425452682963661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 203680659616968455309107 305520989425452682963661)
                    ·
                      refine ⟨114570371034544756111373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 305520989425452682963661 114570371034544756111373)
                      ·
                        rfl

theorem cell23_223125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_223125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223125 prefixEnd_223125 := by exact prefixLift 223125
  have htrace : WordTrace (prefixWord ++ tailWord_223125) baseStart_223125 baseEnd_223125 := by
    simpa [prefixWord, tailWord_223125, baseEnd_223125] using wordTrace_append hprefix tailTrace_223125
  have hstable : (prefixWord ++ tailWord_223125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223125).length < 2 ^ (prefixWord ++ tailWord_223125).sum := by decide
  have hdescent : baseEnd_223125 < baseStart_223125 := by decide
  rcases family_descends (prefixWord ++ tailWord_223125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223151 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 2, 4, 3]
def baseStart_223151 : Nat := 118140960795 + 223151 * 2 ^ 59
def prefixEnd_223151 : Nat := 4983230072969 + 3 ^ 40 * 223151 * 2
def baseEnd_223151 : Nat := 114583721531561654386253

theorem tailTrace_223151 : CollatzResearch.WordTrace tailWord_223151 prefixEnd_223151 114583721531561654386253 := by
  unfold tailWord_223151
  simp only [CollatzResearch.WordTrace]
  refine ⟨8138985614569513001725307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5425990409713008667816871 8138985614569513001725307)
  ·
    refine ⟨12208478421854269502587961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8138985614569513001725307 12208478421854269502587961)
    ·
      refine ⟨9156358816390702126940971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12208478421854269502587961 9156358816390702126940971)
      ·
        refine ⟨13734538224586053190411457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9156358816390702126940971 13734538224586053190411457)
        ·
          refine ⟨10300903668439539892808593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13734538224586053190411457 10300903668439539892808593)
          ·
            refine ⟨7725677751329654919606445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10300903668439539892808593 7725677751329654919606445)
            ·
              refine ⟨2897129156748620594852417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7725677751329654919606445 2897129156748620594852417)
              ·
                refine ⟨2172846867561465446139313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2897129156748620594852417 2172846867561465446139313)
                ·
                  refine ⟨1629635150671099084604485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2172846867561465446139313 1629635150671099084604485)
                  ·
                    refine ⟨305556590750831078363341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1629635150671099084604485 305556590750831078363341)
                    ·
                      refine ⟨114583721531561654386253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 305556590750831078363341 114583721531561654386253)
                      ·
                        rfl

theorem cell23_223151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4, 3].length) (baseStart_223151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223151 prefixEnd_223151 := by exact prefixLift 223151
  have htrace : WordTrace (prefixWord ++ tailWord_223151) baseStart_223151 baseEnd_223151 := by
    simpa [prefixWord, tailWord_223151, baseEnd_223151] using wordTrace_append hprefix tailTrace_223151
  have hstable : (prefixWord ++ tailWord_223151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223151).length < 2 ^ (prefixWord ++ tailWord_223151).sum := by decide
  have hdescent : baseEnd_223151 < baseStart_223151 := by decide
  rcases family_descends (prefixWord ++ tailWord_223151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223161 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 1, 4, 4]
def baseStart_223161 : Nat := 118140960795 + 223161 * 2 ^ 59
def prefixEnd_223161 : Nat := 4983230072969 + 3 ^ 40 * 223161 * 2
def baseEnd_223161 : Nat := 114588856338106615261207

theorem tailTrace_223161 : CollatzResearch.WordTrace tailWord_223161 prefixEnd_223161 114588856338106615261207 := by
  unfold tailWord_223161
  simp only [CollatzResearch.WordTrace]
  refine ⟨8139350344533284709589337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5426233563022189806392891 8139350344533284709589337)
  ·
    refine ⟨6104512758399963532192003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8139350344533284709589337 6104512758399963532192003)
    ·
      refine ⟨9156769137599945298288005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6104512758399963532192003 9156769137599945298288005)
      ·
        refine ⟨1716894213299989743429001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9156769137599945298288005 1716894213299989743429001)
        ·
          refine ⟨1287670659974992307571751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1716894213299989743429001 1287670659974992307571751)
          ·
            refine ⟨1931505989962488461357627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1287670659974992307571751 1931505989962488461357627)
            ·
              refine ⟨2897258984943732692036441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1931505989962488461357627 2897258984943732692036441)
              ·
                refine ⟨2172944238707799519027331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2897258984943732692036441 2172944238707799519027331)
                ·
                  refine ⟨3259416358061699278540997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2172944238707799519027331 3259416358061699278540997)
                  ·
                    refine ⟨611140567136568614726437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3259416358061699278540997 611140567136568614726437)
                    ·
                      refine ⟨114588856338106615261207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 611140567136568614726437 114588856338106615261207)
                      ·
                        rfl

theorem cell23_223161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_223161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223161 prefixEnd_223161 := by exact prefixLift 223161
  have htrace : WordTrace (prefixWord ++ tailWord_223161) baseStart_223161 baseEnd_223161 := by
    simpa [prefixWord, tailWord_223161, baseEnd_223161] using wordTrace_append hprefix tailTrace_223161
  have hstable : (prefixWord ++ tailWord_223161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223161).length < 2 ^ (prefixWord ++ tailWord_223161).sum := by decide
  have hdescent : baseEnd_223161 < baseStart_223161 := by decide
  rcases family_descends (prefixWord ++ tailWord_223161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223165 : List Nat := [1, 4, 1, 2, 3, 1, 2, 2, 1, 4, 2]
def baseStart_223165 : Nat := 118140960795 + 223165 * 2 ^ 59
def prefixEnd_223165 : Nat := 4983230072969 + 3 ^ 40 * 223165 * 2
def baseEnd_223165 : Nat := 114590910260724599611189

theorem tailTrace_223165 : CollatzResearch.WordTrace tailWord_223165 prefixEnd_223165 114590910260724599611189 := by
  unfold tailWord_223165
  simp only [CollatzResearch.WordTrace]
  refine ⟨8139496236518793392734949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5426330824345862261823299 8139496236518793392734949)
  ·
    refine ⟨1526155544347273761137803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8139496236518793392734949 1526155544347273761137803)
    ·
      refine ⟨2289233316520910641706705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1526155544347273761137803 2289233316520910641706705)
      ·
        refine ⟨1716924987390682981280029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2289233316520910641706705 1716924987390682981280029)
        ·
          refine ⟨643846870271506117980011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1716924987390682981280029 643846870271506117980011)
          ·
            refine ⟨965770305407259176970017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643846870271506117980011 965770305407259176970017)
            ·
              refine ⟨724327729055444382727513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 965770305407259176970017 724327729055444382727513)
              ·
                refine ⟨543245796791583287045635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 724327729055444382727513 543245796791583287045635)
                ·
                  refine ⟨814868695187374930568453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 543245796791583287045635 814868695187374930568453)
                  ·
                    refine ⟨152787880347632799481585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 814868695187374930568453 152787880347632799481585)
                    ·
                      refine ⟨114590910260724599611189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 152787880347632799481585 114590910260724599611189)
                      ·
                        rfl

theorem cell23_223165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_223165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223165 prefixEnd_223165 := by exact prefixLift 223165
  have htrace : WordTrace (prefixWord ++ tailWord_223165) baseStart_223165 baseEnd_223165 := by
    simpa [prefixWord, tailWord_223165, baseEnd_223165] using wordTrace_append hprefix tailTrace_223165
  have hstable : (prefixWord ++ tailWord_223165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223165).length < 2 ^ (prefixWord ++ tailWord_223165).sum := by decide
  have hdescent : baseEnd_223165 < baseStart_223165 := by decide
  rcases family_descends (prefixWord ++ tailWord_223165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223188 : List Nat := [2, 4, 1, 2, 1, 1, 4, 1, 7]
def baseStart_223188 : Nat := 118140960795 + 223188 * 2 ^ 59
def prefixEnd_223188 : Nat := 4983230072969 + 3 ^ 40 * 223188 * 2
def baseEnd_223188 : Nat := 12733635590642001069287

theorem tailTrace_223188 : CollatzResearch.WordTrace tailWord_223188 prefixEnd_223188 12733635590642001069287 := by
  unfold tailWord_223188
  simp only [CollatzResearch.WordTrace]
  refine ⟨4070167557717734160411109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5426890076956978880548145 4070167557717734160411109)
  ·
    refine ⟨763156417072075155077083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4070167557717734160411109 763156417072075155077083)
    ·
      refine ⟨1144734625608112732615625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 763156417072075155077083 1144734625608112732615625)
      ·
        refine ⟨858550969206084549461719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1144734625608112732615625 858550969206084549461719)
        ·
          refine ⟨1287826453809126824192579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 858550969206084549461719 1287826453809126824192579)
          ·
            refine ⟨1931739680713690236288869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1287826453809126824192579 1931739680713690236288869)
            ·
              refine ⟨362201190133816919304163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1931739680713690236288869 362201190133816919304163)
              ·
                refine ⟨543301785200725378956245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362201190133816919304163 543301785200725378956245)
                ·
                  refine ⟨12733635590642001069287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 543301785200725378956245 12733635590642001069287)
                  ·
                    rfl

theorem cell23_223188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_223188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223188 prefixEnd_223188 := by exact prefixLift 223188
  have htrace : WordTrace (prefixWord ++ tailWord_223188) baseStart_223188 baseEnd_223188 := by
    simpa [prefixWord, tailWord_223188, baseEnd_223188] using wordTrace_append hprefix tailTrace_223188
  have hstable : (prefixWord ++ tailWord_223188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223188).length < 2 ^ (prefixWord ++ tailWord_223188).sum := by decide
  have hdescent : baseEnd_223188 < baseStart_223188 := by decide
  rcases family_descends (prefixWord ++ tailWord_223188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223199 : List Nat := [1, 1, 2, 3, 4, 2, 3, 1, 2, 2, 2]
def baseStart_223199 : Nat := 118140960795 + 223199 * 2 ^ 59
def prefixEnd_223199 : Nat := 4983230072969 + 3 ^ 40 * 223199 * 2
def baseEnd_223199 : Nat := 114608368602977466586033

theorem tailTrace_223199 : CollatzResearch.WordTrace tailWord_223199 prefixEnd_223199 114608368602977466586033 := by
  unfold tailWord_223199
  simp only [CollatzResearch.WordTrace]
  refine ⟨8140736318395617199472651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5427157545597078132981767 8140736318395617199472651)
  ·
    refine ⟨12211104477593425799208977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8140736318395617199472651 12211104477593425799208977)
    ·
      refine ⟨9158328358195069349406733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12211104477593425799208977 9158328358195069349406733)
      ·
        refine ⟨3434373134323151006027525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9158328358195069349406733 3434373134323151006027525)
        ·
          refine ⟨643944962685590813630161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3434373134323151006027525 643944962685590813630161)
          ·
            refine ⟨482958722014193110222621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 643944962685590813630161 482958722014193110222621)
            ·
              refine ⟨181109520755322416333483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 482958722014193110222621 181109520755322416333483)
              ·
                refine ⟨271664281132983624500225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181109520755322416333483 271664281132983624500225)
                ·
                  refine ⟨203748210849737718375169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 271664281132983624500225 203748210849737718375169)
                  ·
                    refine ⟨152811158137303288781377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 203748210849737718375169 152811158137303288781377)
                    ·
                      refine ⟨114608368602977466586033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 152811158137303288781377 114608368602977466586033)
                      ·
                        rfl

theorem cell23_223199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 2, 2, 2].length) (baseStart_223199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223199 prefixEnd_223199 := by exact prefixLift 223199
  have htrace : WordTrace (prefixWord ++ tailWord_223199) baseStart_223199 baseEnd_223199 := by
    simpa [prefixWord, tailWord_223199, baseEnd_223199] using wordTrace_append hprefix tailTrace_223199
  have hstable : (prefixWord ++ tailWord_223199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223199).length < 2 ^ (prefixWord ++ tailWord_223199).sum := by decide
  have hdescent : baseEnd_223199 < baseStart_223199 := by decide
  rcases family_descends (prefixWord ++ tailWord_223199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223201 : List Nat := [1, 2, 3, 1, 2, 1, 3, 2, 1, 7]
def baseStart_223201 : Nat := 118140960795 + 223201 * 2 ^ 59
def prefixEnd_223201 : Nat := 4983230072969 + 3 ^ 40 * 223201 * 2
def baseEnd_223201 : Nat := 38203131854762152920341

theorem tailTrace_223201 : CollatzResearch.WordTrace tailWord_223201 prefixEnd_223201 38203131854762152920341 := by
  unfold tailWord_223201
  simp only [CollatzResearch.WordTrace]
  refine ⟨8140809264388371541045457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5427206176258914360696971 8140809264388371541045457)
  ·
    refine ⟨6105606948291278655784093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8140809264388371541045457 6105606948291278655784093)
    ·
      refine ⟨2289602605609229495919035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6105606948291278655784093 2289602605609229495919035)
      ·
        refine ⟨3434403908413844243878553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2289602605609229495919035 3434403908413844243878553)
        ·
          refine ⟨2575802931310383182908915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3434403908413844243878553 2575802931310383182908915)
          ·
            refine ⟨3863704396965574774363373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2575802931310383182908915 3863704396965574774363373)
            ·
              refine ⟨1448889148862090540386265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3863704396965574774363373 1448889148862090540386265)
              ·
                refine ⟨1086666861646567905289699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1448889148862090540386265 1086666861646567905289699)
                ·
                  refine ⟨1630000292469851857934549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1086666861646567905289699 1630000292469851857934549)
                  ·
                    refine ⟨38203131854762152920341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1630000292469851857934549 38203131854762152920341)
                    ·
                      rfl

theorem cell23_223201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_223201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223201 prefixEnd_223201 := by exact prefixLift 223201
  have htrace : WordTrace (prefixWord ++ tailWord_223201) baseStart_223201 baseEnd_223201 := by
    simpa [prefixWord, tailWord_223201, baseEnd_223201] using wordTrace_append hprefix tailTrace_223201
  have hstable : (prefixWord ++ tailWord_223201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223201).length < 2 ^ (prefixWord ++ tailWord_223201).sum := by decide
  have hdescent : baseEnd_223201 < baseStart_223201 := by decide
  rcases family_descends (prefixWord ++ tailWord_223201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223251 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 6]
def baseStart_223251 : Nat := 118140960795 + 223251 * 2 ^ 59
def prefixEnd_223251 : Nat := 4983230072969 + 3 ^ 40 * 223251 * 2
def baseEnd_223251 : Nat := 114635069597011263135793

theorem tailTrace_223251 : CollatzResearch.WordTrace tailWord_223251 prefixEnd_223251 114635069597011263135793 := by
  unfold tailWord_223251
  simp only [CollatzResearch.WordTrace]
  refine ⟨8142632914207230080365607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5428421942804820053577071 8142632914207230080365607)
  ·
    refine ⟨12213949371310845120548411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8142632914207230080365607 12213949371310845120548411)
    ·
      refine ⟨18320924056966267680822617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12213949371310845120548411 18320924056966267680822617)
      ·
        refine ⟨13740693042724700760616963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18320924056966267680822617 13740693042724700760616963)
        ·
          refine ⟨20611039564087051140925445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13740693042724700760616963 20611039564087051140925445)
          ·
            refine ⟨3864569918266322088923521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20611039564087051140925445 3864569918266322088923521)
            ·
              refine ⟨2898427438699741566692641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3864569918266322088923521 2898427438699741566692641)
              ·
                refine ⟨2173820579024806175019481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2898427438699741566692641 2173820579024806175019481)
                ·
                  refine ⟨1630365434268604631264611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2173820579024806175019481 1630365434268604631264611)
                  ·
                    refine ⟨2445548151402906946896917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1630365434268604631264611 2445548151402906946896917)
                    ·
                      refine ⟨114635069597011263135793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2445548151402906946896917 114635069597011263135793)
                      ·
                        rfl

theorem cell23_223251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 6].length) (baseStart_223251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223251 prefixEnd_223251 := by exact prefixLift 223251
  have htrace : WordTrace (prefixWord ++ tailWord_223251) baseStart_223251 baseEnd_223251 := by
    simpa [prefixWord, tailWord_223251, baseEnd_223251] using wordTrace_append hprefix tailTrace_223251
  have hstable : (prefixWord ++ tailWord_223251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223251).length < 2 ^ (prefixWord ++ tailWord_223251).sum := by decide
  have hdescent : baseEnd_223251 < baseStart_223251 := by decide
  rcases family_descends (prefixWord ++ tailWord_223251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223305 : List Nat := [1, 2, 1, 1, 2, 2, 4, 3, 3, 1, 3]
def baseStart_223305 : Nat := 118140960795 + 223305 * 2 ^ 59
def prefixEnd_223305 : Nat := 4983230072969 + 3 ^ 40 * 223305 * 2
def baseEnd_223305 : Nat := 114662797552354051860545

theorem tailTrace_223305 : CollatzResearch.WordTrace tailWord_223305 prefixEnd_223305 114662797552354051860545 := by
  unfold tailWord_223305
  simp only [CollatzResearch.WordTrace]
  refine ⟨8144602456011597302831369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5429734970674398201887579 8144602456011597302831369)
  ·
    refine ⟨6108451842008697977123527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8144602456011597302831369 6108451842008697977123527)
    ·
      refine ⟨9162677763013046965685291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6108451842008697977123527 9162677763013046965685291)
      ·
        refine ⟨13744016644519570448527937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9162677763013046965685291 13744016644519570448527937)
        ·
          refine ⟨10308012483389677836395953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13744016644519570448527937 10308012483389677836395953)
          ·
            refine ⟨7731009362542258377296965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10308012483389677836395953 7731009362542258377296965)
            ·
              refine ⟨1449564255476673445743181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7731009362542258377296965 1449564255476673445743181)
              ·
                refine ⟨543586595803752542153693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1449564255476673445743181 543586595803752542153693)
                ·
                  refine ⟨203844973426407203307635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 543586595803752542153693 203844973426407203307635)
                  ·
                    refine ⟨305767460139610804961453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 203844973426407203307635 305767460139610804961453)
                    ·
                      refine ⟨114662797552354051860545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 305767460139610804961453 114662797552354051860545)
                      ·
                        rfl

theorem cell23_223305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3, 1, 3].length) (baseStart_223305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223305 prefixEnd_223305 := by exact prefixLift 223305
  have htrace : WordTrace (prefixWord ++ tailWord_223305) baseStart_223305 baseEnd_223305 := by
    simpa [prefixWord, tailWord_223305, baseEnd_223305] using wordTrace_append hprefix tailTrace_223305
  have hstable : (prefixWord ++ tailWord_223305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223305).length < 2 ^ (prefixWord ++ tailWord_223305).sum := by decide
  have hdescent : baseEnd_223305 < baseStart_223305 := by decide
  rcases family_descends (prefixWord ++ tailWord_223305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223308 : List Nat := [2, 2, 1, 3, 1, 1, 3, 2, 3, 5]
def baseStart_223308 : Nat := 118140960795 + 223308 * 2 ^ 59
def prefixEnd_223308 : Nat := 4983230072969 + 3 ^ 40 * 223308 * 2
def baseEnd_223308 : Nat := 38221445998105846707677

theorem tailTrace_223308 : CollatzResearch.WordTrace tailWord_223308 prefixEnd_223308 38221445998105846707677 := by
  unfold tailWord_223308
  simp only [CollatzResearch.WordTrace]
  refine ⟨4072355937500364407595289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5429807916667152543460385 4072355937500364407595289)
  ·
    refine ⟨3054266953125273305696467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4072355937500364407595289 3054266953125273305696467)
    ·
      refine ⟨4581400429687909958544701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3054266953125273305696467 4581400429687909958544701)
      ·
        refine ⟨1718025161132966234454263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4581400429687909958544701 1718025161132966234454263)
        ·
          refine ⟨2577037741699449351681395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1718025161132966234454263 2577037741699449351681395)
          ·
            refine ⟨3865556612549174027522093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2577037741699449351681395 3865556612549174027522093)
            ·
              refine ⟨1449583729705940260320785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3865556612549174027522093 1449583729705940260320785)
              ·
                refine ⟨1087187797279455195240589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1449583729705940260320785 1087187797279455195240589)
                ·
                  refine ⟨407695423979795698215221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1087187797279455195240589 407695423979795698215221)
                  ·
                    refine ⟨38221445998105846707677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 407695423979795698215221 38221445998105846707677)
                    ·
                      rfl

theorem cell23_223308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 3, 5].length) (baseStart_223308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223308 prefixEnd_223308 := by exact prefixLift 223308
  have htrace : WordTrace (prefixWord ++ tailWord_223308) baseStart_223308 baseEnd_223308 := by
    simpa [prefixWord, tailWord_223308, baseEnd_223308] using wordTrace_append hprefix tailTrace_223308
  have hstable : (prefixWord ++ tailWord_223308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223308).length < 2 ^ (prefixWord ++ tailWord_223308).sum := by decide
  have hdescent : baseEnd_223308 < baseStart_223308 := by decide
  rcases family_descends (prefixWord ++ tailWord_223308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223332 : List Nat := [2, 3, 1, 1, 2, 1, 5, 1, 2, 3, 2]
def baseStart_223332 : Nat := 118140960795 + 223332 * 2 ^ 59
def prefixEnd_223332 : Nat := 4983230072969 + 3 ^ 40 * 223332 * 2
def baseEnd_223332 : Nat := 114676661530025446222921

theorem tailTrace_223332 : CollatzResearch.WordTrace tailWord_223332 prefixEnd_223332 114676661530025446222921 := by
  unfold tailWord_223332
  simp only [CollatzResearch.WordTrace]
  refine ⟨4072793613456890457032125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5430391484609187276042833 4072793613456890457032125)
  ·
    refine ⟨1527297605046333921387047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4072793613456890457032125 1527297605046333921387047)
    ·
      refine ⟨2290946407569500882080571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1527297605046333921387047 2290946407569500882080571)
      ·
        refine ⟨3436419611354251323120857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2290946407569500882080571 3436419611354251323120857)
        ·
          refine ⟨2577314708515688492340643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3436419611354251323120857 2577314708515688492340643)
          ·
            refine ⟨3865972062773532738510965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2577314708515688492340643 3865972062773532738510965)
            ·
              refine ⟨362434880885018694235403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3865972062773532738510965 362434880885018694235403)
              ·
                refine ⟨543652321327528041353105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362434880885018694235403 543652321327528041353105)
                ·
                  refine ⟨407739240995646031014829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 543652321327528041353105 407739240995646031014829)
                  ·
                    refine ⟨152902215373367261630561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 407739240995646031014829 152902215373367261630561)
                    ·
                      refine ⟨114676661530025446222921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 152902215373367261630561 114676661530025446222921)
                      ·
                        rfl

theorem cell23_223332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 2, 3, 2].length) (baseStart_223332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223332 prefixEnd_223332 := by exact prefixLift 223332
  have htrace : WordTrace (prefixWord ++ tailWord_223332) baseStart_223332 baseEnd_223332 := by
    simpa [prefixWord, tailWord_223332, baseEnd_223332] using wordTrace_append hprefix tailTrace_223332
  have hstable : (prefixWord ++ tailWord_223332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223332).length < 2 ^ (prefixWord ++ tailWord_223332).sum := by decide
  have hdescent : baseEnd_223332 < baseStart_223332 := by decide
  rcases family_descends (prefixWord ++ tailWord_223332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223345 : List Nat := [1, 2, 2, 2, 1, 1, 5, 3, 1, 1, 4]
def baseStart_223345 : Nat := 118140960795 + 223345 * 2 ^ 59
def prefixEnd_223345 : Nat := 4983230072969 + 3 ^ 40 * 223345 * 2
def baseEnd_223345 : Nat := 114683336778533895360361

theorem tailTrace_223345 : CollatzResearch.WordTrace tailWord_223345 prefixEnd_223345 114683336778533895360361 := by
  unfold tailWord_223345
  simp only [CollatzResearch.WordTrace]
  refine ⟨8146061375866684134287489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5430707583911122756191659 8146061375866684134287489)
  ·
    refine ⟨6109546031900013100715617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8146061375866684134287489 6109546031900013100715617)
    ·
      refine ⟨4582159523925009825536713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6109546031900013100715617 4582159523925009825536713)
      ·
        refine ⟨3436619642943757369152535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4582159523925009825536713 3436619642943757369152535)
        ·
          refine ⟨5154929464415636053728803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3436619642943757369152535 5154929464415636053728803)
          ·
            refine ⟨7732394196623454080593205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5154929464415636053728803 7732394196623454080593205)
            ·
              refine ⟨724911955933448820055613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7732394196623454080593205 724911955933448820055613)
              ·
                refine ⟨271841983475043307520855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 724911955933448820055613 271841983475043307520855)
                ·
                  refine ⟨407762975212564961281283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271841983475043307520855 407762975212564961281283)
                  ·
                    refine ⟨611644462818847441921925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 407762975212564961281283 611644462818847441921925)
                    ·
                      refine ⟨114683336778533895360361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 611644462818847441921925 114683336778533895360361)
                      ·
                        rfl

theorem cell23_223345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_223345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223345 prefixEnd_223345 := by exact prefixLift 223345
  have htrace : WordTrace (prefixWord ++ tailWord_223345) baseStart_223345 baseEnd_223345 := by
    simpa [prefixWord, tailWord_223345, baseEnd_223345] using wordTrace_append hprefix tailTrace_223345
  have hstable : (prefixWord ++ tailWord_223345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223345).length < 2 ^ (prefixWord ++ tailWord_223345).sum := by decide
  have hdescent : baseEnd_223345 < baseStart_223345 := by decide
  rcases family_descends (prefixWord ++ tailWord_223345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223365 : List Nat := [1, 3, 1, 1, 5, 2, 1, 2, 1, 1, 5]
def baseStart_223365 : Nat := 118140960795 + 223365 * 2 ^ 59
def prefixEnd_223365 : Nat := 4983230072969 + 3 ^ 40 * 223365 * 2
def baseEnd_223365 : Nat := 114693606391623817110269

theorem tailTrace_223365 : CollatzResearch.WordTrace tailWord_223365 prefixEnd_223365 114693606391623817110269 := by
  unfold tailWord_223365
  simp only [CollatzResearch.WordTrace]
  refine ⟨8146790835794227550015549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5431193890529485033343699 8146790835794227550015549)
  ·
    refine ⟨3055046563422835331255831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8146790835794227550015549 3055046563422835331255831)
    ·
      refine ⟨4582569845134252996883747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3055046563422835331255831 4582569845134252996883747)
      ·
        refine ⟨6873854767701379495325621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4582569845134252996883747 6873854767701379495325621)
        ·
          refine ⟨644423884472004327686777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6873854767701379495325621 644423884472004327686777)
          ·
            refine ⟨483317913354003245765083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 644423884472004327686777 483317913354003245765083)
            ·
              refine ⟨724976870031004868647625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483317913354003245765083 724976870031004868647625)
              ·
                refine ⟨543732652523253651485719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 724976870031004868647625 543732652523253651485719)
                ·
                  refine ⟨815598978784880477228579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 543732652523253651485719 815598978784880477228579)
                  ·
                    refine ⟨1223398468177320715842869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 815598978784880477228579 1223398468177320715842869)
                    ·
                      refine ⟨114693606391623817110269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1223398468177320715842869 114693606391623817110269)
                      ·
                        rfl

theorem cell23_223365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_223365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223365 prefixEnd_223365 := by exact prefixLift 223365
  have htrace : WordTrace (prefixWord ++ tailWord_223365) baseStart_223365 baseEnd_223365 := by
    simpa [prefixWord, tailWord_223365, baseEnd_223365] using wordTrace_append hprefix tailTrace_223365
  have hstable : (prefixWord ++ tailWord_223365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223365).length < 2 ^ (prefixWord ++ tailWord_223365).sum := by decide
  have hdescent : baseEnd_223365 < baseStart_223365 := by decide
  rcases family_descends (prefixWord ++ tailWord_223365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223390 : List Nat := [4, 3, 1, 1, 4, 1, 1, 3, 1, 1, 3]
def baseStart_223390 : Nat := 118140960795 + 223390 * 2 ^ 59
def prefixEnd_223390 : Nat := 4983230072969 + 3 ^ 40 * 223390 * 2
def baseEnd_223390 : Nat := 114706443407986219297655

theorem tailTrace_223390 : CollatzResearch.WordTrace tailWord_223390 prefixEnd_223390 114706443407986219297655 := by
  unfold tailWord_223390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1018462832587957102459453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5431801773802437879783749 1018462832587957102459453)
  ·
    refine ⟨381923562220483913422295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1018462832587957102459453 381923562220483913422295)
    ·
      refine ⟨572885343330725870133443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381923562220483913422295 572885343330725870133443)
      ·
        refine ⟨859328014996088805200165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572885343330725870133443 859328014996088805200165)
        ·
          refine ⟨161124002811766650975031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 859328014996088805200165 161124002811766650975031)
          ·
            refine ⟨241686004217649976462547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161124002811766650975031 241686004217649976462547)
            ·
              refine ⟨362529006326474964693821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241686004217649976462547 362529006326474964693821)
              ·
                refine ⟨135948377372428111760183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 362529006326474964693821 135948377372428111760183)
                ·
                  refine ⟨203922566058642167640275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135948377372428111760183 203922566058642167640275)
                  ·
                    refine ⟨305883849087963251460413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 203922566058642167640275 305883849087963251460413)
                    ·
                      refine ⟨114706443407986219297655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 305883849087963251460413 114706443407986219297655)
                      ·
                        rfl

theorem cell23_223390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_223390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223390 prefixEnd_223390 := by exact prefixLift 223390
  have htrace : WordTrace (prefixWord ++ tailWord_223390) baseStart_223390 baseEnd_223390 := by
    simpa [prefixWord, tailWord_223390, baseEnd_223390] using wordTrace_append hprefix tailTrace_223390
  have hstable : (prefixWord ++ tailWord_223390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223390).length < 2 ^ (prefixWord ++ tailWord_223390).sum := by decide
  have hdescent : baseEnd_223390 < baseStart_223390 := by decide
  rcases family_descends (prefixWord ++ tailWord_223390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223402 : List Nat := [3, 1, 5, 1, 2, 2, 9]
def baseStart_223402 : Nat := 118140960795 + 223402 * 2 ^ 59
def prefixEnd_223402 : Nat := 4983230072969 + 3 ^ 40 * 223402 * 2
def baseEnd_223402 : Nat := 1416205002170866325279

theorem tailTrace_223402 : CollatzResearch.WordTrace tailWord_223402 prefixEnd_223402 1416205002170866325279 := by
  unfold tailWord_223402
  simp only [CollatzResearch.WordTrace]
  refine ⟨2037035084165045717278115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5432093557773455246074973 2037035084165045717278115)
  ·
    refine ⟨3055552626247568575917173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2037035084165045717278115 3055552626247568575917173)
    ·
      refine ⟨286458058710709553992235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3055552626247568575917173 286458058710709553992235)
      ·
        refine ⟨429687088066064330988353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286458058710709553992235 429687088066064330988353)
        ·
          refine ⟨322265316049548248241265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429687088066064330988353 322265316049548248241265)
          ·
            refine ⟨241698987037161186180949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322265316049548248241265 241698987037161186180949)
            ·
              refine ⟨1416205002170866325279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 241698987037161186180949 1416205002170866325279)
              ·
                rfl

theorem cell23_223402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 9].length) (baseStart_223402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223402 prefixEnd_223402 := by exact prefixLift 223402
  have htrace : WordTrace (prefixWord ++ tailWord_223402) baseStart_223402 baseEnd_223402 := by
    simpa [prefixWord, tailWord_223402, baseEnd_223402] using wordTrace_append hprefix tailTrace_223402
  have hstable : (prefixWord ++ tailWord_223402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223402).length < 2 ^ (prefixWord ++ tailWord_223402).sum := by decide
  have hdescent : baseEnd_223402 < baseStart_223402 := by decide
  rcases family_descends (prefixWord ++ tailWord_223402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223413 : List Nat := [1, 3, 3, 4, 1, 2, 1, 1, 3, 2, 2]
def baseStart_223413 : Nat := 118140960795 + 223413 * 2 ^ 59
def prefixEnd_223413 : Nat := 4983230072969 + 3 ^ 40 * 223413 * 2
def baseEnd_223413 : Nat := 114718253463039629310049

theorem tailTrace_223413 : CollatzResearch.WordTrace tailWord_223413 prefixEnd_223413 114718253463039629310049 := by
  unfold tailWord_223413
  simp only [CollatzResearch.WordTrace]
  refine ⟨8148541539620331747762893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5432361026413554498508595 8148541539620331747762893)
  ·
    refine ⟨3055703077357624405411085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8148541539620331747762893 3055703077357624405411085)
    ·
      refine ⟨1145888654009109152029157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3055703077357624405411085 1145888654009109152029157)
      ·
        refine ⟨214854122626707966005467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1145888654009109152029157 214854122626707966005467)
        ·
          refine ⟨322281183940061949008201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214854122626707966005467 322281183940061949008201)
          ·
            refine ⟨241710887955046461756151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322281183940061949008201 241710887955046461756151)
            ·
              refine ⟨362566331932569692634227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241710887955046461756151 362566331932569692634227)
              ·
                refine ⟨543849497898854538951341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362566331932569692634227 543849497898854538951341)
                ·
                  refine ⟨203943561712070452106753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 543849497898854538951341 203943561712070452106753)
                  ·
                    refine ⟨152957671284052839080065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 203943561712070452106753 152957671284052839080065)
                    ·
                      refine ⟨114718253463039629310049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 152957671284052839080065 114718253463039629310049)
                      ·
                        rfl

theorem cell23_223413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_223413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223413 prefixEnd_223413 := by exact prefixLift 223413
  have htrace : WordTrace (prefixWord ++ tailWord_223413) baseStart_223413 baseEnd_223413 := by
    simpa [prefixWord, tailWord_223413, baseEnd_223413] using wordTrace_append hprefix tailTrace_223413
  have hstable : (prefixWord ++ tailWord_223413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223413).length < 2 ^ (prefixWord ++ tailWord_223413).sum := by decide
  have hdescent : baseEnd_223413 < baseStart_223413 := by decide
  rcases family_descends (prefixWord ++ tailWord_223413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223429 : List Nat := [1, 3, 1, 1, 1, 1, 8, 1, 2, 1, 3]
def baseStart_223429 : Nat := 118140960795 + 223429 * 2 ^ 59
def prefixEnd_223429 : Nat := 4983230072969 + 3 ^ 40 * 223429 * 2
def baseEnd_223429 : Nat := 114726469153511566709975

theorem tailTrace_223429 : CollatzResearch.WordTrace tailWord_223429 prefixEnd_223429 114726469153511566709975 := by
  unfold tailWord_223429
  simp only [CollatzResearch.WordTrace]
  refine ⟨8149125107562366480345341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5432750071708244320230227 8149125107562366480345341)
  ·
    refine ⟨3055921915335887430129503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8149125107562366480345341 3055921915335887430129503)
    ·
      refine ⟨4583882873003831145194255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3055921915335887430129503 4583882873003831145194255)
      ·
        refine ⟨6875824309505746717791383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4583882873003831145194255 6875824309505746717791383)
        ·
          refine ⟨10313736464258620076687075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6875824309505746717791383 10313736464258620076687075)
          ·
            refine ⟨15470604696387930115030613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10313736464258620076687075 15470604696387930115030613)
            ·
              refine ⟨181296148785796056035515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 15470604696387930115030613 181296148785796056035515)
              ·
                refine ⟨271944223178694084053273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181296148785796056035515 271944223178694084053273)
                ·
                  refine ⟨203958167384020563039955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 271944223178694084053273 203958167384020563039955)
                  ·
                    refine ⟨305937251076030844559933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 203958167384020563039955 305937251076030844559933)
                    ·
                      refine ⟨114726469153511566709975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 305937251076030844559933 114726469153511566709975)
                      ·
                        rfl

theorem cell23_223429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 2, 1, 3].length) (baseStart_223429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223429 prefixEnd_223429 := by exact prefixLift 223429
  have htrace : WordTrace (prefixWord ++ tailWord_223429) baseStart_223429 baseEnd_223429 := by
    simpa [prefixWord, tailWord_223429, baseEnd_223429] using wordTrace_append hprefix tailTrace_223429
  have hstable : (prefixWord ++ tailWord_223429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223429).length < 2 ^ (prefixWord ++ tailWord_223429).sum := by decide
  have hdescent : baseEnd_223429 < baseStart_223429 := by decide
  rcases family_descends (prefixWord ++ tailWord_223429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223486 : List Nat := [4, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2]
def baseStart_223486 : Nat := 118140960795 + 223486 * 2 ^ 59
def prefixEnd_223486 : Nat := 4983230072969 + 3 ^ 40 * 223486 * 2
def baseEnd_223486 : Nat := 114755737550817843697213

theorem tailTrace_223486 : CollatzResearch.WordTrace tailWord_223486 prefixEnd_223486 114755737550817843697213 := by
  unfold tailWord_223486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1018900508544483151896289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5434136045570576810113541 1018900508544483151896289)
  ·
    refine ⟨764175381408362363922217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1018900508544483151896289 764175381408362363922217)
    ·
      refine ⟨573131536056271772941663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 764175381408362363922217 573131536056271772941663)
      ·
        refine ⟨859697304084407659412495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573131536056271772941663 859697304084407659412495)
        ·
          refine ⟨1289545956126611489118743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859697304084407659412495 1289545956126611489118743)
          ·
            refine ⟨1934318934189917233678115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1289545956126611489118743 1934318934189917233678115)
            ·
              refine ⟨2901478401284875850517173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1934318934189917233678115 2901478401284875850517173)
              ·
                refine ⟨272013600120457110985985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2901478401284875850517173 272013600120457110985985)
                ·
                  refine ⟨204010200090342833239489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 272013600120457110985985 204010200090342833239489)
                  ·
                    refine ⟨153007650067757124929617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 204010200090342833239489 153007650067757124929617)
                    ·
                      refine ⟨114755737550817843697213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 153007650067757124929617 114755737550817843697213)
                      ·
                        rfl

theorem cell23_223486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_223486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223486 prefixEnd_223486 := by exact prefixLift 223486
  have htrace : WordTrace (prefixWord ++ tailWord_223486) baseStart_223486 baseEnd_223486 := by
    simpa [prefixWord, tailWord_223486, baseEnd_223486] using wordTrace_append hprefix tailTrace_223486
  have hstable : (prefixWord ++ tailWord_223486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223486).length < 2 ^ (prefixWord ++ tailWord_223486).sum := by decide
  have hdescent : baseEnd_223486 < baseStart_223486 := by decide
  rcases family_descends (prefixWord ++ tailWord_223486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223492 : List Nat := [2, 3, 2, 2, 3, 1, 1, 2, 7]
def baseStart_223492 : Nat := 118140960795 + 223492 * 2 ^ 59
def prefixEnd_223492 : Nat := 4983230072969 + 3 ^ 40 * 223492 * 2
def baseEnd_223492 : Nat := 12750979826082757802465

theorem tailTrace_223492 : CollatzResearch.WordTrace tailWord_223492 prefixEnd_223492 12750979826082757802465 := by
  unfold tailWord_223492
  simp only [CollatzResearch.WordTrace]
  refine ⟨4075711453167064119944365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5434281937556085493259153 4075711453167064119944365)
  ·
    refine ⟨1528391794937649044979137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4075711453167064119944365 1528391794937649044979137)
    ·
      refine ⟨1146293846203236783734353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1528391794937649044979137 1146293846203236783734353)
      ·
        refine ⟨859720384652427587800765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1146293846203236783734353 859720384652427587800765)
        ·
          refine ⟨322395144244660345425287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 859720384652427587800765 322395144244660345425287)
          ·
            refine ⟨483592716366990518137931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322395144244660345425287 483592716366990518137931)
            ·
              refine ⟨725389074550485777206897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483592716366990518137931 725389074550485777206897)
              ·
                refine ⟨544041805912864332905173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 725389074550485777206897 544041805912864332905173)
                ·
                  refine ⟨12750979826082757802465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 544041805912864332905173 12750979826082757802465)
                  ·
                    rfl

theorem cell23_223492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 7].length) (baseStart_223492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223492 prefixEnd_223492 := by exact prefixLift 223492
  have htrace : WordTrace (prefixWord ++ tailWord_223492) baseStart_223492 baseEnd_223492 := by
    simpa [prefixWord, tailWord_223492, baseEnd_223492] using wordTrace_append hprefix tailTrace_223492
  have hstable : (prefixWord ++ tailWord_223492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223492).length < 2 ^ (prefixWord ++ tailWord_223492).sum := by decide
  have hdescent : baseEnd_223492 < baseStart_223492 := by decide
  rcases family_descends (prefixWord ++ tailWord_223492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223505 : List Nat := [1, 2, 2, 1, 1, 6, 1, 1, 1, 7]
def baseStart_223505 : Nat := 118140960795 + 223505 * 2 ^ 59
def prefixEnd_223505 : Nat := 4983230072969 + 3 ^ 40 * 223505 * 2
def baseEnd_223505 : Nat := 38255164561084423119875

theorem tailTrace_223505 : CollatzResearch.WordTrace tailWord_223505 prefixEnd_223505 38255164561084423119875 := by
  unfold tailWord_223505
  simp only [CollatzResearch.WordTrace]
  refine ⟨8151897055287031460111969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5434598036858020973407979 8151897055287031460111969)
  ·
    refine ⟨6113922791465273595083977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8151897055287031460111969 6113922791465273595083977)
    ·
      refine ⟨4585442093598955196312983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6113922791465273595083977 4585442093598955196312983)
      ·
        refine ⟨6878163140398432794469475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4585442093598955196312983 6878163140398432794469475)
        ·
          refine ⟨10317244710597649191704213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6878163140398432794469475 10317244710597649191704213)
          ·
            refine ⟨483620845809264805861135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10317244710597649191704213 483620845809264805861135)
            ·
              refine ⟨725431268713897208791703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483620845809264805861135 725431268713897208791703)
              ·
                refine ⟨1088146903070845813187555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 725431268713897208791703 1088146903070845813187555)
                ·
                  refine ⟨1632220354606268719781333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1088146903070845813187555 1632220354606268719781333)
                  ·
                    refine ⟨38255164561084423119875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1632220354606268719781333 38255164561084423119875)
                    ·
                      rfl

theorem cell23_223505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 7].length) (baseStart_223505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223505 prefixEnd_223505 := by exact prefixLift 223505
  have htrace : WordTrace (prefixWord ++ tailWord_223505) baseStart_223505 baseEnd_223505 := by
    simpa [prefixWord, tailWord_223505, baseEnd_223505] using wordTrace_append hprefix tailTrace_223505
  have hstable : (prefixWord ++ tailWord_223505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223505).length < 2 ^ (prefixWord ++ tailWord_223505).sum := by decide
  have hdescent : baseEnd_223505 < baseStart_223505 := by decide
  rcases family_descends (prefixWord ++ tailWord_223505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223586 : List Nat := [3, 3, 2, 1, 1, 4, 1, 1, 3, 4]
def baseStart_223586 : Nat := 118140960795 + 223586 * 2 ^ 59
def prefixEnd_223586 : Nat := 4983230072969 + 3 ^ 40 * 223586 * 2
def baseEnd_223586 : Nat := 38269028538755817482251

theorem tailTrace_223586 : CollatzResearch.WordTrace tailWord_223586 prefixEnd_223586 38269028538755817482251 := by
  unfold tailWord_223586
  simp only [CollatzResearch.WordTrace]
  refine ⟨2038712841998395573452653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5436567578662388195873741 2038712841998395573452653)
  ·
    refine ⟨764517315749398340044745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2038712841998395573452653 764517315749398340044745)
    ·
      refine ⟨573387986812048755033559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 764517315749398340044745 573387986812048755033559)
      ·
        refine ⟨860081980218073132550339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573387986812048755033559 860081980218073132550339)
        ·
          refine ⟨1290122970327109698825509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860081980218073132550339 1290122970327109698825509)
          ·
            refine ⟨241898056936333068529783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1290122970327109698825509 241898056936333068529783)
            ·
              refine ⟨362847085404499602794675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241898056936333068529783 362847085404499602794675)
              ·
                refine ⟨544270628106749404192013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362847085404499602794675 544270628106749404192013)
                ·
                  refine ⟨204101485540031026572005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 544270628106749404192013 204101485540031026572005)
                  ·
                    refine ⟨38269028538755817482251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 204101485540031026572005 38269028538755817482251)
                    ·
                      rfl

theorem cell23_223586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_223586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223586 prefixEnd_223586 := by exact prefixLift 223586
  have htrace : WordTrace (prefixWord ++ tailWord_223586) baseStart_223586 baseEnd_223586 := by
    simpa [prefixWord, tailWord_223586, baseEnd_223586] using wordTrace_append hprefix tailTrace_223586
  have hstable : (prefixWord ++ tailWord_223586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223586).length < 2 ^ (prefixWord ++ tailWord_223586).sum := by decide
  have hdescent : baseEnd_223586 < baseStart_223586 := by decide
  rcases family_descends (prefixWord ++ tailWord_223586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223595 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 5, 5]
def baseStart_223595 : Nat := 118140960795 + 223595 * 2 ^ 59
def prefixEnd_223595 : Nat := 4983230072969 + 3 ^ 40 * 223595 * 2
def baseEnd_223595 : Nat := 38270568980719305744737

theorem tailTrace_223595 : CollatzResearch.WordTrace tailWord_223595 prefixEnd_223595 38270568980719305744737 := by
  unfold tailWord_223595
  simp only [CollatzResearch.WordTrace]
  refine ⟨8155179624960976830888239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5436786416640651220592159 8155179624960976830888239)
  ·
    refine ⟨12232769437441465246332359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8155179624960976830888239 12232769437441465246332359)
    ·
      refine ⟨18349154156162197869498539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12232769437441465246332359 18349154156162197869498539)
      ·
        refine ⟨27523731234243296804247809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18349154156162197869498539 27523731234243296804247809)
        ·
          refine ⟨20642798425682472603185857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27523731234243296804247809 20642798425682472603185857)
          ·
            refine ⟨15482098819261854452389393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20642798425682472603185857 15482098819261854452389393)
            ·
              refine ⟨11611574114446390839292045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15482098819261854452389393 11611574114446390839292045)
              ·
                refine ⟨4354340292917396564734517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11611574114446390839292045 4354340292917396564734517)
                ·
                  refine ⟨408219402461005927943861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4354340292917396564734517 408219402461005927943861)
                  ·
                    refine ⟨38270568980719305744737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 408219402461005927943861 38270568980719305744737)
                    ·
                      rfl

theorem cell23_223595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 5].length) (baseStart_223595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223595 prefixEnd_223595 := by exact prefixLift 223595
  have htrace : WordTrace (prefixWord ++ tailWord_223595) baseStart_223595 baseEnd_223595 := by
    simpa [prefixWord, tailWord_223595, baseEnd_223595] using wordTrace_append hprefix tailTrace_223595
  have hstable : (prefixWord ++ tailWord_223595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223595).length < 2 ^ (prefixWord ++ tailWord_223595).sum := by decide
  have hdescent : baseEnd_223595 < baseStart_223595 := by decide
  rcases family_descends (prefixWord ++ tailWord_223595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223612 : List Nat := [2, 2, 2, 1, 1, 1, 2, 6, 1, 5]
def baseStart_223612 : Nat := 118140960795 + 223612 * 2 ^ 59
def prefixEnd_223612 : Nat := 4983230072969 + 3 ^ 40 * 223612 * 2
def baseEnd_223612 : Nat := 38273478704428116907211

theorem tailTrace_223612 : CollatzResearch.WordTrace tailWord_223612 prefixEnd_223612 38273478704428116907211 := by
  unfold tailWord_223612
  simp only [CollatzResearch.WordTrace]
  refine ⟨4077899832949694367128545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5437199777266259156171393 4077899832949694367128545)
  ·
    refine ⟨3058424874712270775346409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4077899832949694367128545 3058424874712270775346409)
    ·
      refine ⟨2293818656034203081509807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3058424874712270775346409 2293818656034203081509807)
      ·
        refine ⟨3440727984051304622264711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2293818656034203081509807 3440727984051304622264711)
        ·
          refine ⟨5161091976076956933397067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3440727984051304622264711 5161091976076956933397067)
          ·
            refine ⟨7741637964115435400095601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5161091976076956933397067 7741637964115435400095601)
            ·
              refine ⟨5806228473086576550071701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7741637964115435400095601 5806228473086576550071701)
              ·
                refine ⟨272166959675933275784611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5806228473086576550071701 272166959675933275784611)
                ·
                  refine ⟨408250439513899913676917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272166959675933275784611 408250439513899913676917)
                  ·
                    refine ⟨38273478704428116907211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 408250439513899913676917 38273478704428116907211)
                    ·
                      rfl

theorem cell23_223612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_223612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223612 prefixEnd_223612 := by exact prefixLift 223612
  have htrace : WordTrace (prefixWord ++ tailWord_223612) baseStart_223612 baseEnd_223612 := by
    simpa [prefixWord, tailWord_223612, baseEnd_223612] using wordTrace_append hprefix tailTrace_223612
  have hstable : (prefixWord ++ tailWord_223612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223612).length < 2 ^ (prefixWord ++ tailWord_223612).sum := by decide
  have hdescent : baseEnd_223612 < baseStart_223612 := by decide
  rcases family_descends (prefixWord ++ tailWord_223612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223615 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 4]
def baseStart_223615 : Nat := 118140960795 + 223615 * 2 ^ 59
def prefixEnd_223615 : Nat := 4983230072969 + 3 ^ 40 * 223615 * 2
def baseEnd_223615 : Nat := 114821976555247838984119

theorem tailTrace_223615 : CollatzResearch.WordTrace tailWord_223615 prefixEnd_223615 114821976555247838984119 := by
  unfold tailWord_223615
  simp only [CollatzResearch.WordTrace]
  refine ⟨8155909084888520246616299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5437272723259013497744199 8155909084888520246616299)
  ·
    refine ⟨12233863627332780369924449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8155909084888520246616299 12233863627332780369924449)
    ·
      refine ⟨9175397720499585277443337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12233863627332780369924449 9175397720499585277443337)
      ·
        refine ⟨6881548290374688958082503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9175397720499585277443337 6881548290374688958082503)
        ·
          refine ⟨10322322435562033437123755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6881548290374688958082503 10322322435562033437123755)
          ·
            refine ⟨15483483653343050155685633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10322322435562033437123755 15483483653343050155685633)
            ·
              refine ⟨11612612740007287616764225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15483483653343050155685633 11612612740007287616764225)
              ·
                refine ⟨8709459555005465712573169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11612612740007287616764225 8709459555005465712573169)
                ·
                  refine ⟨6532094666254099284429877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8709459555005465712573169 6532094666254099284429877)
                  ·
                    refine ⟨612383874961321807915301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6532094666254099284429877 612383874961321807915301)
                    ·
                      refine ⟨114821976555247838984119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 612383874961321807915301 114821976555247838984119)
                      ·
                        rfl

theorem cell23_223615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_223615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223615 prefixEnd_223615 := by exact prefixLift 223615
  have htrace : WordTrace (prefixWord ++ tailWord_223615) baseStart_223615 baseEnd_223615 := by
    simpa [prefixWord, tailWord_223615, baseEnd_223615] using wordTrace_append hprefix tailTrace_223615
  have hstable : (prefixWord ++ tailWord_223615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223615).length < 2 ^ (prefixWord ++ tailWord_223615).sum := by decide
  have hdescent : baseEnd_223615 < baseStart_223615 := by decide
  rcases family_descends (prefixWord ++ tailWord_223615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223632 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 3, 8, 2]
def baseStart_223632 : Nat := 118140960795 + 223632 * 2 ^ 59
def prefixEnd_223632 : Nat := 4983230072969 + 3 ^ 40 * 223632 * 2
def baseEnd_223632 : Nat := 114830705726374272471541

theorem tailTrace_223632 : CollatzResearch.WordTrace tailWord_223632 prefixEnd_223632 114830705726374272471541 := by
  unfold tailWord_223632
  simp only [CollatzResearch.WordTrace]
  refine ⟨4078264562913466074992575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5437686083884621433323433 4078264562913466074992575)
  ·
    refine ⟨6117396844370199112488863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4078264562913466074992575 6117396844370199112488863)
    ·
      refine ⟨9176095266555298668733295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6117396844370199112488863 9176095266555298668733295)
      ·
        refine ⟨13764142899832948003099943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9176095266555298668733295 13764142899832948003099943)
        ·
          refine ⟨20646214349749422004649915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13764142899832948003099943 20646214349749422004649915)
          ·
            refine ⟨30969321524624133006974873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20646214349749422004649915 30969321524624133006974873)
            ·
              refine ⟨23226991143468099755231155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30969321524624133006974873 23226991143468099755231155)
              ·
                refine ⟨34840486715202149632846733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23226991143468099755231155 34840486715202149632846733)
                ·
                  refine ⟨13065182518200806112317525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34840486715202149632846733 13065182518200806112317525)
                  ·
                    refine ⟨153107607635165696628721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13065182518200806112317525 153107607635165696628721)
                    ·
                      refine ⟨114830705726374272471541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 153107607635165696628721 114830705726374272471541)
                      ·
                        rfl

theorem cell23_223632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 8, 2].length) (baseStart_223632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223632 prefixEnd_223632 := by exact prefixLift 223632
  have htrace : WordTrace (prefixWord ++ tailWord_223632) baseStart_223632 baseEnd_223632 := by
    simpa [prefixWord, tailWord_223632, baseEnd_223632] using wordTrace_append hprefix tailTrace_223632
  have hstable : (prefixWord ++ tailWord_223632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223632).length < 2 ^ (prefixWord ++ tailWord_223632).sum := by decide
  have hdescent : baseEnd_223632 < baseStart_223632 := by decide
  rcases family_descends (prefixWord ++ tailWord_223632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223652 : List Nat := [2, 3, 1, 2, 1, 1, 2, 4, 1, 1, 5]
def baseStart_223652 : Nat := 118140960795 + 223652 * 2 ^ 59
def prefixEnd_223652 : Nat := 4983230072969 + 3 ^ 40 * 223652 * 2
def baseEnd_223652 : Nat := 114840975339464194221449

theorem tailTrace_223652 : CollatzResearch.WordTrace tailWord_223652 prefixEnd_223652 114840975339464194221449 := by
  unfold tailWord_223652
  simp only [CollatzResearch.WordTrace]
  refine ⟨4078629292877237782856605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5438172390502983710475473 4078629292877237782856605)
  ·
    refine ⟨1529485984828964168571227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4078629292877237782856605 1529485984828964168571227)
    ·
      refine ⟨2294228977243446252856841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1529485984828964168571227 2294228977243446252856841)
      ·
        refine ⟨1720671732932584689642631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2294228977243446252856841 1720671732932584689642631)
        ·
          refine ⟨2581007599398877034463947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1720671732932584689642631 2581007599398877034463947)
          ·
            refine ⟨3871511399098315551695921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2581007599398877034463947 3871511399098315551695921)
            ·
              refine ⟨2903633549323736663771941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3871511399098315551695921 2903633549323736663771941)
              ·
                refine ⟨544431290498200624457239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2903633549323736663771941 544431290498200624457239)
                ·
                  refine ⟨816646935747300936685859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 544431290498200624457239 816646935747300936685859)
                  ·
                    refine ⟨1224970403620951405028789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 816646935747300936685859 1224970403620951405028789)
                    ·
                      refine ⟨114840975339464194221449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1224970403620951405028789 114840975339464194221449)
                      ·
                        rfl

theorem cell23_223652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_223652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223652 prefixEnd_223652 := by exact prefixLift 223652
  have htrace : WordTrace (prefixWord ++ tailWord_223652) baseStart_223652 baseEnd_223652 := by
    simpa [prefixWord, tailWord_223652, baseEnd_223652] using wordTrace_append hprefix tailTrace_223652
  have hstable : (prefixWord ++ tailWord_223652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223652).length < 2 ^ (prefixWord ++ tailWord_223652).sum := by decide
  have hdescent : baseEnd_223652 < baseStart_223652 := by decide
  rcases family_descends (prefixWord ++ tailWord_223652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223666 : List Nat := [3, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2]
def baseStart_223666 : Nat := 118140960795 + 223666 * 2 ^ 59
def prefixEnd_223666 : Nat := 4983230072969 + 3 ^ 40 * 223666 * 2
def baseEnd_223666 : Nat := 114848164068627139446385

theorem tailTrace_223666 : CollatzResearch.WordTrace tailWord_223666 prefixEnd_223666 114848164068627139446385 := by
  unfold tailWord_223666
  simp only [CollatzResearch.WordTrace]
  refine ⟨2039442301925938989180713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5438512805135837304481901 2039442301925938989180713)
  ·
    refine ⟨1529581726444454241885535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2039442301925938989180713 1529581726444454241885535)
    ·
      refine ⟨2294372589666681362828303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1529581726444454241885535 2294372589666681362828303)
      ·
        refine ⟨3441558884500022044242455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2294372589666681362828303 3441558884500022044242455)
        ·
          refine ⟨5162338326750033066363683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3441558884500022044242455 5162338326750033066363683)
          ·
            refine ⟨7743507490125049599545525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5162338326750033066363683 7743507490125049599545525)
            ·
              refine ⟨725953827199223399957393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7743507490125049599545525 725953827199223399957393)
              ·
                refine ⟨544465370399417549968045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 725953827199223399957393 544465370399417549968045)
                ·
                  refine ⟨204174513899781581238017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 544465370399417549968045 204174513899781581238017)
                  ·
                    refine ⟨153130885424836185928513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 204174513899781581238017 153130885424836185928513)
                    ·
                      refine ⟨114848164068627139446385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 153130885424836185928513 114848164068627139446385)
                      ·
                        rfl

theorem cell23_223666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2].length) (baseStart_223666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223666 prefixEnd_223666 := by exact prefixLift 223666
  have htrace : WordTrace (prefixWord ++ tailWord_223666) baseStart_223666 baseEnd_223666 := by
    simpa [prefixWord, tailWord_223666, baseEnd_223666] using wordTrace_append hprefix tailTrace_223666
  have hstable : (prefixWord ++ tailWord_223666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223666).length < 2 ^ (prefixWord ++ tailWord_223666).sum := by decide
  have hdescent : baseEnd_223666 < baseStart_223666 := by decide
  rcases family_descends (prefixWord ++ tailWord_223666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223675 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 6]
def baseStart_223675 : Nat := 118140960795 + 223675 * 2 ^ 59
def prefixEnd_223675 : Nat := 4983230072969 + 3 ^ 40 * 223675 * 2
def baseEnd_223675 : Nat := 114852785394517604233843

theorem tailTrace_223675 : CollatzResearch.WordTrace tailWord_223675 prefixEnd_223675 114852785394517604233843 := by
  unfold tailWord_223675
  simp only [CollatzResearch.WordTrace]
  refine ⟨8158097464671150493800479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5438731643114100329200319 8158097464671150493800479)
  ·
    refine ⟨12237146197006725740700719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8158097464671150493800479 12237146197006725740700719)
    ·
      refine ⟨18355719295510088611051079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12237146197006725740700719 18355719295510088611051079)
      ·
        refine ⟨27533578943265132916576619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18355719295510088611051079 27533578943265132916576619)
        ·
          refine ⟨41300368414897699374864929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27533578943265132916576619 41300368414897699374864929)
          ·
            refine ⟨30975276311173274531148697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41300368414897699374864929 30975276311173274531148697)
            ·
              refine ⟨23231457233379955898361523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30975276311173274531148697 23231457233379955898361523)
              ·
                refine ⟨34847185850069933847542285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23231457233379955898361523 34847185850069933847542285)
                ·
                  refine ⟨13067694693776225192828357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34847185850069933847542285 13067694693776225192828357)
                  ·
                    refine ⟨2450192755083042223655317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13067694693776225192828357 2450192755083042223655317)
                    ·
                      refine ⟨114852785394517604233843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2450192755083042223655317 114852785394517604233843)
                      ·
                        rfl

theorem cell23_223675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 6].length) (baseStart_223675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223675 prefixEnd_223675 := by exact prefixLift 223675
  have htrace : WordTrace (prefixWord ++ tailWord_223675) baseStart_223675 baseEnd_223675 := by
    simpa [prefixWord, tailWord_223675, baseEnd_223675] using wordTrace_append hprefix tailTrace_223675
  have hstable : (prefixWord ++ tailWord_223675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223675).length < 2 ^ (prefixWord ++ tailWord_223675).sum := by decide
  have hdescent : baseEnd_223675 < baseStart_223675 := by decide
  rcases family_descends (prefixWord ++ tailWord_223675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223700 : List Nat := [2, 4, 1, 2, 2, 1, 2, 4, 1, 2, 2]
def baseStart_223700 : Nat := 118140960795 + 223700 * 2 ^ 59
def prefixEnd_223700 : Nat := 4983230072969 + 3 ^ 40 * 223700 * 2
def baseEnd_223700 : Nat := 114865622410880006421229

theorem tailTrace_223700 : CollatzResearch.WordTrace tailWord_223700 prefixEnd_223700 114865622410880006421229 := by
  unfold tailWord_223700
  simp only [CollatzResearch.WordTrace]
  refine ⟨4079504644790289881730277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5439339526387053175640369 4079504644790289881730277)
  ·
    refine ⟨764907120898179352824427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4079504644790289881730277 764907120898179352824427)
    ·
      refine ⟨1147360681347269029236641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 764907120898179352824427 1147360681347269029236641)
      ·
        refine ⟨860520511010451771927481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1147360681347269029236641 860520511010451771927481)
        ·
          refine ⟨645390383257838828945611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 860520511010451771927481 645390383257838828945611)
          ·
            refine ⟨968085574886758243418417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645390383257838828945611 968085574886758243418417)
            ·
              refine ⟨726064181165068682563813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 968085574886758243418417 726064181165068682563813)
              ·
                refine ⟨136137033968450377980715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 726064181165068682563813 136137033968450377980715)
                ·
                  refine ⟨204205550952675566971073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136137033968450377980715 204205550952675566971073)
                  ·
                    refine ⟨153154163214506675228305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 204205550952675566971073 153154163214506675228305)
                    ·
                      refine ⟨114865622410880006421229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 153154163214506675228305 114865622410880006421229)
                      ·
                        rfl

theorem cell23_223700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_223700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223700 prefixEnd_223700 := by exact prefixLift 223700
  have htrace : WordTrace (prefixWord ++ tailWord_223700) baseStart_223700 baseEnd_223700 := by
    simpa [prefixWord, tailWord_223700, baseEnd_223700] using wordTrace_append hprefix tailTrace_223700
  have hstable : (prefixWord ++ tailWord_223700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223700).length < 2 ^ (prefixWord ++ tailWord_223700).sum := by decide
  have hdescent : baseEnd_223700 < baseStart_223700 := by decide
  rcases family_descends (prefixWord ++ tailWord_223700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223767 : List Nat := [1, 1, 3, 6, 1, 2, 2, 1, 2, 1, 3]
def baseStart_223767 : Nat := 118140960795 + 223767 * 2 ^ 59
def prefixEnd_223767 : Nat := 4983230072969 + 3 ^ 40 * 223767 * 2
def baseEnd_223767 : Nat := 114900025614731244283421

theorem tailTrace_223767 : CollatzResearch.WordTrace tailWord_223767 prefixEnd_223767 114900025614731244283421 := by
  unfold tailWord_223767
  simp only [CollatzResearch.WordTrace]
  refine ⟨8161452980337850206149555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5440968653558566804099703 8161452980337850206149555)
  ·
    refine ⟨12242179470506775309224333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8161452980337850206149555 12242179470506775309224333)
    ·
      refine ⟨4590817301440040740959125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12242179470506775309224333 4590817301440040740959125)
      ·
        refine ⟨215194561005001909732459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4590817301440040740959125 215194561005001909732459)
        ·
          refine ⟨322791841507502864598689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215194561005001909732459 322791841507502864598689)
          ·
            refine ⟨242093881130627148449017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322791841507502864598689 242093881130627148449017)
            ·
              refine ⟨181570410847970361336763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242093881130627148449017 181570410847970361336763)
              ·
                refine ⟨272355616271955542005145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181570410847970361336763 272355616271955542005145)
                ·
                  refine ⟨204266712203966656503859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 272355616271955542005145 204266712203966656503859)
                  ·
                    refine ⟨306400068305949984755789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 204266712203966656503859 306400068305949984755789)
                    ·
                      refine ⟨114900025614731244283421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 306400068305949984755789 114900025614731244283421)
                      ·
                        rfl

theorem cell23_223767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_223767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223767 prefixEnd_223767 := by exact prefixLift 223767
  have htrace : WordTrace (prefixWord ++ tailWord_223767) baseStart_223767 baseEnd_223767 := by
    simpa [prefixWord, tailWord_223767, baseEnd_223767] using wordTrace_append hprefix tailTrace_223767
  have hstable : (prefixWord ++ tailWord_223767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223767).length < 2 ^ (prefixWord ++ tailWord_223767).sum := by decide
  have hdescent : baseEnd_223767 < baseStart_223767 := by decide
  rcases family_descends (prefixWord ++ tailWord_223767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223792 : List Nat := [2, 1, 1, 1, 2, 3, 2, 3, 1, 7]
def baseStart_223792 : Nat := 118140960795 + 223792 * 2 ^ 59
def prefixEnd_223792 : Nat := 4983230072969 + 3 ^ 40 * 223792 * 2
def baseEnd_223792 : Nat := 38304287543697882156935

theorem tailTrace_223792 : CollatzResearch.WordTrace tailWord_223792 prefixEnd_223792 38304287543697882156935 := by
  unfold tailWord_223792
  simp only [CollatzResearch.WordTrace]
  refine ⟨4081182402623639737904815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5441576536831519650539753 4081182402623639737904815)
  ·
    refine ⟨6121773603935459606857223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4081182402623639737904815 6121773603935459606857223)
    ·
      refine ⟨9182660405903189410285835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6121773603935459606857223 9182660405903189410285835)
      ·
        refine ⟨13773990608854784115428753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9182660405903189410285835 13773990608854784115428753)
        ·
          refine ⟨10330492956641088086571565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13773990608854784115428753 10330492956641088086571565)
          ·
            refine ⟨3873934858740408032464337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10330492956641088086571565 3873934858740408032464337)
            ·
              refine ⟨2905451144055306024348253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3873934858740408032464337 2905451144055306024348253)
              ·
                refine ⟨1089544179020739759130595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2905451144055306024348253 1089544179020739759130595)
                ·
                  refine ⟨1634316268531109638695893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1089544179020739759130595 1634316268531109638695893)
                  ·
                    refine ⟨38304287543697882156935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1634316268531109638695893 38304287543697882156935)
                    ·
                      rfl

theorem cell23_223792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 1, 7].length) (baseStart_223792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223792 prefixEnd_223792 := by exact prefixLift 223792
  have htrace : WordTrace (prefixWord ++ tailWord_223792) baseStart_223792 baseEnd_223792 := by
    simpa [prefixWord, tailWord_223792, baseEnd_223792] using wordTrace_append hprefix tailTrace_223792
  have hstable : (prefixWord ++ tailWord_223792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223792).length < 2 ^ (prefixWord ++ tailWord_223792).sum := by decide
  have hdescent : baseEnd_223792 < baseStart_223792 := by decide
  rcases family_descends (prefixWord ++ tailWord_223792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223813 : List Nat := [1, 3, 1, 1, 1, 7, 2, 2, 5]
def baseStart_223813 : Nat := 118140960795 + 223813 * 2 ^ 59
def prefixEnd_223813 : Nat := 4983230072969 + 3 ^ 40 * 223813 * 2
def baseEnd_223813 : Nat := 12769293969426451589801

theorem tailTrace_223813 : CollatzResearch.WordTrace tailWord_223813 prefixEnd_223813 12769293969426451589801 := by
  unfold tailWord_223813
  simp only [CollatzResearch.WordTrace]
  refine ⟨8163130738171200062324093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5442087158780800041549395 8163130738171200062324093)
  ·
    refine ⟨3061174026814200023371535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8163130738171200062324093 3061174026814200023371535)
    ·
      refine ⟨4591761040221300035057303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3061174026814200023371535 4591761040221300035057303)
      ·
        refine ⟨6887641560331950052585955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4591761040221300035057303 6887641560331950052585955)
        ·
          refine ⟨10331462340497925078878933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6887641560331950052585955 10331462340497925078878933)
          ·
            refine ⟨242143648605420119036225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 10331462340497925078878933 242143648605420119036225)
            ·
              refine ⟨181607736454065089277169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242143648605420119036225 181607736454065089277169)
              ·
                refine ⟨136205802340548816957877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181607736454065089277169 136205802340548816957877)
                ·
                  refine ⟨12769293969426451589801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136205802340548816957877 12769293969426451589801)
                  ·
                    rfl

theorem cell23_223813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2, 5].length) (baseStart_223813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223813 prefixEnd_223813 := by exact prefixLift 223813
  have htrace : WordTrace (prefixWord ++ tailWord_223813) baseStart_223813 baseEnd_223813 := by
    simpa [prefixWord, tailWord_223813, baseEnd_223813] using wordTrace_append hprefix tailTrace_223813
  have hstable : (prefixWord ++ tailWord_223813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223813).length < 2 ^ (prefixWord ++ tailWord_223813).sum := by decide
  have hdescent : baseEnd_223813 < baseStart_223813 := by decide
  rcases family_descends (prefixWord ++ tailWord_223813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223829 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 4, 1, 4]
def baseStart_223829 : Nat := 118140960795 + 223829 * 2 ^ 59
def prefixEnd_223829 : Nat := 4983230072969 + 3 ^ 40 * 223829 * 2
def baseEnd_223829 : Nat := 114931861415310001708135

theorem tailTrace_223829 : CollatzResearch.WordTrace tailWord_223829 prefixEnd_223829 114931861415310001708135 := by
  unfold tailWord_223829
  simp only [CollatzResearch.WordTrace]
  refine ⟨8163714306113234794906541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5442476204075489863271027 8163714306113234794906541)
  ·
    refine ⟨3061392864792463048089953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8163714306113234794906541 3061392864792463048089953)
    ·
      refine ⟨2296044648594347286067465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3061392864792463048089953 2296044648594347286067465)
      ·
        refine ⟨1722033486445760464550599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2296044648594347286067465 1722033486445760464550599)
        ·
          refine ⟨2583050229668640696825899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1722033486445760464550599 2583050229668640696825899)
          ·
            refine ⟨3874575344502961045238849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2583050229668640696825899 3874575344502961045238849)
            ·
              refine ⟨2905931508377220783929137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3874575344502961045238849 2905931508377220783929137)
              ·
                refine ⟨2179448631282915587946853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2905931508377220783929137 2179448631282915587946853)
                ·
                  refine ⟨408646618365546672740035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2179448631282915587946853 408646618365546672740035)
                  ·
                    refine ⟨612969927548320009110053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 408646618365546672740035 612969927548320009110053)
                    ·
                      refine ⟨114931861415310001708135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 612969927548320009110053 114931861415310001708135)
                      ·
                        rfl

theorem cell23_223829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_223829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223829 prefixEnd_223829 := by exact prefixLift 223829
  have htrace : WordTrace (prefixWord ++ tailWord_223829) baseStart_223829 baseEnd_223829 := by
    simpa [prefixWord, tailWord_223829, baseEnd_223829] using wordTrace_append hprefix tailTrace_223829
  have hstable : (prefixWord ++ tailWord_223829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223829).length < 2 ^ (prefixWord ++ tailWord_223829).sum := by decide
  have hdescent : baseEnd_223829 < baseStart_223829 := by decide
  rcases family_descends (prefixWord ++ tailWord_223829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223873 : List Nat := [1, 2, 4, 2, 1, 1, 1, 6, 1, 4]
def baseStart_223873 : Nat := 118140960795 + 223873 * 2 ^ 59
def prefixEnd_223873 : Nat := 4983230072969 + 3 ^ 40 * 223873 * 2
def baseEnd_223873 : Nat := 38318151521369276519311

theorem tailTrace_223873 : CollatzResearch.WordTrace tailWord_223873 prefixEnd_223873 38318151521369276519311 := by
  unfold tailWord_223873
  simp only [CollatzResearch.WordTrace]
  refine ⟨8165319117953830309508273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5443546078635886873005515 8165319117953830309508273)
  ·
    refine ⟨6123989338465372732131205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8165319117953830309508273 6123989338465372732131205)
    ·
      refine ⟨1148248000962257387274601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6123989338465372732131205 1148248000962257387274601)
      ·
        refine ⟨861186000721693040455951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1148248000962257387274601 861186000721693040455951)
        ·
          refine ⟨1291779001082539560683927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 861186000721693040455951 1291779001082539560683927)
          ·
            refine ⟨1937668501623809341025891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1291779001082539560683927 1937668501623809341025891)
            ·
              refine ⟨2906502752435714011538837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1937668501623809341025891 2906502752435714011538837)
              ·
                refine ⟨136242316520424094290883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2906502752435714011538837 136242316520424094290883)
                ·
                  refine ⟨204363474780636141436325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136242316520424094290883 204363474780636141436325)
                  ·
                    refine ⟨38318151521369276519311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 204363474780636141436325 38318151521369276519311)
                    ·
                      rfl

theorem cell23_223873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_223873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223873 prefixEnd_223873 := by exact prefixLift 223873
  have htrace : WordTrace (prefixWord ++ tailWord_223873) baseStart_223873 baseEnd_223873 := by
    simpa [prefixWord, tailWord_223873, baseEnd_223873] using wordTrace_append hprefix tailTrace_223873
  have hstable : (prefixWord ++ tailWord_223873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223873).length < 2 ^ (prefixWord ++ tailWord_223873).sum := by decide
  have hdescent : baseEnd_223873 < baseStart_223873 := by decide
  rcases family_descends (prefixWord ++ tailWord_223873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223923 : List Nat := [1, 1, 1, 2, 3, 5, 1, 2, 2, 3, 2]
def baseStart_223923 : Nat := 118140960795 + 223923 * 2 ^ 59
def prefixEnd_223923 : Nat := 4983230072969 + 3 ^ 40 * 223923 * 2
def baseEnd_223923 : Nat := 114980128596832633932703

theorem tailTrace_223923 : CollatzResearch.WordTrace tailWord_223923 prefixEnd_223923 114980128596832633932703 := by
  unfold tailWord_223923
  simp only [CollatzResearch.WordTrace]
  refine ⟨8167142767772688848828423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5444761845181792565885615 8167142767772688848828423)
  ·
    refine ⟨12250714151659033273242635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8167142767772688848828423 12250714151659033273242635)
    ·
      refine ⟨18376071227488549909863953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12250714151659033273242635 18376071227488549909863953)
      ·
        refine ⟨13782053420616412432397965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18376071227488549909863953 13782053420616412432397965)
        ·
          refine ⟨5168270032731154662149237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13782053420616412432397965 5168270032731154662149237)
          ·
            refine ⟨484525315568545749576491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5168270032731154662149237 484525315568545749576491)
            ·
              refine ⟨726787973352818624364737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484525315568545749576491 726787973352818624364737)
              ·
                refine ⟨545090980014613968273553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 726787973352818624364737 545090980014613968273553)
                ·
                  refine ⟨408818235010960476205165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 545090980014613968273553 408818235010960476205165)
                  ·
                    refine ⟨153306838129110178576937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 408818235010960476205165 153306838129110178576937)
                    ·
                      refine ⟨114980128596832633932703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 153306838129110178576937 114980128596832633932703)
                      ·
                        rfl

theorem cell23_223923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 3, 2].length) (baseStart_223923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223923 prefixEnd_223923 := by exact prefixLift 223923
  have htrace : WordTrace (prefixWord ++ tailWord_223923) baseStart_223923 baseEnd_223923 := by
    simpa [prefixWord, tailWord_223923, baseEnd_223923] using wordTrace_append hprefix tailTrace_223923
  have hstable : (prefixWord ++ tailWord_223923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223923).length < 2 ^ (prefixWord ++ tailWord_223923).sum := by decide
  have hdescent : baseEnd_223923 < baseStart_223923 := by decide
  rcases family_descends (prefixWord ++ tailWord_223923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223937 : List Nat := [1, 2, 6, 2, 1, 2, 2, 1, 6]
def baseStart_223937 : Nat := 118140960795 + 223937 * 2 ^ 59
def prefixEnd_223937 : Nat := 4983230072969 + 3 ^ 40 * 223937 * 2
def baseEnd_223937 : Nat := 12776368591777286573071

theorem tailTrace_223937 : CollatzResearch.WordTrace tailWord_223937 prefixEnd_223937 12776368591777286573071 := by
  unfold tailWord_223937
  simp only [CollatzResearch.WordTrace]
  refine ⟨8167653389721969239838065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5445102259814646159892043 8167653389721969239838065)
  ·
    refine ⟨6125740042291476929878549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8167653389721969239838065 6125740042291476929878549)
    ·
      refine ⟨287144064482412981088057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6125740042291476929878549 287144064482412981088057)
      ·
        refine ⟨215358048361809735816043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287144064482412981088057 215358048361809735816043)
        ·
          refine ⟨323037072542714603724065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215358048361809735816043 323037072542714603724065)
          ·
            refine ⟨242277804407035952793049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323037072542714603724065 242277804407035952793049)
            ·
              refine ⟨181708353305276964594787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242277804407035952793049 181708353305276964594787)
              ·
                refine ⟨272562529957915446892181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181708353305276964594787 272562529957915446892181)
                ·
                  refine ⟨12776368591777286573071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 272562529957915446892181 12776368591777286573071)
                  ·
                    rfl

theorem cell23_223937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 6].length) (baseStart_223937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223937 prefixEnd_223937 := by exact prefixLift 223937
  have htrace : WordTrace (prefixWord ++ tailWord_223937) baseStart_223937 baseEnd_223937 := by
    simpa [prefixWord, tailWord_223937, baseEnd_223937] using wordTrace_append hprefix tailTrace_223937
  have hstable : (prefixWord ++ tailWord_223937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223937).length < 2 ^ (prefixWord ++ tailWord_223937).sum := by decide
  have hdescent : baseEnd_223937 < baseStart_223937 := by decide
  rcases family_descends (prefixWord ++ tailWord_223937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223953 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 5, 2, 2]
def baseStart_223953 : Nat := 118140960795 + 223953 * 2 ^ 59
def prefixEnd_223953 : Nat := 4983230072969 + 3 ^ 40 * 223953 * 2
def baseEnd_223953 : Nat := 114995533016467516557565

theorem tailTrace_223953 : CollatzResearch.WordTrace tailWord_223953 prefixEnd_223953 114995533016467516557565 := by
  unfold tailWord_223953
  simp only [CollatzResearch.WordTrace]
  refine ⟨8168236957664003972420513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5445491305109335981613675 8168236957664003972420513)
  ·
    refine ⟨6126177718248002979315385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8168236957664003972420513 6126177718248002979315385)
    ·
      refine ⟨4594633288686002234486539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6126177718248002979315385 4594633288686002234486539)
      ·
        refine ⟨6891949933029003351729809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4594633288686002234486539 6891949933029003351729809)
        ·
          refine ⟨5168962449771752513797357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6891949933029003351729809 5168962449771752513797357)
          ·
            refine ⟨1938360918664407192674009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5168962449771752513797357 1938360918664407192674009)
            ·
              refine ⟨1453770688998305394505507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1938360918664407192674009 1453770688998305394505507)
              ·
                refine ⟨2180656033497458091758261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1453770688998305394505507 2180656033497458091758261)
                ·
                  refine ⟨204436503140386696102337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2180656033497458091758261 204436503140386696102337)
                  ·
                    refine ⟨153327377355290022076753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 204436503140386696102337 153327377355290022076753)
                    ·
                      refine ⟨114995533016467516557565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 153327377355290022076753 114995533016467516557565)
                      ·
                        rfl

theorem cell23_223953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5, 2, 2].length) (baseStart_223953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223953 prefixEnd_223953 := by exact prefixLift 223953
  have htrace : WordTrace (prefixWord ++ tailWord_223953) baseStart_223953 baseEnd_223953 := by
    simpa [prefixWord, tailWord_223953, baseEnd_223953] using wordTrace_append hprefix tailTrace_223953
  have hstable : (prefixWord ++ tailWord_223953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223953).length < 2 ^ (prefixWord ++ tailWord_223953).sum := by decide
  have hdescent : baseEnd_223953 < baseStart_223953 := by decide
  rcases family_descends (prefixWord ++ tailWord_223953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223957 : List Nat := [1, 3, 2, 5, 1, 1, 2, 1, 2, 3, 2]
def baseStart_223957 : Nat := 118140960795 + 223957 * 2 ^ 59
def prefixEnd_223957 : Nat := 4983230072969 + 3 ^ 40 * 223957 * 2
def baseEnd_223957 : Nat := 114997586939085500907547

theorem tailTrace_223957 : CollatzResearch.WordTrace tailWord_223957 prefixEnd_223957 114997586939085500907547 := by
  unfold tailWord_223957
  simp only [CollatzResearch.WordTrace]
  refine ⟨8168382849649512655566125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5445588566433008437044083 8168382849649512655566125)
  ·
    refine ⟨3063143568618567245837297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8168382849649512655566125 3063143568618567245837297)
    ·
      refine ⟨2297357676463925434377973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3063143568618567245837297 2297357676463925434377973)
      ·
        refine ⟨215377282168493009472935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2297357676463925434377973 215377282168493009472935)
        ·
          refine ⟨323065923252739514209403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215377282168493009472935 323065923252739514209403)
          ·
            refine ⟨484598884879109271314105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323065923252739514209403 484598884879109271314105)
            ·
              refine ⟨363449163659331953485579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 484598884879109271314105 363449163659331953485579)
              ·
                refine ⟨545173745488997930228369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363449163659331953485579 545173745488997930228369)
                ·
                  refine ⟨408880309116748447671277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 545173745488997930228369 408880309116748447671277)
                  ·
                    refine ⟨153330115918780667876729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 408880309116748447671277 153330115918780667876729)
                    ·
                      refine ⟨114997586939085500907547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 153330115918780667876729 114997586939085500907547)
                      ·
                        rfl

theorem cell23_223957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_223957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223957 prefixEnd_223957 := by exact prefixLift 223957
  have htrace : WordTrace (prefixWord ++ tailWord_223957) baseStart_223957 baseEnd_223957 := by
    simpa [prefixWord, tailWord_223957, baseEnd_223957] using wordTrace_append hprefix tailTrace_223957
  have hstable : (prefixWord ++ tailWord_223957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223957).length < 2 ^ (prefixWord ++ tailWord_223957).sum := by decide
  have hdescent : baseEnd_223957 < baseStart_223957 := by decide
  rcases family_descends (prefixWord ++ tailWord_223957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223959 : List Nat := [1, 1, 3, 2, 1, 4, 2, 9]
def baseStart_223959 : Nat := 118140960795 + 223959 * 2 ^ 59
def prefixEnd_223959 : Nat := 4983230072969 + 3 ^ 40 * 223959 * 2
def baseEnd_223959 : Nat := 4259207922236833077131

theorem tailTrace_223959 : CollatzResearch.WordTrace tailWord_223959 prefixEnd_223959 4259207922236833077131 := by
  unfold tailWord_223959
  simp only [CollatzResearch.WordTrace]
  refine ⟨8168455795642266997138931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5445637197094844664759287 8168455795642266997138931)
  ·
    refine ⟨12252683693463400495708397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8168455795642266997138931 12252683693463400495708397)
    ·
      refine ⟨4594756385048775185890649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12252683693463400495708397 4594756385048775185890649)
      ·
        refine ⟨3446067288786581389417987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4594756385048775185890649 3446067288786581389417987)
        ·
          refine ⟨5169100933179872084126981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3446067288786581389417987 5169100933179872084126981)
          ·
            refine ⟨969206424971226015773809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5169100933179872084126981 969206424971226015773809)
            ·
              refine ⟨726904818728419511830357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 969206424971226015773809 726904818728419511830357)
              ·
                refine ⟨4259207922236833077131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 726904818728419511830357 4259207922236833077131)
                ·
                  rfl

theorem cell23_223959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 9].length) (baseStart_223959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223959 prefixEnd_223959 := by exact prefixLift 223959
  have htrace : WordTrace (prefixWord ++ tailWord_223959) baseStart_223959 baseEnd_223959 := by
    simpa [prefixWord, tailWord_223959, baseEnd_223959] using wordTrace_append hprefix tailTrace_223959
  have hstable : (prefixWord ++ tailWord_223959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223959).length < 2 ^ (prefixWord ++ tailWord_223959).sum := by decide
  have hdescent : baseEnd_223959 < baseStart_223959 := by decide
  rcases family_descends (prefixWord ++ tailWord_223959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223973 : List Nat := [1, 3, 1, 4, 1, 4, 1, 1, 1, 1, 5]
def baseStart_223973 : Nat := 118140960795 + 223973 * 2 ^ 59
def prefixEnd_223973 : Nat := 4983230072969 + 3 ^ 40 * 223973 * 2
def baseEnd_223973 : Nat := 115005802629557438307473

theorem tailTrace_223973 : CollatzResearch.WordTrace tailWord_223973 prefixEnd_223973 115005802629557438307473 := by
  unfold tailWord_223973
  simp only [CollatzResearch.WordTrace]
  refine ⟨8168966417591547388148573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5445977611727698258765715 8168966417591547388148573)
  ·
    refine ⟨3063362406596830270555715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8168966417591547388148573 3063362406596830270555715)
    ·
      refine ⟨4595043609895245405833573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3063362406596830270555715 4595043609895245405833573)
      ·
        refine ⟨861570676855358513593795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4595043609895245405833573 861570676855358513593795)
        ·
          refine ⟨1292356015283037770390693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 861570676855358513593795 1292356015283037770390693)
          ·
            refine ⟨242316752865569581948255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1292356015283037770390693 242316752865569581948255)
            ·
              refine ⟨363475129298354372922383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242316752865569581948255 363475129298354372922383)
              ·
                refine ⟨545212693947531559383575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363475129298354372922383 545212693947531559383575)
                ·
                  refine ⟨817819040921297339075363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 545212693947531559383575 817819040921297339075363)
                  ·
                    refine ⟨1226728561381946008613045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 817819040921297339075363 1226728561381946008613045)
                    ·
                      refine ⟨115005802629557438307473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1226728561381946008613045 115005802629557438307473)
                      ·
                        rfl

theorem cell23_223973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_223973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223973 prefixEnd_223973 := by exact prefixLift 223973
  have htrace : WordTrace (prefixWord ++ tailWord_223973) baseStart_223973 baseEnd_223973 := by
    simpa [prefixWord, tailWord_223973, baseEnd_223973] using wordTrace_append hprefix tailTrace_223973
  have hstable : (prefixWord ++ tailWord_223973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223973).length < 2 ^ (prefixWord ++ tailWord_223973).sum := by decide
  have hdescent : baseEnd_223973 < baseStart_223973 := by decide
  rcases family_descends (prefixWord ++ tailWord_223973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223976 : List Nat := [2, 1, 4, 1, 5, 10]
def baseStart_223976 : Nat := 118140960795 + 223976 * 2 ^ 59
def prefixEnd_223976 : Nat := 4983230072969 + 3 ^ 40 * 223976 * 2
def baseEnd_223976 : Nat := 473281247207905047613

theorem tailTrace_223976 : CollatzResearch.WordTrace tailWord_223976 prefixEnd_223976 473281247207905047613 := by
  unfold tailWord_223976
  simp only [CollatzResearch.WordTrace]
  refine ⟨4084537918290339450253891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5446050557720452600338521 4084537918290339450253891)
  ·
    refine ⟨6126806877435509175380837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4084537918290339450253891 6126806877435509175380837)
    ·
      refine ⟨1148776289519157970383907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6126806877435509175380837 1148776289519157970383907)
      ·
        refine ⟨1723164434278736955575861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1148776289519157970383907 1723164434278736955575861)
        ·
          refine ⟨161546665713631589585237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1723164434278736955575861 161546665713631589585237)
          ·
            refine ⟨473281247207905047613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 161546665713631589585237 473281247207905047613)
            ·
              rfl

theorem cell23_223976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 10].length) (baseStart_223976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223976 prefixEnd_223976 := by exact prefixLift 223976
  have htrace : WordTrace (prefixWord ++ tailWord_223976) baseStart_223976 baseEnd_223976 := by
    simpa [prefixWord, tailWord_223976, baseEnd_223976] using wordTrace_append hprefix tailTrace_223976
  have hstable : (prefixWord ++ tailWord_223976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223976).length < 2 ^ (prefixWord ++ tailWord_223976).sum := by decide
  have hdescent : baseEnd_223976 < baseStart_223976 := by decide
  rcases family_descends (prefixWord ++ tailWord_223976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223999 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 5]
def baseStart_223999 : Nat := 118140960795 + 223999 * 2 ^ 59
def prefixEnd_223999 : Nat := 4983230072969 + 3 ^ 40 * 223999 * 2
def baseEnd_223999 : Nat := 115019153126574336582353

theorem tailTrace_223999 : CollatzResearch.WordTrace tailWord_223999 prefixEnd_223999 115019153126574336582353 := by
  unfold tailWord_223999
  simp only [CollatzResearch.WordTrace]
  refine ⟨8169914715497353828595051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5446609810331569219063367 8169914715497353828595051)
  ·
    refine ⟨12254872073246030742892577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8169914715497353828595051 12254872073246030742892577)
    ·
      refine ⟨9191154054934523057169433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12254872073246030742892577 9191154054934523057169433)
      ·
        refine ⟨6893365541200892292877075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9191154054934523057169433 6893365541200892292877075)
        ·
          refine ⟨10340048311801338439315613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6893365541200892292877075 10340048311801338439315613)
          ·
            refine ⟨3877518116925501914743355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10340048311801338439315613 3877518116925501914743355)
            ·
              refine ⟨5816277175388252872115033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3877518116925501914743355 5816277175388252872115033)
              ·
                refine ⟨4362207881541189654086275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5816277175388252872115033 4362207881541189654086275)
                ·
                  refine ⟨6543311822311784481129413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4362207881541189654086275 6543311822311784481129413)
                  ·
                    refine ⟨1226870966683459590211765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6543311822311784481129413 1226870966683459590211765)
                    ·
                      refine ⟨115019153126574336582353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1226870966683459590211765 115019153126574336582353)
                      ·
                        rfl

theorem cell23_223999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_223999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_223999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_223999 prefixEnd_223999 := by exact prefixLift 223999
  have htrace : WordTrace (prefixWord ++ tailWord_223999) baseStart_223999 baseEnd_223999 := by
    simpa [prefixWord, tailWord_223999, baseEnd_223999] using wordTrace_append hprefix tailTrace_223999
  have hstable : (prefixWord ++ tailWord_223999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223999).length < 2 ^ (prefixWord ++ tailWord_223999).sum := by decide
  have hdescent : baseEnd_223999 < baseStart_223999 := by decide
  rcases family_descends (prefixWord ++ tailWord_223999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224019 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 1, 8]
def baseStart_224019 : Nat := 118140960795 + 224019 * 2 ^ 59
def prefixEnd_224019 : Nat := 4983230072969 + 3 ^ 40 * 224019 * 2
def baseEnd_224019 : Nat := 38343140913221419444087

theorem tailTrace_224019 : CollatzResearch.WordTrace tailWord_224019 prefixEnd_224019 38343140913221419444087 := by
  unfold tailWord_224019
  simp only [CollatzResearch.WordTrace]
  refine ⟨8170644175424897244323111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5447096116949931496215407 8170644175424897244323111)
  ·
    refine ⟨12255966263137345866484667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8170644175424897244323111 12255966263137345866484667)
    ·
      refine ⟨18383949394706018799727001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12255966263137345866484667 18383949394706018799727001)
      ·
        refine ⟨13787962046029514099795251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18383949394706018799727001 13787962046029514099795251)
        ·
          refine ⟨20681943069044271149692877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13787962046029514099795251 20681943069044271149692877)
          ·
            refine ⟨7755728650891601681134829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20681943069044271149692877 7755728650891601681134829)
            ·
              refine ⟨2908398244084350630425561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7755728650891601681134829 2908398244084350630425561)
              ·
                refine ⟨2181298683063262972819171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2908398244084350630425561 2181298683063262972819171)
                ·
                  refine ⟨3271948024594894459228757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2181298683063262972819171 3271948024594894459228757)
                  ·
                    refine ⟨38343140913221419444087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3271948024594894459228757 38343140913221419444087)
                    ·
                      rfl

theorem cell23_224019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 8].length) (baseStart_224019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224019 prefixEnd_224019 := by exact prefixLift 224019
  have htrace : WordTrace (prefixWord ++ tailWord_224019) baseStart_224019 baseEnd_224019 := by
    simpa [prefixWord, tailWord_224019, baseEnd_224019] using wordTrace_append hprefix tailTrace_224019
  have hstable : (prefixWord ++ tailWord_224019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224019).length < 2 ^ (prefixWord ++ tailWord_224019).sum := by decide
  have hdescent : baseEnd_224019 < baseStart_224019 := by decide
  rcases family_descends (prefixWord ++ tailWord_224019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224054 : List Nat := [5, 1, 2, 2, 3, 1, 1, 1, 1, 3, 3]
def baseStart_224054 : Nat := 118140960795 + 224054 * 2 ^ 59
def prefixEnd_224054 : Nat := 4983230072969 + 3 ^ 40 * 224054 * 2
def baseEnd_224054 : Nat := 115047394562571621394601

theorem tailTrace_224054 : CollatzResearch.WordTrace tailWord_224054 prefixEnd_224054 115047394562571621394601 := by
  unfold tailWord_224054
  simp only [CollatzResearch.WordTrace]
  refine ⟨510745045643631138865451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5447947153532065481231477 510745045643631138865451)
  ·
    refine ⟨766117568465446708298177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 510745045643631138865451 766117568465446708298177)
    ·
      refine ⟨574588176349085031223633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 766117568465446708298177 574588176349085031223633)
      ·
        refine ⟨430941132261813773417725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 574588176349085031223633 430941132261813773417725)
        ·
          refine ⟨161602924598180165031647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 430941132261813773417725 161602924598180165031647)
          ·
            refine ⟨242404386897270247547471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161602924598180165031647 242404386897270247547471)
            ·
              refine ⟨363606580345905371321207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242404386897270247547471 363606580345905371321207)
              ·
                refine ⟨545409870518858056981811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363606580345905371321207 545409870518858056981811)
                ·
                  refine ⟨818114805778287085472717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 545409870518858056981811 818114805778287085472717)
                  ·
                    refine ⟨306793052166857657052269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 818114805778287085472717 306793052166857657052269)
                    ·
                      refine ⟨115047394562571621394601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 306793052166857657052269 115047394562571621394601)
                      ·
                        rfl

theorem cell23_224054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_224054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224054 prefixEnd_224054 := by exact prefixLift 224054
  have htrace : WordTrace (prefixWord ++ tailWord_224054) baseStart_224054 baseEnd_224054 := by
    simpa [prefixWord, tailWord_224054, baseEnd_224054] using wordTrace_append hprefix tailTrace_224054
  have hstable : (prefixWord ++ tailWord_224054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224054).length < 2 ^ (prefixWord ++ tailWord_224054).sum := by decide
  have hdescent : baseEnd_224054 < baseStart_224054 := by decide
  rcases family_descends (prefixWord ++ tailWord_224054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224056 : List Nat := [2, 1, 2, 1, 3, 2, 1, 3, 2, 2, 4]
def baseStart_224056 : Nat := 118140960795 + 224056 * 2 ^ 59
def prefixEnd_224056 : Nat := 4983230072969 + 3 ^ 40 * 224056 * 2
def baseEnd_224056 : Nat := 115048421523880613569591

theorem tailTrace_224056 : CollatzResearch.WordTrace tailWord_224056 prefixEnd_224056 115048421523880613569591 := by
  unfold tailWord_224056
  simp only [CollatzResearch.WordTrace]
  refine ⟨4085996838145426281710011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5447995784193901708946681 4085996838145426281710011)
  ·
    refine ⟨6128995257218139422565017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4085996838145426281710011 6128995257218139422565017)
    ·
      refine ⟨4596746442913604566923763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6128995257218139422565017 4596746442913604566923763)
      ·
        refine ⟨6895119664370406850385645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4596746442913604566923763 6895119664370406850385645)
        ·
          refine ⟨2585669874138902568894617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6895119664370406850385645 2585669874138902568894617)
          ·
            refine ⟨1939252405604176926670963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2585669874138902568894617 1939252405604176926670963)
            ·
              refine ⟨2908878608406265390006445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1939252405604176926670963 2908878608406265390006445)
              ·
                refine ⟨1090829478152349521252417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2908878608406265390006445 1090829478152349521252417)
                ·
                  refine ⟨818122108614262140939313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1090829478152349521252417 818122108614262140939313)
                  ·
                    refine ⟨613591581460696605704485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 818122108614262140939313 613591581460696605704485)
                    ·
                      refine ⟨115048421523880613569591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 613591581460696605704485 115048421523880613569591)
                      ·
                        rfl

theorem cell23_224056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_224056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224056 prefixEnd_224056 := by exact prefixLift 224056
  have htrace : WordTrace (prefixWord ++ tailWord_224056) baseStart_224056 baseEnd_224056 := by
    simpa [prefixWord, tailWord_224056, baseEnd_224056] using wordTrace_append hprefix tailTrace_224056
  have hstable : (prefixWord ++ tailWord_224056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224056).length < 2 ^ (prefixWord ++ tailWord_224056).sum := by decide
  have hdescent : baseEnd_224056 < baseStart_224056 := by decide
  rcases family_descends (prefixWord ++ tailWord_224056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224133 : List Nat := [1, 3, 1, 1, 3, 3, 1, 3, 2, 1, 4]
def baseStart_224133 : Nat := 118140960795 + 224133 * 2 ^ 59
def prefixEnd_224133 : Nat := 4983230072969 + 3 ^ 40 * 224133 * 2
def baseEnd_224133 : Nat := 115087959534276812306737

theorem tailTrace_224133 : CollatzResearch.WordTrace tailWord_224133 prefixEnd_224133 115087959534276812306737 := by
  unfold tailWord_224133
  simp only [CollatzResearch.WordTrace]
  refine ⟨8174802097011894713973053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5449868064674596475982035 8174802097011894713973053)
  ·
    refine ⟨3065550786379460517739895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8174802097011894713973053 3065550786379460517739895)
    ·
      refine ⟨4598326179569190776609843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3065550786379460517739895 4598326179569190776609843)
      ·
        refine ⟨6897489269353786164914765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4598326179569190776609843 6897489269353786164914765)
        ·
          refine ⟨2586558476007669811843037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6897489269353786164914765 2586558476007669811843037)
          ·
            refine ⟨969959428502876179441139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2586558476007669811843037 969959428502876179441139)
            ·
              refine ⟨1454939142754314269161709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 969959428502876179441139 1454939142754314269161709)
              ·
                refine ⟨545602178532867850935641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1454939142754314269161709 545602178532867850935641)
                ·
                  refine ⟨409201633899650888201731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 545602178532867850935641 409201633899650888201731)
                  ·
                    refine ⟨613802450849476332302597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 409201633899650888201731 613802450849476332302597)
                    ·
                      refine ⟨115087959534276812306737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 613802450849476332302597 115087959534276812306737)
                      ·
                        rfl

theorem cell23_224133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_224133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224133 prefixEnd_224133 := by exact prefixLift 224133
  have htrace : WordTrace (prefixWord ++ tailWord_224133) baseStart_224133 baseEnd_224133 := by
    simpa [prefixWord, tailWord_224133, baseEnd_224133] using wordTrace_append hprefix tailTrace_224133
  have hstable : (prefixWord ++ tailWord_224133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224133).length < 2 ^ (prefixWord ++ tailWord_224133).sum := by decide
  have hdescent : baseEnd_224133 < baseStart_224133 := by decide
  rcases family_descends (prefixWord ++ tailWord_224133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224167 : List Nat := [1, 1, 6, 1, 3, 1, 1, 1, 2, 4, 2]
def baseStart_224167 : Nat := 118140960795 + 224167 * 2 ^ 59
def prefixEnd_224167 : Nat := 4983230072969 + 3 ^ 40 * 224167 * 2
def baseEnd_224167 : Nat := 115105417876529679281581

theorem tailTrace_224167 : CollatzResearch.WordTrace tailWord_224167 prefixEnd_224167 115105417876529679281581 := by
  unfold tailWord_224167
  simp only [CollatzResearch.WordTrace]
  refine ⟨8176042178888718520710755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5450694785925812347140503 8176042178888718520710755)
  ·
    refine ⟨12264063268333077781066133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8176042178888718520710755 12264063268333077781066133)
    ·
      refine ⟨574877965703113020987475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12264063268333077781066133 574877965703113020987475)
      ·
        refine ⟨862316948554669531481213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574877965703113020987475 862316948554669531481213)
        ·
          refine ⟨323368855708001074305455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 862316948554669531481213 323368855708001074305455)
          ·
            refine ⟨485053283562001611458183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323368855708001074305455 485053283562001611458183)
            ·
              refine ⟨727579925343002417187275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485053283562001611458183 727579925343002417187275)
              ·
                refine ⟨1091369888014503625780913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 727579925343002417187275 1091369888014503625780913)
                ·
                  refine ⟨818527416010877719335685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1091369888014503625780913 818527416010877719335685)
                  ·
                    refine ⟨153473890502039572375441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 818527416010877719335685 153473890502039572375441)
                    ·
                      refine ⟨115105417876529679281581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 153473890502039572375441 115105417876529679281581)
                      ·
                        rfl

theorem cell23_224167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_224167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224167 prefixEnd_224167 := by exact prefixLift 224167
  have htrace : WordTrace (prefixWord ++ tailWord_224167) baseStart_224167 baseEnd_224167 := by
    simpa [prefixWord, tailWord_224167, baseEnd_224167] using wordTrace_append hprefix tailTrace_224167
  have hstable : (prefixWord ++ tailWord_224167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224167).length < 2 ^ (prefixWord ++ tailWord_224167).sum := by decide
  have hdescent : baseEnd_224167 < baseStart_224167 := by decide
  rcases family_descends (prefixWord ++ tailWord_224167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224217 : List Nat := [1, 2, 1, 2, 5, 2, 2, 1, 3, 1, 3]
def baseStart_224217 : Nat := 118140960795 + 224217 * 2 ^ 59
def prefixEnd_224217 : Nat := 4983230072969 + 3 ^ 40 * 224217 * 2
def baseEnd_224217 : Nat := 115131091909254483656351

theorem tailTrace_224217 : CollatzResearch.WordTrace tailWord_224217 prefixEnd_224217 115131091909254483656351 := by
  unfold tailWord_224217
  simp only [CollatzResearch.WordTrace]
  refine ⟨8177865828707577060030905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5451910552471718040020603 8177865828707577060030905)
  ·
    refine ⟨6133399371530682795023179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8177865828707577060030905 6133399371530682795023179)
    ·
      refine ⟨9200099057296024192534769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6133399371530682795023179 9200099057296024192534769)
      ·
        refine ⟨6900074292972018144401077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9200099057296024192534769 6900074292972018144401077)
        ·
          refine ⟨646881964966126701037601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6900074292972018144401077 646881964966126701037601)
          ·
            refine ⟨485161473724595025778201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 646881964966126701037601 485161473724595025778201)
            ·
              refine ⟨363871105293446269333651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 485161473724595025778201 363871105293446269333651)
              ·
                refine ⟨545806657940169404000477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363871105293446269333651 545806657940169404000477)
                ·
                  refine ⟨204677496727563526500179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 545806657940169404000477 204677496727563526500179)
                  ·
                    refine ⟨307016245091345289750269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 204677496727563526500179 307016245091345289750269)
                    ·
                      refine ⟨115131091909254483656351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 307016245091345289750269 115131091909254483656351)
                      ·
                        rfl

theorem cell23_224217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3, 1, 3].length) (baseStart_224217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224217 prefixEnd_224217 := by exact prefixLift 224217
  have htrace : WordTrace (prefixWord ++ tailWord_224217) baseStart_224217 baseEnd_224217 := by
    simpa [prefixWord, tailWord_224217, baseEnd_224217] using wordTrace_append hprefix tailTrace_224217
  have hstable : (prefixWord ++ tailWord_224217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224217).length < 2 ^ (prefixWord ++ tailWord_224217).sum := by decide
  have hdescent : baseEnd_224217 < baseStart_224217 := by decide
  rcases family_descends (prefixWord ++ tailWord_224217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224253 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 3, 2, 4]
def baseStart_224253 : Nat := 118140960795 + 224253 * 2 ^ 59
def prefixEnd_224253 : Nat := 4983230072969 + 3 ^ 40 * 224253 * 2
def baseEnd_224253 : Nat := 115149577212816342806185

theorem tailTrace_224253 : CollatzResearch.WordTrace tailWord_224253 prefixEnd_224253 115149577212816342806185 := by
  unfold tailWord_224253
  simp only [CollatzResearch.WordTrace]
  refine ⟨8179178856577155208341413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5452785904384770138894275 8179178856577155208341413)
  ·
    refine ⟨1533596035608216601564015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8179178856577155208341413 1533596035608216601564015)
    ·
      refine ⟨2300394053412324902346023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1533596035608216601564015 2300394053412324902346023)
      ·
        refine ⟨3450591080118487353519035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2300394053412324902346023 3450591080118487353519035)
        ·
          refine ⟨5175886620177731030278553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3450591080118487353519035 5175886620177731030278553)
          ·
            refine ⟨3881914965133298272708915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5175886620177731030278553 3881914965133298272708915)
            ·
              refine ⟨5822872447699947409063373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3881914965133298272708915 5822872447699947409063373)
              ·
                refine ⟨2183577167887480278398765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5822872447699947409063373 2183577167887480278398765)
                ·
                  refine ⟨818841437957805104399537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2183577167887480278398765 818841437957805104399537)
                  ·
                    refine ⟨614131078468353828299653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 818841437957805104399537 614131078468353828299653)
                    ·
                      refine ⟨115149577212816342806185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 614131078468353828299653 115149577212816342806185)
                      ·
                        rfl

theorem cell23_224253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_224253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224253 prefixEnd_224253 := by exact prefixLift 224253
  have htrace : WordTrace (prefixWord ++ tailWord_224253) baseStart_224253 baseEnd_224253 := by
    simpa [prefixWord, tailWord_224253, baseEnd_224253] using wordTrace_append hprefix tailTrace_224253
  have hstable : (prefixWord ++ tailWord_224253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224253).length < 2 ^ (prefixWord ++ tailWord_224253).sum := by decide
  have hdescent : baseEnd_224253 < baseStart_224253 := by decide
  rcases family_descends (prefixWord ++ tailWord_224253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224323 : List Nat := [1, 1, 1, 3, 1, 2, 4, 2, 2, 6]
def baseStart_224323 : Nat := 118140960795 + 224323 * 2 ^ 59
def prefixEnd_224323 : Nat := 4983230072969 + 3 ^ 40 * 224323 * 2
def baseEnd_224323 : Nat := 38395173619543689643621

theorem tailTrace_224323 : CollatzResearch.WordTrace tailWord_224323 prefixEnd_224323 38395173619543689643621 := by
  unfold tailWord_224323
  simp only [CollatzResearch.WordTrace]
  refine ⟨8181731966323557163389623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5454487977549038108926415 8181731966323557163389623)
  ·
    refine ⟨12272597949485335745084435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8181731966323557163389623 12272597949485335745084435)
    ·
      refine ⟨18408896924228003617626653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12272597949485335745084435 18408896924228003617626653)
      ·
        refine ⟨6903336346585501356609995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18408896924228003617626653 6903336346585501356609995)
        ·
          refine ⟨10355004519878252034914993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6903336346585501356609995 10355004519878252034914993)
          ·
            refine ⟨7766253389908689026186245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10355004519878252034914993 7766253389908689026186245)
            ·
              refine ⟨1456172510607879192409921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7766253389908689026186245 1456172510607879192409921)
              ·
                refine ⟨1092129382955909394307441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1456172510607879192409921 1092129382955909394307441)
                ·
                  refine ⟨819097037216932045730581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1092129382955909394307441 819097037216932045730581)
                  ·
                    refine ⟨38395173619543689643621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 819097037216932045730581 38395173619543689643621)
                    ·
                      rfl

theorem cell23_224323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 6].length) (baseStart_224323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224323 prefixEnd_224323 := by exact prefixLift 224323
  have htrace : WordTrace (prefixWord ++ tailWord_224323) baseStart_224323 baseEnd_224323 := by
    simpa [prefixWord, tailWord_224323, baseEnd_224323] using wordTrace_append hprefix tailTrace_224323
  have hstable : (prefixWord ++ tailWord_224323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224323).length < 2 ^ (prefixWord ++ tailWord_224323).sum := by decide
  have hdescent : baseEnd_224323 < baseStart_224323 := by decide
  rcases family_descends (prefixWord ++ tailWord_224323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224353 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 9]
def baseStart_224353 : Nat := 118140960795 + 224353 * 2 ^ 59
def prefixEnd_224353 : Nat := 4983230072969 + 3 ^ 40 * 224353 * 2
def baseEnd_224353 : Nat := 12800102808696216839525

theorem tailTrace_224353 : CollatzResearch.WordTrace tailWord_224353 prefixEnd_224353 12800102808696216839525 := by
  unfold tailWord_224353
  simp only [CollatzResearch.WordTrace]
  refine ⟨8182826156214872286981713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5455217437476581524654475 8182826156214872286981713)
  ·
    refine ⟨6137119617161154215236285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8182826156214872286981713 6137119617161154215236285)
    ·
      refine ⟨2301419856435432830713607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6137119617161154215236285 2301419856435432830713607)
      ·
        refine ⟨3452129784653149246070411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2301419856435432830713607 3452129784653149246070411)
        ·
          refine ⟨5178194676979723869105617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3452129784653149246070411 5178194676979723869105617)
          ·
            refine ⟨3883646007734792901829213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5178194676979723869105617 3883646007734792901829213)
            ·
              refine ⟨1456367252900547338185955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3883646007734792901829213 1456367252900547338185955)
              ·
                refine ⟨2184550879350821007278933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1456367252900547338185955 2184550879350821007278933)
                ·
                  refine ⟨12800102808696216839525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2184550879350821007278933 12800102808696216839525)
                  ·
                    rfl

theorem cell23_224353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 9].length) (baseStart_224353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224353 prefixEnd_224353 := by exact prefixLift 224353
  have htrace : WordTrace (prefixWord ++ tailWord_224353) baseStart_224353 baseEnd_224353 := by
    simpa [prefixWord, tailWord_224353, baseEnd_224353] using wordTrace_append hprefix tailTrace_224353
  have hstable : (prefixWord ++ tailWord_224353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224353).length < 2 ^ (prefixWord ++ tailWord_224353).sum := by decide
  have hdescent : baseEnd_224353 < baseStart_224353 := by decide
  rcases family_descends (prefixWord ++ tailWord_224353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224380 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 4, 3, 3]
def baseStart_224380 : Nat := 118140960795 + 224380 * 2 ^ 59
def prefixEnd_224380 : Nat := 4983230072969 + 3 ^ 40 * 224380 * 2
def baseEnd_224380 : Nat := 115214789255937345918101

theorem tailTrace_224380 : CollatzResearch.WordTrace tailWord_224380 prefixEnd_224380 115214789255937345918101 := by
  unfold tailWord_224380
  simp only [CollatzResearch.WordTrace]
  refine ⟨4091905463558527949107297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5455873951411370598809729 4091905463558527949107297)
  ·
    refine ⟨3068929097668895961830473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4091905463558527949107297 3068929097668895961830473)
    ·
      refine ⟨2301696823251671971372855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3068929097668895961830473 2301696823251671971372855)
      ·
        refine ⟨3452545234877507957059283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2301696823251671971372855 3452545234877507957059283)
        ·
          refine ⟨5178817852316261935588925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3452545234877507957059283 5178817852316261935588925)
          ·
            refine ⟨1942056694618598225845847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5178817852316261935588925 1942056694618598225845847)
            ·
              refine ⟨2913085041927897338768771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1942056694618598225845847 2913085041927897338768771)
              ·
                refine ⟨4369627562891846008153157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2913085041927897338768771 4369627562891846008153157)
                ·
                  refine ⟨819305168042221126528717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4369627562891846008153157 819305168042221126528717)
                  ·
                    refine ⟨307239438015832922448269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 819305168042221126528717 307239438015832922448269)
                    ·
                      refine ⟨115214789255937345918101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 307239438015832922448269 115214789255937345918101)
                      ·
                        rfl

theorem cell23_224380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_224380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224380 prefixEnd_224380 := by exact prefixLift 224380
  have htrace : WordTrace (prefixWord ++ tailWord_224380) baseStart_224380 baseEnd_224380 := by
    simpa [prefixWord, tailWord_224380, baseEnd_224380] using wordTrace_append hprefix tailTrace_224380
  have hstable : (prefixWord ++ tailWord_224380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224380).length < 2 ^ (prefixWord ++ tailWord_224380).sum := by decide
  have hdescent : baseEnd_224380 < baseStart_224380 := by decide
  rcases family_descends (prefixWord ++ tailWord_224380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224398 : List Nat := [4, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2]
def baseStart_224398 : Nat := 118140960795 + 224398 * 2 ^ 59
def prefixEnd_224398 : Nat := 4983230072969 + 3 ^ 40 * 224398 * 2
def baseEnd_224398 : Nat := 115224031907718275493019

theorem tailTrace_224398 : CollatzResearch.WordTrace tailWord_224398 prefixEnd_224398 115224031907718275493019 := by
  unfold tailWord_224398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1023058430131480621546231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5456311627367896648246565 1023058430131480621546231)
  ·
    refine ⟨1534587645197220932319347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1023058430131480621546231 1534587645197220932319347)
    ·
      refine ⟨2301881467795831398479021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1534587645197220932319347 2301881467795831398479021)
      ·
        refine ⟨863205550423436774429633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2301881467795831398479021 863205550423436774429633)
        ·
          refine ⟨647404162817577580822225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 863205550423436774429633 647404162817577580822225)
          ·
            refine ⟨485553122113183185616669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 647404162817577580822225 485553122113183185616669)
            ·
              refine ⟨182082420792443694606251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 485553122113183185616669 182082420792443694606251)
              ·
                refine ⟨273123631188665541909377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182082420792443694606251 273123631188665541909377)
                ·
                  refine ⟨204842723391499156432033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273123631188665541909377 204842723391499156432033)
                  ·
                    refine ⟨153632042543624367324025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 204842723391499156432033 153632042543624367324025)
                    ·
                      refine ⟨115224031907718275493019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 153632042543624367324025 115224031907718275493019)
                      ·
                        rfl

theorem cell23_224398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_224398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224398 prefixEnd_224398 := by exact prefixLift 224398
  have htrace : WordTrace (prefixWord ++ tailWord_224398) baseStart_224398 baseEnd_224398 := by
    simpa [prefixWord, tailWord_224398, baseEnd_224398] using wordTrace_append hprefix tailTrace_224398
  have hstable : (prefixWord ++ tailWord_224398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224398).length < 2 ^ (prefixWord ++ tailWord_224398).sum := by decide
  have hdescent : baseEnd_224398 < baseStart_224398 := by decide
  rcases family_descends (prefixWord ++ tailWord_224398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224438 : List Nat := [5, 1, 3, 2, 2, 1, 1, 1, 7]
def baseStart_224438 : Nat := 118140960795 + 224438 * 2 ^ 59
def prefixEnd_224438 : Nat := 4983230072969 + 3 ^ 40 * 224438 * 2
def baseEnd_224438 : Nat := 12804952348210902110315

theorem tailTrace_224438 : CollatzResearch.WordTrace tailWord_224438 prefixEnd_224438 12804952348210902110315 := by
  unfold tailWord_224438
  simp only [CollatzResearch.WordTrace]
  refine ⟨511620397556683237739123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5457284240604621202550645 511620397556683237739123)
  ·
    refine ⟨767430596335024856608685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 511620397556683237739123 767430596335024856608685)
    ·
      refine ⟨287786473625634321228257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 767430596335024856608685 287786473625634321228257)
      ·
        refine ⟨215839855219225740921193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287786473625634321228257 215839855219225740921193)
        ·
          refine ⟨161879891414419305690895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215839855219225740921193 161879891414419305690895)
          ·
            refine ⟨242819837121628958536343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161879891414419305690895 242819837121628958536343)
            ·
              refine ⟨364229755682443437804515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242819837121628958536343 364229755682443437804515)
              ·
                refine ⟨546344633523665156706773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 364229755682443437804515 546344633523665156706773)
                ·
                  refine ⟨12804952348210902110315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 546344633523665156706773 12804952348210902110315)
                  ·
                    rfl

theorem cell23_224438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_224438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224438 prefixEnd_224438 := by exact prefixLift 224438
  have htrace : WordTrace (prefixWord ++ tailWord_224438) baseStart_224438 baseEnd_224438 := by
    simpa [prefixWord, tailWord_224438, baseEnd_224438] using wordTrace_append hprefix tailTrace_224438
  have hstable : (prefixWord ++ tailWord_224438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224438).length < 2 ^ (prefixWord ++ tailWord_224438).sum := by decide
  have hdescent : baseEnd_224438 < baseStart_224438 := by decide
  rcases family_descends (prefixWord ++ tailWord_224438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224440 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 3, 4, 3]
def baseStart_224440 : Nat := 118140960795 + 224440 * 2 ^ 59
def prefixEnd_224440 : Nat := 4983230072969 + 3 ^ 40 * 224440 * 2
def baseEnd_224440 : Nat := 115245598095207111167825

theorem tailTrace_224440 : CollatzResearch.WordTrace tailWord_224440 prefixEnd_224440 115245598095207111167825 := by
  unfold tailWord_224440
  simp only [CollatzResearch.WordTrace]
  refine ⟨4092999653449843072699387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5457332871266457430265849 4092999653449843072699387)
  ·
    refine ⟨6139499480174764609049081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4092999653449843072699387 6139499480174764609049081)
    ·
      refine ⟨4604624610131073456786811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6139499480174764609049081 4604624610131073456786811)
      ·
        refine ⟨6906936915196610185180217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4604624610131073456786811 6906936915196610185180217)
        ·
          refine ⟨5180202686397457638885163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6906936915196610185180217 5180202686397457638885163)
          ·
            refine ⟨7770304029596186458327745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5180202686397457638885163 7770304029596186458327745)
            ·
              refine ⟨5827728022197139843745809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7770304029596186458327745 5827728022197139843745809)
              ·
                refine ⟨4370796016647854882809357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5827728022197139843745809 4370796016647854882809357)
                ·
                  refine ⟨1639048506242945581053509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4370796016647854882809357 1639048506242945581053509)
                  ·
                    refine ⟨307321594920552296447533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1639048506242945581053509 307321594920552296447533)
                    ·
                      refine ⟨115245598095207111167825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 307321594920552296447533 115245598095207111167825)
                      ·
                        rfl

theorem cell23_224440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 3, 4, 3].length) (baseStart_224440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224440 prefixEnd_224440 := by exact prefixLift 224440
  have htrace : WordTrace (prefixWord ++ tailWord_224440) baseStart_224440 baseEnd_224440 := by
    simpa [prefixWord, tailWord_224440, baseEnd_224440] using wordTrace_append hprefix tailTrace_224440
  have hstable : (prefixWord ++ tailWord_224440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224440).length < 2 ^ (prefixWord ++ tailWord_224440).sum := by decide
  have hdescent : baseEnd_224440 < baseStart_224440 := by decide
  rcases family_descends (prefixWord ++ tailWord_224440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224447 : List Nat := [1, 1, 2, 2, 2, 2, 5, 1, 3, 4]
def baseStart_224447 : Nat := 118140960795 + 224447 * 2 ^ 59
def prefixEnd_224447 : Nat := 4983230072969 + 3 ^ 40 * 224447 * 2
def baseEnd_224447 : Nat := 38416397486596194593431

theorem tailTrace_224447 : CollatzResearch.WordTrace tailWord_224447 prefixEnd_224447 38416397486596194593431 := by
  unfold tailWord_224447
  simp only [CollatzResearch.WordTrace]
  refine ⟨8186254617874326340903595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5457503078582884227269063 8186254617874326340903595)
  ·
    refine ⟨12279381926811489511355393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8186254617874326340903595 12279381926811489511355393)
    ·
      refine ⟨9209536445108617133516545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12279381926811489511355393 9209536445108617133516545)
      ·
        refine ⟨6907152333831462850137409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9209536445108617133516545 6907152333831462850137409)
        ·
          refine ⟨5180364250373597137603057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6907152333831462850137409 5180364250373597137603057)
          ·
            refine ⟨3885273187780197853202293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5180364250373597137603057 3885273187780197853202293)
            ·
              refine ⟨364244361354393548737715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3885273187780197853202293 364244361354393548737715)
              ·
                refine ⟨546366542031590323106573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 364244361354393548737715 546366542031590323106573)
                ·
                  refine ⟨204887453261846371164965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 546366542031590323106573 204887453261846371164965)
                  ·
                    refine ⟨38416397486596194593431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 204887453261846371164965 38416397486596194593431)
                    ·
                      rfl

theorem cell23_224447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3, 4].length) (baseStart_224447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224447 prefixEnd_224447 := by exact prefixLift 224447
  have htrace : WordTrace (prefixWord ++ tailWord_224447) baseStart_224447 baseEnd_224447 := by
    simpa [prefixWord, tailWord_224447, baseEnd_224447] using wordTrace_append hprefix tailTrace_224447
  have hstable : (prefixWord ++ tailWord_224447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224447).length < 2 ^ (prefixWord ++ tailWord_224447).sum := by decide
  have hdescent : baseEnd_224447 < baseStart_224447 := by decide
  rcases family_descends (prefixWord ++ tailWord_224447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224497 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 3, 5, 2]
def baseStart_224497 : Nat := 118140960795 + 224497 * 2 ^ 59
def prefixEnd_224497 : Nat := 4983230072969 + 3 ^ 40 * 224497 * 2
def baseEnd_224497 : Nat := 115274866492513388155063

theorem tailTrace_224497 : CollatzResearch.WordTrace tailWord_224497 prefixEnd_224497 115274866492513388155063 := by
  unfold tailWord_224497
  simp only [CollatzResearch.WordTrace]
  refine ⟨8188078267693184880223745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5458718845128789920149163 8188078267693184880223745)
  ·
    refine ⟨6141058700769888660167809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8188078267693184880223745 6141058700769888660167809)
    ·
      refine ⟨4605794025577416495125857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6141058700769888660167809 4605794025577416495125857)
      ·
        refine ⟨3454345519183062371344393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4605794025577416495125857 3454345519183062371344393)
        ·
          refine ⟨2590759139387296778508295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3454345519183062371344393 2590759139387296778508295)
          ·
            refine ⟨3886138709080945167762443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2590759139387296778508295 3886138709080945167762443)
            ·
              refine ⟨5829208063621417751643665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3886138709080945167762443 5829208063621417751643665)
              ·
                refine ⟨4371906047716063313732749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5829208063621417751643665 4371906047716063313732749)
                ·
                  refine ⟨1639464767893523742649781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4371906047716063313732749 1639464767893523742649781)
                  ·
                    refine ⟨153699821990017850873417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1639464767893523742649781 153699821990017850873417)
                    ·
                      refine ⟨115274866492513388155063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 153699821990017850873417 115274866492513388155063)
                      ·
                        rfl

theorem cell23_224497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 5, 2].length) (baseStart_224497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224497 prefixEnd_224497 := by exact prefixLift 224497
  have htrace : WordTrace (prefixWord ++ tailWord_224497) baseStart_224497 baseEnd_224497 := by
    simpa [prefixWord, tailWord_224497, baseEnd_224497] using wordTrace_append hprefix tailTrace_224497
  have hstable : (prefixWord ++ tailWord_224497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224497).length < 2 ^ (prefixWord ++ tailWord_224497).sum := by decide
  have hdescent : baseEnd_224497 < baseStart_224497 := by decide
  rcases family_descends (prefixWord ++ tailWord_224497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224538 : List Nat := [3, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3]
def baseStart_224538 : Nat := 118140960795 + 224538 * 2 ^ 59
def prefixEnd_224538 : Nat := 4983230072969 + 3 ^ 40 * 224538 * 2
def baseEnd_224538 : Nat := 115295919199347727742375

theorem tailTrace_224538 : CollatzResearch.WordTrace tailWord_224538 prefixEnd_224538 115295919199347727742375 := by
  unfold tailWord_224538
  simp only [CollatzResearch.WordTrace]
  refine ⟨2047393415136162220616567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5459715773696432588310845 2047393415136162220616567)
  ·
    refine ⟨3071090122704243330924851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2047393415136162220616567 3071090122704243330924851)
    ·
      refine ⟨4606635184056364996387277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3071090122704243330924851 4606635184056364996387277)
      ·
        refine ⟨1727488194021136873645229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4606635184056364996387277 1727488194021136873645229)
        ·
          refine ⟨647808072757926327616961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1727488194021136873645229 647808072757926327616961)
          ·
            refine ⟨485856054568444745712721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 647808072757926327616961 485856054568444745712721)
            ·
              refine ⟨364392040926333559284541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 485856054568444745712721 364392040926333559284541)
              ·
                refine ⟨136647015347375084731703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 364392040926333559284541 136647015347375084731703)
                ·
                  refine ⟨204970523021062627097555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136647015347375084731703 204970523021062627097555)
                  ·
                    refine ⟨307455784531593940646333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 204970523021062627097555 307455784531593940646333)
                    ·
                      refine ⟨115295919199347727742375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 307455784531593940646333 115295919199347727742375)
                      ·
                        rfl

theorem cell23_224538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_224538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224538 prefixEnd_224538 := by exact prefixLift 224538
  have htrace : WordTrace (prefixWord ++ tailWord_224538) baseStart_224538 baseEnd_224538 := by
    simpa [prefixWord, tailWord_224538, baseEnd_224538] using wordTrace_append hprefix tailTrace_224538
  have hstable : (prefixWord ++ tailWord_224538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224538).length < 2 ^ (prefixWord ++ tailWord_224538).sum := by decide
  have hdescent : baseEnd_224538 < baseStart_224538 := by decide
  rcases family_descends (prefixWord ++ tailWord_224538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224541 : List Nat := [1, 4, 2, 3, 1, 1, 4, 1, 1, 5]
def baseStart_224541 : Nat := 118140960795 + 224541 * 2 ^ 59
def prefixEnd_224541 : Nat := 4983230072969 + 3 ^ 40 * 224541 * 2
def baseEnd_224541 : Nat := 38432486547103738668287

theorem tailTrace_224541 : CollatzResearch.WordTrace tailWord_224541 prefixEnd_224541 38432486547103738668287 := by
  unfold tailWord_224541
  simp only [CollatzResearch.WordTrace]
  refine ⟨8189683079533780394825477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5459788719689186929883651 8189683079533780394825477)
  ·
    refine ⟨1535565577412583824029777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8189683079533780394825477 1535565577412583824029777)
    ·
      refine ⟨1151674183059437868022333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1535565577412583824029777 1151674183059437868022333)
      ·
        refine ⟨431877818647289200508375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1151674183059437868022333 431877818647289200508375)
        ·
          refine ⟨647816727970933800762563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431877818647289200508375 647816727970933800762563)
          ·
            refine ⟨971725091956400701143845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647816727970933800762563 971725091956400701143845)
            ·
              refine ⟨182198454741825131464471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 971725091956400701143845 182198454741825131464471)
              ·
                refine ⟨273297682112737697196707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182198454741825131464471 273297682112737697196707)
                ·
                  refine ⟨409946523169106545795061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 273297682112737697196707 409946523169106545795061)
                  ·
                    refine ⟨38432486547103738668287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 409946523169106545795061 38432486547103738668287)
                    ·
                      rfl

theorem cell23_224541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_224541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224541 prefixEnd_224541 := by exact prefixLift 224541
  have htrace : WordTrace (prefixWord ++ tailWord_224541) baseStart_224541 baseEnd_224541 := by
    simpa [prefixWord, tailWord_224541, baseEnd_224541] using wordTrace_append hprefix tailTrace_224541
  have hstable : (prefixWord ++ tailWord_224541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224541).length < 2 ^ (prefixWord ++ tailWord_224541).sum := by decide
  have hdescent : baseEnd_224541 < baseStart_224541 := by decide
  rcases family_descends (prefixWord ++ tailWord_224541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224561 : List Nat := [1, 2, 2, 3, 3, 1, 1, 3, 3, 2, 2]
def baseStart_224561 : Nat := 118140960795 + 224561 * 2 ^ 59
def prefixEnd_224561 : Nat := 4983230072969 + 3 ^ 40 * 224561 * 2
def baseEnd_224561 : Nat := 115307729254401137754769

theorem tailTrace_224561 : CollatzResearch.WordTrace tailWord_224561 prefixEnd_224561 115307729254401137754769 := by
  unfold tailWord_224561
  simp only [CollatzResearch.WordTrace]
  refine ⟨8190412539461323810553537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5460275026307549207035691 8190412539461323810553537)
  ·
    refine ⟨6142809404595992857915153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8190412539461323810553537 6142809404595992857915153)
    ·
      refine ⟨4607107053446994643436365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6142809404595992857915153 4607107053446994643436365)
      ·
        refine ⟨1727665145042622991288637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4607107053446994643436365 1727665145042622991288637)
        ·
          refine ⟨647874429390983621733239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1727665145042622991288637 647874429390983621733239)
          ·
            refine ⟨971811644086475432599859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647874429390983621733239 971811644086475432599859)
            ·
              refine ⟨1457717466129713148899789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 971811644086475432599859 1457717466129713148899789)
              ·
                refine ⟨546644049798642430837421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1457717466129713148899789 546644049798642430837421)
                ·
                  refine ⟨204991518674490911564033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 546644049798642430837421 204991518674490911564033)
                  ·
                    refine ⟨153743639005868183673025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 204991518674490911564033 153743639005868183673025)
                    ·
                      refine ⟨115307729254401137754769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 153743639005868183673025 115307729254401137754769)
                      ·
                        rfl

theorem cell23_224561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_224561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224561 prefixEnd_224561 := by exact prefixLift 224561
  have htrace : WordTrace (prefixWord ++ tailWord_224561) baseStart_224561 baseEnd_224561 := by
    simpa [prefixWord, tailWord_224561, baseEnd_224561] using wordTrace_append hprefix tailTrace_224561
  have hstable : (prefixWord ++ tailWord_224561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224561).length < 2 ^ (prefixWord ++ tailWord_224561).sum := by decide
  have hdescent : baseEnd_224561 < baseStart_224561 := by decide
  rcases family_descends (prefixWord ++ tailWord_224561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224564 : List Nat := [2, 5, 1, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_224564 : Nat := 118140960795 + 224564 * 2 ^ 59
def prefixEnd_224564 : Nat := 4983230072969 + 3 ^ 40 * 224564 * 2
def baseEnd_224564 : Nat := 115309269696364626017255

theorem tailTrace_224564 : CollatzResearch.WordTrace tailWord_224564 prefixEnd_224564 115309269696364626017255 := by
  unfold tailWord_224564
  simp only [CollatzResearch.WordTrace]
  refine ⟨4095260979225227661456373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5460347972300303548608497 4095260979225227661456373)
  ·
    refine ⟨383930716802365093261535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4095260979225227661456373 383930716802365093261535)
    ·
      refine ⟨575896075203547639892303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383930716802365093261535 575896075203547639892303)
      ·
        refine ⟨863844112805321459838455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575896075203547639892303 863844112805321459838455)
        ·
          refine ⟨1295766169207982189757683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 863844112805321459838455 1295766169207982189757683)
          ·
            refine ⟨1943649253811973284636525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1295766169207982189757683 1943649253811973284636525)
            ·
              refine ⟨728868470179489981738697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1943649253811973284636525 728868470179489981738697)
              ·
                refine ⟨546651352634617486304023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 728868470179489981738697 546651352634617486304023)
                ·
                  refine ⟨819977028951926229456035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 546651352634617486304023 819977028951926229456035)
                  ·
                    refine ⟨1229965543427889344184053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 819977028951926229456035 1229965543427889344184053)
                    ·
                      refine ⟨115309269696364626017255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1229965543427889344184053 115309269696364626017255)
                      ·
                        rfl

theorem cell23_224564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_224564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224564 prefixEnd_224564 := by exact prefixLift 224564
  have htrace : WordTrace (prefixWord ++ tailWord_224564) baseStart_224564 baseEnd_224564 := by
    simpa [prefixWord, tailWord_224564, baseEnd_224564] using wordTrace_append hprefix tailTrace_224564
  have hstable : (prefixWord ++ tailWord_224564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224564).length < 2 ^ (prefixWord ++ tailWord_224564).sum := by decide
  have hdescent : baseEnd_224564 < baseStart_224564 := by decide
  rcases family_descends (prefixWord ++ tailWord_224564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224589 : List Nat := [1, 6, 1, 3, 2, 1, 1, 3, 1, 1, 3]
def baseStart_224589 : Nat := 118140960795 + 224589 * 2 ^ 59
def prefixEnd_224589 : Nat := 4983230072969 + 3 ^ 40 * 224589 * 2
def baseEnd_224589 : Nat := 115322106712727028204641

theorem tailTrace_224589 : CollatzResearch.WordTrace tailWord_224589 prefixEnd_224589 115322106712727028204641 := by
  unfold tailWord_224589
  simp only [CollatzResearch.WordTrace]
  refine ⟨8191433783359884592572821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5460955855573256395048547 8191433783359884592572821)
  ·
    refine ⟨383973458594994590276851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8191433783359884592572821 383973458594994590276851)
    ·
      refine ⟨575960187892491885415277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383973458594994590276851 575960187892491885415277)
      ·
        refine ⟨215985070459684457030729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 575960187892491885415277 215985070459684457030729)
        ·
          refine ⟨161988802844763342773047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215985070459684457030729 161988802844763342773047)
          ·
            refine ⟨242983204267145014159571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161988802844763342773047 242983204267145014159571)
            ·
              refine ⟨364474806400717521239357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242983204267145014159571 364474806400717521239357)
              ·
                refine ⟨136678052400269070464759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 364474806400717521239357 136678052400269070464759)
                ·
                  refine ⟨205017078600403605697139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136678052400269070464759 205017078600403605697139)
                  ·
                    refine ⟨307525617900605408545709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 205017078600403605697139 307525617900605408545709)
                    ·
                      refine ⟨115322106712727028204641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 307525617900605408545709 115322106712727028204641)
                      ·
                        rfl

theorem cell23_224589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_224589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224589 prefixEnd_224589 := by exact prefixLift 224589
  have htrace : WordTrace (prefixWord ++ tailWord_224589) baseStart_224589 baseEnd_224589 := by
    simpa [prefixWord, tailWord_224589, baseEnd_224589] using wordTrace_append hprefix tailTrace_224589
  have hstable : (prefixWord ++ tailWord_224589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224589).length < 2 ^ (prefixWord ++ tailWord_224589).sum := by decide
  have hdescent : baseEnd_224589 < baseStart_224589 := by decide
  rcases family_descends (prefixWord ++ tailWord_224589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224622 : List Nat := [4, 1, 2, 4, 2, 1, 2, 1, 2, 4]
def baseStart_224622 : Nat := 118140960795 + 224622 * 2 ^ 59
def prefixEnd_224622 : Nat := 4983230072969 + 3 ^ 40 * 224622 * 2
def baseEnd_224622 : Nat := 38446350524775133030663

theorem tailTrace_224622 : CollatzResearch.WordTrace tailWord_224622 prefixEnd_224622 38446350524775133030663 := by
  unfold tailWord_224622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1024079674030041403565515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5461758261493554152349413 1024079674030041403565515)
  ·
    refine ⟨1536119511045062105348273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1024079674030041403565515 1536119511045062105348273)
    ·
      refine ⟨1152089633283796579011205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1536119511045062105348273 1152089633283796579011205)
      ·
        refine ⟨216016806240711858564601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1152089633283796579011205 216016806240711858564601)
        ·
          refine ⟨162012604680533893923451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216016806240711858564601 162012604680533893923451)
          ·
            refine ⟨243018907020800840885177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162012604680533893923451 243018907020800840885177)
            ·
              refine ⟨182264180265600630663883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243018907020800840885177 182264180265600630663883)
              ·
                refine ⟨273396270398400945995825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182264180265600630663883 273396270398400945995825)
                ·
                  refine ⟨205047202798800709496869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273396270398400945995825 205047202798800709496869)
                  ·
                    refine ⟨38446350524775133030663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 205047202798800709496869 38446350524775133030663)
                    ·
                      rfl

theorem cell23_224622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_224622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224622 prefixEnd_224622 := by exact prefixLift 224622
  have htrace : WordTrace (prefixWord ++ tailWord_224622) baseStart_224622 baseEnd_224622 := by
    simpa [prefixWord, tailWord_224622, baseEnd_224622] using wordTrace_append hprefix tailTrace_224622
  have hstable : (prefixWord ++ tailWord_224622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224622).length < 2 ^ (prefixWord ++ tailWord_224622).sum := by decide
  have hdescent : baseEnd_224622 < baseStart_224622 := by decide
  rcases family_descends (prefixWord ++ tailWord_224622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224637 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 4, 1, 5]
def baseStart_224637 : Nat := 118140960795 + 224637 * 2 ^ 59
def prefixEnd_224637 : Nat := 4983230072969 + 3 ^ 40 * 224637 * 2
def baseEnd_224637 : Nat := 115346753784142840404419

theorem tailTrace_224637 : CollatzResearch.WordTrace tailWord_224637 prefixEnd_224637 115346753784142840404419 := by
  unfold tailWord_224637
  simp only [CollatzResearch.WordTrace]
  refine ⟨8193184487185988790320165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5462122991457325860213443 8193184487185988790320165)
  ·
    refine ⟨1536222091347372898185031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8193184487185988790320165 1536222091347372898185031)
    ·
      refine ⟨2304333137021059347277547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1536222091347372898185031 2304333137021059347277547)
      ·
        refine ⟨3456499705531589020916321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2304333137021059347277547 3456499705531589020916321)
        ·
          refine ⟨2592374779148691765687241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3456499705531589020916321 2592374779148691765687241)
          ·
            refine ⟨1944281084361518824265431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2592374779148691765687241 1944281084361518824265431)
            ·
              refine ⟨2916421626542278236398147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1944281084361518824265431 2916421626542278236398147)
              ·
                refine ⟨4374632439813417354597221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2916421626542278236398147 4374632439813417354597221)
                ·
                  refine ⟨820243582465015753986979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4374632439813417354597221 820243582465015753986979)
                  ·
                    refine ⟨1230365373697523630980469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 820243582465015753986979 1230365373697523630980469)
                    ·
                      refine ⟨115346753784142840404419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1230365373697523630980469 115346753784142840404419)
                      ·
                        rfl

theorem cell23_224637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_224637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224637 prefixEnd_224637 := by exact prefixLift 224637
  have htrace : WordTrace (prefixWord ++ tailWord_224637) baseStart_224637 baseEnd_224637 := by
    simpa [prefixWord, tailWord_224637, baseEnd_224637] using wordTrace_append hprefix tailTrace_224637
  have hstable : (prefixWord ++ tailWord_224637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224637).length < 2 ^ (prefixWord ++ tailWord_224637).sum := by decide
  have hdescent : baseEnd_224637 < baseStart_224637 := by decide
  rcases family_descends (prefixWord ++ tailWord_224637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224685 : List Nat := [1, 5, 2, 2, 1, 1, 2, 3, 2, 2, 2]
def baseStart_224685 : Nat := 118140960795 + 224685 * 2 ^ 59
def prefixEnd_224685 : Nat := 4983230072969 + 3 ^ 40 * 224685 * 2
def baseEnd_224685 : Nat := 115371400855558652604199

theorem tailTrace_224685 : CollatzResearch.WordTrace tailWord_224685 prefixEnd_224685 115371400855558652604199 := by
  unfold tailWord_224685
  simp only [CollatzResearch.WordTrace]
  refine ⟨8194935191012092988067509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5463290127341395325378339 8194935191012092988067509)
  ·
    refine ⟨768275174157383717631329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8194935191012092988067509 768275174157383717631329)
    ·
      refine ⟨576206380618037788223497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 768275174157383717631329 576206380618037788223497)
      ·
        refine ⟨432154785463528341167623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 576206380618037788223497 432154785463528341167623)
        ·
          refine ⟨648232178195292511751435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432154785463528341167623 648232178195292511751435)
          ·
            refine ⟨972348267292938767627153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648232178195292511751435 972348267292938767627153)
            ·
              refine ⟨729261200469704075720365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 972348267292938767627153 729261200469704075720365)
              ·
                refine ⟨273472950176139028395137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 729261200469704075720365 273472950176139028395137)
                ·
                  refine ⟨205104712632104271296353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273472950176139028395137 205104712632104271296353)
                  ·
                    refine ⟨153828534474078203472265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 205104712632104271296353 153828534474078203472265)
                    ·
                      refine ⟨115371400855558652604199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 153828534474078203472265 115371400855558652604199)
                      ·
                        rfl

theorem cell23_224685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_224685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224685 prefixEnd_224685 := by exact prefixLift 224685
  have htrace : WordTrace (prefixWord ++ tailWord_224685) baseStart_224685 baseEnd_224685 := by
    simpa [prefixWord, tailWord_224685, baseEnd_224685] using wordTrace_append hprefix tailTrace_224685
  have hstable : (prefixWord ++ tailWord_224685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224685).length < 2 ^ (prefixWord ++ tailWord_224685).sum := by decide
  have hdescent : baseEnd_224685 < baseStart_224685 := by decide
  rcases family_descends (prefixWord ++ tailWord_224685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224687 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 4, 5]
def baseStart_224687 : Nat := 118140960795 + 224687 * 2 ^ 59
def prefixEnd_224687 : Nat := 4983230072969 + 3 ^ 40 * 224687 * 2
def baseEnd_224687 : Nat := 38457475938955881593063

theorem tailTrace_224687 : CollatzResearch.WordTrace tailWord_224687 prefixEnd_224687 38457475938955881593063 := by
  unfold tailWord_224687
  simp only [CollatzResearch.WordTrace]
  refine ⟨8195008137004847329640315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5463338758003231553093543 8195008137004847329640315)
  ·
    refine ⟨12292512205507270994460473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8195008137004847329640315 12292512205507270994460473)
    ·
      refine ⟨9219384154130453245845355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12292512205507270994460473 9219384154130453245845355)
      ·
        refine ⟨13829076231195679868768033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9219384154130453245845355 13829076231195679868768033)
        ·
          refine ⟨10371807173396759901576025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13829076231195679868768033 10371807173396759901576025)
          ·
            refine ⟨7778855380047569926182019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10371807173396759901576025 7778855380047569926182019)
            ·
              refine ⟨11668283070071354889273029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7778855380047569926182019 11668283070071354889273029)
              ·
                refine ⟨2187803075638379041738693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11668283070071354889273029 2187803075638379041738693)
                ·
                  refine ⟨410213076682196070326005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2187803075638379041738693 410213076682196070326005)
                  ·
                    refine ⟨38457475938955881593063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 410213076682196070326005 38457475938955881593063)
                    ·
                      rfl

theorem cell23_224687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 5].length) (baseStart_224687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224687 prefixEnd_224687 := by exact prefixLift 224687
  have htrace : WordTrace (prefixWord ++ tailWord_224687) baseStart_224687 baseEnd_224687 := by
    simpa [prefixWord, tailWord_224687, baseEnd_224687] using wordTrace_append hprefix tailTrace_224687
  have hstable : (prefixWord ++ tailWord_224687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224687).length < 2 ^ (prefixWord ++ tailWord_224687).sum := by decide
  have hdescent : baseEnd_224687 < baseStart_224687 := by decide
  rcases family_descends (prefixWord ++ tailWord_224687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224704 : List Nat := [2, 1, 1, 2, 3, 1, 5, 1, 2, 5]
def baseStart_224704 : Nat := 118140960795 + 224704 * 2 ^ 59
def prefixEnd_224704 : Nat := 4983230072969 + 3 ^ 40 * 224704 * 2
def baseEnd_224704 : Nat := 38460385662664692755537

theorem tailTrace_224704 : CollatzResearch.WordTrace tailWord_224704 prefixEnd_224704 38460385662664692755537 := by
  unfold tailWord_224704
  simp only [CollatzResearch.WordTrace]
  refine ⟨4097814088971629616504583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5463752118628839488672777 4097814088971629616504583)
  ·
    refine ⟨6146721133457444424756875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4097814088971629616504583 6146721133457444424756875)
    ·
      refine ⟨9220081700186166637135313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6146721133457444424756875 9220081700186166637135313)
      ·
        refine ⟨6915061275139624977851485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9220081700186166637135313 6915061275139624977851485)
        ·
          refine ⟨2593147978177359366694307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6915061275139624977851485 2593147978177359366694307)
          ·
            refine ⟨3889721967266039050041461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2593147978177359366694307 3889721967266039050041461)
            ·
              refine ⟨364661434431191160941387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3889721967266039050041461 364661434431191160941387)
              ·
                refine ⟨546992151646786741412081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 364661434431191160941387 546992151646786741412081)
                ·
                  refine ⟨410244113735090056059061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 546992151646786741412081 410244113735090056059061)
                  ·
                    refine ⟨38460385662664692755537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 410244113735090056059061 38460385662664692755537)
                    ·
                      rfl

theorem cell23_224704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 2, 5].length) (baseStart_224704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224704 prefixEnd_224704 := by exact prefixLift 224704
  have htrace : WordTrace (prefixWord ++ tailWord_224704) baseStart_224704 baseEnd_224704 := by
    simpa [prefixWord, tailWord_224704, baseEnd_224704] using wordTrace_append hprefix tailTrace_224704
  have hstable : (prefixWord ++ tailWord_224704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224704).length < 2 ^ (prefixWord ++ tailWord_224704).sum := by decide
  have hdescent : baseEnd_224704 < baseStart_224704 := by decide
  rcases family_descends (prefixWord ++ tailWord_224704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224708 : List Nat := [2, 3, 3, 2, 1, 2, 2, 3, 5]
def baseStart_224708 : Nat := 118140960795 + 224708 * 2 ^ 59
def prefixEnd_224708 : Nat := 4983230072969 + 3 ^ 40 * 224708 * 2
def baseEnd_224708 : Nat := 12820356767845784735177

theorem tailTrace_224708 : CollatzResearch.WordTrace tailWord_224708 prefixEnd_224708 12820356767845784735177 := by
  unfold tailWord_224708
  simp only [CollatzResearch.WordTrace]
  refine ⟨4097887034964383958077389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5463849379952511944103185 4097887034964383958077389)
  ·
    refine ⟨1536707638111643984279021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4097887034964383958077389 1536707638111643984279021)
    ·
      refine ⟨576265364291866494104633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1536707638111643984279021 576265364291866494104633)
      ·
        refine ⟨432199023218899870578475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 576265364291866494104633 432199023218899870578475)
        ·
          refine ⟨648298534828349805867713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432199023218899870578475 648298534828349805867713)
          ·
            refine ⟨486223901121262354400785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 648298534828349805867713 486223901121262354400785)
            ·
              refine ⟨364667925840946765800589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 486223901121262354400785 364667925840946765800589)
              ·
                refine ⟨136750472190355037175221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 364667925840946765800589 136750472190355037175221)
                ·
                  refine ⟨12820356767845784735177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136750472190355037175221 12820356767845784735177)
                  ·
                    rfl

theorem cell23_224708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3, 5].length) (baseStart_224708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224708 prefixEnd_224708 := by exact prefixLift 224708
  have htrace : WordTrace (prefixWord ++ tailWord_224708) baseStart_224708 baseEnd_224708 := by
    simpa [prefixWord, tailWord_224708, baseEnd_224708] using wordTrace_append hprefix tailTrace_224708
  have hstable : (prefixWord ++ tailWord_224708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224708).length < 2 ^ (prefixWord ++ tailWord_224708).sum := by decide
  have hdescent : baseEnd_224708 < baseStart_224708 := by decide
  rcases family_descends (prefixWord ++ tailWord_224708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224727 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 5]
def baseStart_224727 : Nat := 118140960795 + 224727 * 2 ^ 59
def prefixEnd_224727 : Nat := 4983230072969 + 3 ^ 40 * 224727 * 2
def baseEnd_224727 : Nat := 115392967043047488279005

theorem tailTrace_224727 : CollatzResearch.WordTrace tailWord_224727 prefixEnd_224727 115392967043047488279005 := by
  unfold tailWord_224727
  simp only [CollatzResearch.WordTrace]
  refine ⟨8196467056859934161096435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5464311371239956107397623 8196467056859934161096435)
  ·
    refine ⟨12294700585289901241644653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8196467056859934161096435 12294700585289901241644653)
    ·
      refine ⟨4610512719483712965616745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12294700585289901241644653 4610512719483712965616745)
      ·
        refine ⟨3457884539612784724212559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4610512719483712965616745 3457884539612784724212559)
        ·
          refine ⟨5186826809419177086318839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3457884539612784724212559 5186826809419177086318839)
          ·
            refine ⟨7780240214128765629478259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5186826809419177086318839 7780240214128765629478259)
            ·
              refine ⟨11670360321193148444217389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7780240214128765629478259 11670360321193148444217389)
              ·
                refine ⟨4376385120447430666581521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11670360321193148444217389 4376385120447430666581521)
                ·
                  refine ⟨3282288840335572999936141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4376385120447430666581521 3282288840335572999936141)
                  ·
                    refine ⟨1230858315125839874976053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3282288840335572999936141 1230858315125839874976053)
                    ·
                      refine ⟨115392967043047488279005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1230858315125839874976053 115392967043047488279005)
                      ·
                        rfl

theorem cell23_224727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_224727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224727 prefixEnd_224727 := by exact prefixLift 224727
  have htrace : WordTrace (prefixWord ++ tailWord_224727) baseStart_224727 baseEnd_224727 := by
    simpa [prefixWord, tailWord_224727, baseEnd_224727] using wordTrace_append hprefix tailTrace_224727
  have hstable : (prefixWord ++ tailWord_224727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224727).length < 2 ^ (prefixWord ++ tailWord_224727).sum := by decide
  have hdescent : baseEnd_224727 < baseStart_224727 := by decide
  rcases family_descends (prefixWord ++ tailWord_224727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224744 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 3, 4, 3]
def baseStart_224744 : Nat := 118140960795 + 224744 * 2 ^ 59
def prefixEnd_224744 : Nat := 4983230072969 + 3 ^ 40 * 224744 * 2
def baseEnd_224744 : Nat := 115401696214173921766427

theorem tailTrace_224744 : CollatzResearch.WordTrace tailWord_224744 prefixEnd_224744 115401696214173921766427 := by
  unfold tailWord_224744
  simp only [CollatzResearch.WordTrace]
  refine ⟨4098543548899173032232643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5464724731865564042976857 4098543548899173032232643)
  ·
    refine ⟨6147815323348759548348965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4098543548899173032232643 6147815323348759548348965)
    ·
      refine ⟨1152715373127892415315431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6147815323348759548348965 1152715373127892415315431)
      ·
        refine ⟨1729073059691838622973147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1152715373127892415315431 1729073059691838622973147)
        ·
          refine ⟨2593609589537757934459721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1729073059691838622973147 2593609589537757934459721)
          ·
            refine ⟨1945207192153318450844791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2593609589537757934459721 1945207192153318450844791)
            ·
              refine ⟨2917810788229977676267187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1945207192153318450844791 2917810788229977676267187)
              ·
                refine ⟨4376716182344966514400781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2917810788229977676267187 4376716182344966514400781)
                ·
                  refine ⟨1641268568379362442900293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4376716182344966514400781 1641268568379362442900293)
                  ·
                    refine ⟨307737856571130458043805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1641268568379362442900293 307737856571130458043805)
                    ·
                      refine ⟨115401696214173921766427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 307737856571130458043805 115401696214173921766427)
                      ·
                        rfl

theorem cell23_224744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_224744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224744 prefixEnd_224744 := by exact prefixLift 224744
  have htrace : WordTrace (prefixWord ++ tailWord_224744) baseStart_224744 baseEnd_224744 := by
    simpa [prefixWord, tailWord_224744, baseEnd_224744] using wordTrace_append hprefix tailTrace_224744
  have hstable : (prefixWord ++ tailWord_224744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224744).length < 2 ^ (prefixWord ++ tailWord_224744).sum := by decide
  have hdescent : baseEnd_224744 < baseStart_224744 := by decide
  rcases family_descends (prefixWord ++ tailWord_224744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224767 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 8]
def baseStart_224767 : Nat := 118140960795 + 224767 * 2 ^ 59
def prefixEnd_224767 : Nat := 4983230072969 + 3 ^ 40 * 224767 * 2
def baseEnd_224767 : Nat := 115413506269227331778821

theorem tailTrace_224767 : CollatzResearch.WordTrace tailWord_224767 prefixEnd_224767 115413506269227331778821 := by
  unfold tailWord_224767
  simp only [CollatzResearch.WordTrace]
  refine ⟨8197925976715020992552555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5465283984476680661701703 8197925976715020992552555)
  ·
    refine ⟨12296888965072531488828833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8197925976715020992552555 12296888965072531488828833)
    ·
      refine ⟨9222666723804398616621625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12296888965072531488828833 9222666723804398616621625)
      ·
        refine ⟨6917000042853298962466219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9222666723804398616621625 6917000042853298962466219)
        ·
          refine ⟨10375500064279948443699329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6917000042853298962466219 10375500064279948443699329)
          ·
            refine ⟨7781625048209961332774497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10375500064279948443699329 7781625048209961332774497)
            ·
              refine ⟨5836218786157470999580873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7781625048209961332774497 5836218786157470999580873)
              ·
                refine ⟨4377164089618103249685655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5836218786157470999580873 4377164089618103249685655)
                ·
                  refine ⟨6565746134427154874528483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4377164089618103249685655 6565746134427154874528483)
                  ·
                    refine ⟨9848619201640732311792725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6565746134427154874528483 9848619201640732311792725)
                    ·
                      refine ⟨115413506269227331778821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 9848619201640732311792725 115413506269227331778821)
                      ·
                        rfl

theorem cell23_224767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_224767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224767 prefixEnd_224767 := by exact prefixLift 224767
  have htrace : WordTrace (prefixWord ++ tailWord_224767) baseStart_224767 baseEnd_224767 := by
    simpa [prefixWord, tailWord_224767, baseEnd_224767] using wordTrace_append hprefix tailTrace_224767
  have hstable : (prefixWord ++ tailWord_224767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224767).length < 2 ^ (prefixWord ++ tailWord_224767).sum := by decide
  have hdescent : baseEnd_224767 < baseStart_224767 := by decide
  rcases family_descends (prefixWord ++ tailWord_224767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224794 : List Nat := [3, 1, 1, 3, 1, 1, 1, 4, 3, 5]
def baseStart_224794 : Nat := 118140960795 + 224794 * 2 ^ 59
def prefixEnd_224794 : Nat := 4983230072969 + 3 ^ 40 * 224794 * 2
def baseEnd_224794 : Nat := 38475790082299575380399

theorem tailTrace_224794 : CollatzResearch.WordTrace tailWord_224794 prefixEnd_224794 38475790082299575380399 := by
  unfold tailWord_224794
  simp only [CollatzResearch.WordTrace]
  refine ⟨2049727686904301150946359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5465940498411469735856957 2049727686904301150946359)
  ·
    refine ⟨3074591530356451726419539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2049727686904301150946359 3074591530356451726419539)
    ·
      refine ⟨4611887295534677589629309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3074591530356451726419539 4611887295534677589629309)
      ·
        refine ⟨1729457735825504096110991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4611887295534677589629309 1729457735825504096110991)
        ·
          refine ⟨2594186603738256144166487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1729457735825504096110991 2594186603738256144166487)
          ·
            refine ⟨3891279905607384216249731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2594186603738256144166487 3891279905607384216249731)
            ·
              refine ⟨5836919858411076324374597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3891279905607384216249731 5836919858411076324374597)
              ·
                refine ⟨1094422473452076810820237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5836919858411076324374597 1094422473452076810820237)
                ·
                  refine ⟨410408427544528804057589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1094422473452076810820237 410408427544528804057589)
                  ·
                    refine ⟨38475790082299575380399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 410408427544528804057589 38475790082299575380399)
                    ·
                      rfl

theorem cell23_224794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 3, 5].length) (baseStart_224794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224794 prefixEnd_224794 := by exact prefixLift 224794
  have htrace : WordTrace (prefixWord ++ tailWord_224794) baseStart_224794 baseEnd_224794 := by
    simpa [prefixWord, tailWord_224794, baseEnd_224794] using wordTrace_append hprefix tailTrace_224794
  have hstable : (prefixWord ++ tailWord_224794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224794).length < 2 ^ (prefixWord ++ tailWord_224794).sum := by decide
  have hdescent : baseEnd_224794 < baseStart_224794 := by decide
  rcases family_descends (prefixWord ++ tailWord_224794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224824 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 3, 6]
def baseStart_224824 : Nat := 118140960795 + 224824 * 2 ^ 59
def prefixEnd_224824 : Nat := 4983230072969 + 3 ^ 40 * 224824 * 2
def baseEnd_224824 : Nat := 38480924888844536255353

theorem tailTrace_224824 : CollatzResearch.WordTrace tailWord_224824 prefixEnd_224824 38480924888844536255353 := by
  unfold tailWord_224824
  simp only [CollatzResearch.WordTrace]
  refine ⟨4100002468754259863688763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5466669958339013151585017 4100002468754259863688763)
  ·
    refine ⟨6150003703131389795533145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4100002468754259863688763 6150003703131389795533145)
    ·
      refine ⟨4612502777348542346649859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6150003703131389795533145 4612502777348542346649859)
      ·
        refine ⟨6918754166022813519974789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4612502777348542346649859 6918754166022813519974789)
        ·
          refine ⟨1297266406129277534995273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6918754166022813519974789 1297266406129277534995273)
          ·
            refine ⟨972949804596958151246455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1297266406129277534995273 972949804596958151246455)
            ·
              refine ⟨1459424706895437226869683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 972949804596958151246455 1459424706895437226869683)
              ·
                refine ⟨2189137060343155840304525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1459424706895437226869683 2189137060343155840304525)
                ·
                  refine ⟨820926397628683440114197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2189137060343155840304525 820926397628683440114197)
                  ·
                    refine ⟨38480924888844536255353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 820926397628683440114197 38480924888844536255353)
                    ·
                      rfl

theorem cell23_224824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 3, 6].length) (baseStart_224824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224824 prefixEnd_224824 := by exact prefixLift 224824
  have htrace : WordTrace (prefixWord ++ tailWord_224824) baseStart_224824 baseEnd_224824 := by
    simpa [prefixWord, tailWord_224824, baseEnd_224824] using wordTrace_append hprefix tailTrace_224824
  have hstable : (prefixWord ++ tailWord_224824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224824).length < 2 ^ (prefixWord ++ tailWord_224824).sum := by decide
  have hdescent : baseEnd_224824 < baseStart_224824 := by decide
  rcases family_descends (prefixWord ++ tailWord_224824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224848 : List Nat := [2, 1, 1, 1, 1, 3, 4, 3, 3, 2, 2]
def baseStart_224848 : Nat := 118140960795 + 224848 * 2 ^ 59
def prefixEnd_224848 : Nat := 4983230072969 + 3 ^ 40 * 224848 * 2
def baseEnd_224848 : Nat := 115455098202241514865949

theorem tailTrace_224848 : CollatzResearch.WordTrace tailWord_224848 prefixEnd_224848 115455098202241514865949 := by
  unfold tailWord_224848
  simp only [CollatzResearch.WordTrace]
  refine ⟨4100440144710785913125599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5467253526281047884167465 4100440144710785913125599)
  ·
    refine ⟨6150660217066178869688399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4100440144710785913125599 6150660217066178869688399)
    ·
      refine ⟨9225990325599268304532599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6150660217066178869688399 9225990325599268304532599)
      ·
        refine ⟨13838985488398902456798899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9225990325599268304532599 13838985488398902456798899)
        ·
          refine ⟨20758478232598353685198349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13838985488398902456798899 20758478232598353685198349)
          ·
            refine ⟨7784429337224382631949381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20758478232598353685198349 7784429337224382631949381)
            ·
              refine ⟨1459580500729571743490509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7784429337224382631949381 1459580500729571743490509)
              ·
                refine ⟨547342687773589403808941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1459580500729571743490509 547342687773589403808941)
                ·
                  refine ⟨205253507915096026428353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 547342687773589403808941 205253507915096026428353)
                  ·
                    refine ⟨153940130936322019821265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 205253507915096026428353 153940130936322019821265)
                    ·
                      refine ⟨115455098202241514865949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 153940130936322019821265 115455098202241514865949)
                      ·
                        rfl

theorem cell23_224848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 3, 2, 2].length) (baseStart_224848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224848 prefixEnd_224848 := by exact prefixLift 224848
  have htrace : WordTrace (prefixWord ++ tailWord_224848) baseStart_224848 baseEnd_224848 := by
    simpa [prefixWord, tailWord_224848, baseEnd_224848] using wordTrace_append hprefix tailTrace_224848
  have hstable : (prefixWord ++ tailWord_224848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224848).length < 2 ^ (prefixWord ++ tailWord_224848).sum := by decide
  have hdescent : baseEnd_224848 < baseStart_224848 := by decide
  rcases family_descends (prefixWord ++ tailWord_224848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224882 : List Nat := [3, 2, 1, 2, 3, 1, 1, 5, 1, 2, 2]
def baseStart_224882 : Nat := 118140960795 + 224882 * 2 ^ 59
def prefixEnd_224882 : Nat := 4983230072969 + 3 ^ 40 * 224882 * 2
def baseEnd_224882 : Nat := 115472556544494381840793

theorem tailTrace_224882 : CollatzResearch.WordTrace tailWord_224882 prefixEnd_224882 115472556544494381840793 := by
  unfold tailWord_224882
  simp only [CollatzResearch.WordTrace]
  refine ⟨2050530092824598908247225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5468080247532263755325933 2050530092824598908247225)
  ·
    refine ⟨1537897569618449181185419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2050530092824598908247225 1537897569618449181185419)
    ·
      refine ⟨2306846354427673771778129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1537897569618449181185419 2306846354427673771778129)
      ·
        refine ⟨1730134765820755328833597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2306846354427673771778129 1730134765820755328833597)
        ·
          refine ⟨648800537182783248312599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1730134765820755328833597 648800537182783248312599)
          ·
            refine ⟨973200805774174872468899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648800537182783248312599 973200805774174872468899)
            ·
              refine ⟨1459801208661262308703349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 973200805774174872468899 1459801208661262308703349)
              ·
                refine ⟨136856363311993341440939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1459801208661262308703349 136856363311993341440939)
                ·
                  refine ⟨205284544967990012161409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136856363311993341440939 205284544967990012161409)
                  ·
                    refine ⟨153963408725992509121057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 205284544967990012161409 153963408725992509121057)
                    ·
                      refine ⟨115472556544494381840793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 153963408725992509121057 115472556544494381840793)
                      ·
                        rfl

theorem cell23_224882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_224882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224882 prefixEnd_224882 := by exact prefixLift 224882
  have htrace : WordTrace (prefixWord ++ tailWord_224882) baseStart_224882 baseEnd_224882 := by
    simpa [prefixWord, tailWord_224882, baseEnd_224882] using wordTrace_append hprefix tailTrace_224882
  have hstable : (prefixWord ++ tailWord_224882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224882).length < 2 ^ (prefixWord ++ tailWord_224882).sum := by decide
  have hdescent : baseEnd_224882 < baseStart_224882 := by decide
  rcases family_descends (prefixWord ++ tailWord_224882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224885 : List Nat := [1, 3, 4, 2, 1, 2, 1, 3, 1, 2, 3]
def baseStart_224885 : Nat := 118140960795 + 224885 * 2 ^ 59
def prefixEnd_224885 : Nat := 4983230072969 + 3 ^ 40 * 224885 * 2
def baseEnd_224885 : Nat := 115474096986457870103279

theorem tailTrace_224885 : CollatzResearch.WordTrace tailWord_224885 prefixEnd_224885 115474096986457870103279 := by
  unfold tailWord_224885
  simp only [CollatzResearch.WordTrace]
  refine ⟨8202229790287527145348109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5468153193525018096898739 8202229790287527145348109)
  ·
    refine ⟨3075836171357822679505541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8202229790287527145348109 3075836171357822679505541)
    ·
      refine ⟨576719282129591752407289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3075836171357822679505541 576719282129591752407289)
      ·
        refine ⟨432539461597193814305467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 576719282129591752407289 432539461597193814305467)
        ·
          refine ⟨648809192395790721458201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432539461597193814305467 648809192395790721458201)
          ·
            refine ⟨486606894296843041093651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 648809192395790721458201 486606894296843041093651)
            ·
              refine ⟨729910341445264561640477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486606894296843041093651 729910341445264561640477)
              ·
                refine ⟨273716378041974210615179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 729910341445264561640477 273716378041974210615179)
                ·
                  refine ⟨410574567062961315922769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 273716378041974210615179 410574567062961315922769)
                  ·
                    refine ⟨307930925297220986942077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 410574567062961315922769 307930925297220986942077)
                    ·
                      refine ⟨115474096986457870103279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 307930925297220986942077 115474096986457870103279)
                      ·
                        rfl

theorem cell23_224885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_224885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224885 prefixEnd_224885 := by exact prefixLift 224885
  have htrace : WordTrace (prefixWord ++ tailWord_224885) baseStart_224885 baseEnd_224885 := by
    simpa [prefixWord, tailWord_224885, baseEnd_224885] using wordTrace_append hprefix tailTrace_224885
  have hstable : (prefixWord ++ tailWord_224885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224885).length < 2 ^ (prefixWord ++ tailWord_224885).sum := by decide
  have hdescent : baseEnd_224885 < baseStart_224885 := by decide
  rcases family_descends (prefixWord ++ tailWord_224885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224944 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 9]
def baseStart_224944 : Nat := 118140960795 + 224944 * 2 ^ 59
def prefixEnd_224944 : Nat := 4983230072969 + 3 ^ 40 * 224944 * 2
def baseEnd_224944 : Nat := 12833821371674793251723

theorem tailTrace_224944 : CollatzResearch.WordTrace tailWord_224944 prefixEnd_224944 12833821371674793251723 := by
  unfold tailWord_224944
  simp only [CollatzResearch.WordTrace]
  refine ⟨4102190848536890110872943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5469587798049186814497257 4102190848536890110872943)
  ·
    refine ⟨6153286272805335166309415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4102190848536890110872943 6153286272805335166309415)
    ·
      refine ⟨9229929409208002749464123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6153286272805335166309415 9229929409208002749464123)
      ·
        refine ⟨13844894113812004124196185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9229929409208002749464123 13844894113812004124196185)
        ·
          refine ⟨10383670585359003093147139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13844894113812004124196185 10383670585359003093147139)
          ·
            refine ⟨15575505878038504639720709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10383670585359003093147139 15575505878038504639720709)
            ·
              refine ⟨2920407352132219619947633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15575505878038504639720709 2920407352132219619947633)
              ·
                refine ⟨2190305514099164714960725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2920407352132219619947633 2190305514099164714960725)
                ·
                  refine ⟨12833821371674793251723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2190305514099164714960725 12833821371674793251723)
                  ·
                    rfl

theorem cell23_224944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 9].length) (baseStart_224944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224944 prefixEnd_224944 := by exact prefixLift 224944
  have htrace : WordTrace (prefixWord ++ tailWord_224944) baseStart_224944 baseEnd_224944 := by
    simpa [prefixWord, tailWord_224944, baseEnd_224944] using wordTrace_append hprefix tailTrace_224944
  have hstable : (prefixWord ++ tailWord_224944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224944).length < 2 ^ (prefixWord ++ tailWord_224944).sum := by decide
  have hdescent : baseEnd_224944 < baseStart_224944 := by decide
  rcases family_descends (prefixWord ++ tailWord_224944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224966 : List Nat := [6, 1, 2, 1, 1, 1, 4, 1, 2, 1, 3]
def baseStart_224966 : Nat := 118140960795 + 224966 * 2 ^ 59
def prefixEnd_224966 : Nat := 4983230072969 + 3 ^ 40 * 224966 * 2
def baseEnd_224966 : Nat := 115515688919472053190407

theorem tailTrace_224966 : CollatzResearch.WordTrace tailWord_224966 prefixEnd_224966 115515688919472053190407 := by
  unfold tailWord_224966
  simp only [CollatzResearch.WordTrace]
  refine ⟨256412003218564936845211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5470122735329385319364501 256412003218564936845211)
  ·
    refine ⟨384618004827847405267817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256412003218564936845211 384618004827847405267817)
    ·
      refine ⟨288463503620885553950863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384618004827847405267817 288463503620885553950863)
      ·
        refine ⟨432695255431328330926295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288463503620885553950863 432695255431328330926295)
        ·
          refine ⟨649042883146992496389443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432695255431328330926295 649042883146992496389443)
          ·
            refine ⟨973564324720488744584165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649042883146992496389443 973564324720488744584165)
            ·
              refine ⟨182543310885091639609531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 973564324720488744584165 182543310885091639609531)
              ·
                refine ⟨273814966327637459414297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182543310885091639609531 273814966327637459414297)
                ·
                  refine ⟨205361224745728094560723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273814966327637459414297 205361224745728094560723)
                  ·
                    refine ⟨308041837118592141841085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 205361224745728094560723 308041837118592141841085)
                    ·
                      refine ⟨115515688919472053190407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 308041837118592141841085 115515688919472053190407)
                      ·
                        rfl

theorem cell23_224966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_224966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224966 prefixEnd_224966 := by exact prefixLift 224966
  have htrace : WordTrace (prefixWord ++ tailWord_224966) baseStart_224966 baseEnd_224966 := by
    simpa [prefixWord, tailWord_224966, baseEnd_224966] using wordTrace_append hprefix tailTrace_224966
  have hstable : (prefixWord ++ tailWord_224966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224966).length < 2 ^ (prefixWord ++ tailWord_224966).sum := by decide
  have hdescent : baseEnd_224966 < baseStart_224966 := by decide
  rcases family_descends (prefixWord ++ tailWord_224966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224971 : List Nat := [1, 1, 1, 1, 3, 2, 1, 5, 2, 3, 3]
def baseStart_224971 : Nat := 118140960795 + 224971 * 2 ^ 59
def prefixEnd_224971 : Nat := 4983230072969 + 3 ^ 40 * 224971 * 2
def baseEnd_224971 : Nat := 115518256322744533627883

theorem tailTrace_224971 : CollatzResearch.WordTrace tailWord_224971 prefixEnd_224971 115518256322744533627883 := by
  unfold tailWord_224971
  simp only [CollatzResearch.WordTrace]
  refine ⟨8205366467975963832978767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5470244311983975888652511 8205366467975963832978767)
  ·
    refine ⟨12308049701963945749468151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8205366467975963832978767 12308049701963945749468151)
    ·
      refine ⟨18462074552945918624202227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12308049701963945749468151 18462074552945918624202227)
      ·
        refine ⟨27693111829418877936303341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18462074552945918624202227 27693111829418877936303341)
        ·
          refine ⟨10384916936032079226113753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27693111829418877936303341 10384916936032079226113753)
          ·
            refine ⟨7788687702024059419585315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10384916936032079226113753 7788687702024059419585315)
            ·
              refine ⟨11683031553036089129377973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7788687702024059419585315 11683031553036089129377973)
              ·
                refine ⟨1095284208097133355879185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11683031553036089129377973 1095284208097133355879185)
                ·
                  refine ⟨821463156072850016909389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1095284208097133355879185 821463156072850016909389)
                  ·
                    refine ⟨308048683527318756341021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 821463156072850016909389 308048683527318756341021)
                    ·
                      refine ⟨115518256322744533627883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 308048683527318756341021 115518256322744533627883)
                      ·
                        rfl

theorem cell23_224971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3, 3].length) (baseStart_224971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_224971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_224971 prefixEnd_224971 := by exact prefixLift 224971
  have htrace : WordTrace (prefixWord ++ tailWord_224971) baseStart_224971 baseEnd_224971 := by
    simpa [prefixWord, tailWord_224971, baseEnd_224971] using wordTrace_append hprefix tailTrace_224971
  have hstable : (prefixWord ++ tailWord_224971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224971).length < 2 ^ (prefixWord ++ tailWord_224971).sum := by decide
  have hdescent : baseEnd_224971 < baseStart_224971 := by decide
  rcases family_descends (prefixWord ++ tailWord_224971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225038 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 5, 4]
def baseStart_225038 : Nat := 118140960795 + 225038 * 2 ^ 59
def prefixEnd_225038 : Nat := 4983230072969 + 3 ^ 40 * 225038 * 2
def baseEnd_225038 : Nat := 38517553175531923830025

theorem tailTrace_225038 : CollatzResearch.WordTrace tailWord_225038 prefixEnd_225038 38517553175531923830025 := by
  unfold tailWord_225038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1025976269841654284458471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5471873439155489517111845 1025976269841654284458471)
  ·
    refine ⟨1538964404762481426687707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1025976269841654284458471 1538964404762481426687707)
    ·
      refine ⟨2308446607143722140031561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1538964404762481426687707 2308446607143722140031561)
      ·
        refine ⟨1731334955357791605023671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2308446607143722140031561 1731334955357791605023671)
        ·
          refine ⟨2597002433036687407535507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1731334955357791605023671 2597002433036687407535507)
          ·
            refine ⟨3895503649555031111303261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2597002433036687407535507 3895503649555031111303261)
            ·
              refine ⟨1460813868583136666738723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3895503649555031111303261 1460813868583136666738723)
              ·
                refine ⟨2191220802874705000108085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1460813868583136666738723 2191220802874705000108085)
                ·
                  refine ⟨205426950269503593760133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2191220802874705000108085 205426950269503593760133)
                  ·
                    refine ⟨38517553175531923830025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 205426950269503593760133 38517553175531923830025)
                    ·
                      rfl

theorem cell23_225038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_225038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225038 prefixEnd_225038 := by exact prefixLift 225038
  have htrace : WordTrace (prefixWord ++ tailWord_225038) baseStart_225038 baseEnd_225038 := by
    simpa [prefixWord, tailWord_225038, baseEnd_225038] using wordTrace_append hprefix tailTrace_225038
  have hstable : (prefixWord ++ tailWord_225038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225038).length < 2 ^ (prefixWord ++ tailWord_225038).sum := by decide
  have hdescent : baseEnd_225038 < baseStart_225038 := by decide
  rcases family_descends (prefixWord ++ tailWord_225038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225042 : List Nat := [3, 2, 4, 1, 1, 3, 1, 1, 2, 5]
def baseStart_225042 : Nat := 118140960795 + 225042 * 2 ^ 59
def prefixEnd_225042 : Nat := 4983230072969 + 3 ^ 40 * 225042 * 2
def baseEnd_225042 : Nat := 38518237816404585280019

theorem tailTrace_225042 : CollatzResearch.WordTrace tailWord_225042 prefixEnd_225042 38518237816404585280019 := by
  unfold tailWord_225042
  simp only [CollatzResearch.WordTrace]
  refine ⟨2051989012679685739703345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5471970700479161972542253 2051989012679685739703345)
  ·
    refine ⟨1538991759509764304777509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2051989012679685739703345 1538991759509764304777509)
    ·
      refine ⟨288560954908080807145783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1538991759509764304777509 288560954908080807145783)
      ·
        refine ⟨432841432362121210718675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288560954908080807145783 432841432362121210718675)
        ·
          refine ⟨649262148543181816078013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432841432362121210718675 649262148543181816078013)
          ·
            refine ⟨243473305703693181029255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 649262148543181816078013 243473305703693181029255)
            ·
              refine ⟨365209958555539771543883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243473305703693181029255 365209958555539771543883)
              ·
                refine ⟨547814937833309657315825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365209958555539771543883 547814937833309657315825)
                ·
                  refine ⟨410861203374982242986869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 547814937833309657315825 410861203374982242986869)
                  ·
                    refine ⟨38518237816404585280019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 410861203374982242986869 38518237816404585280019)
                    ·
                      rfl

theorem cell23_225042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_225042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225042 prefixEnd_225042 := by exact prefixLift 225042
  have htrace : WordTrace (prefixWord ++ tailWord_225042) baseStart_225042 baseEnd_225042 := by
    simpa [prefixWord, tailWord_225042, baseEnd_225042] using wordTrace_append hprefix tailTrace_225042
  have hstable : (prefixWord ++ tailWord_225042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225042).length < 2 ^ (prefixWord ++ tailWord_225042).sum := by decide
  have hdescent : baseEnd_225042 < baseStart_225042 := by decide
  rcases family_descends (prefixWord ++ tailWord_225042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225045 : List Nat := [1, 3, 2, 1, 2, 5, 1, 1, 2, 1, 4]
def baseStart_225045 : Nat := 118140960795 + 225045 * 2 ^ 59
def prefixEnd_225045 : Nat := 4983230072969 + 3 ^ 40 * 225045 * 2
def baseEnd_225045 : Nat := 115556253891177244102543

theorem tailTrace_225045 : CollatzResearch.WordTrace tailWord_225045 prefixEnd_225045 115556253891177244102543 := by
  unfold tailWord_225045
  simp only [CollatzResearch.WordTrace]
  refine ⟨8208065469707874471172589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5472043646471916314115059 8208065469707874471172589)
  ·
    refine ⟨3078024551140452926689721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8208065469707874471172589 3078024551140452926689721)
    ·
      refine ⟨2308518413355339695017291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3078024551140452926689721 2308518413355339695017291)
      ·
        refine ⟨3462777620033009542525937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2308518413355339695017291 3462777620033009542525937)
        ·
          refine ⟨2597083215024757156894453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3462777620033009542525937 2597083215024757156894453)
          ·
            refine ⟨243476551408570983458855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2597083215024757156894453 243476551408570983458855)
            ·
              refine ⟨365214827112856475188283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243476551408570983458855 365214827112856475188283)
              ·
                refine ⟨547822240669284712782425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365214827112856475188283 547822240669284712782425)
                ·
                  refine ⟨410866680501963534586819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 547822240669284712782425 410866680501963534586819)
                  ·
                    refine ⟨616300020752945301880229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 410866680501963534586819 616300020752945301880229)
                    ·
                      refine ⟨115556253891177244102543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 616300020752945301880229 115556253891177244102543)
                      ·
                        rfl

theorem cell23_225045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_225045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225045 prefixEnd_225045 := by exact prefixLift 225045
  have htrace : WordTrace (prefixWord ++ tailWord_225045) baseStart_225045 baseEnd_225045 := by
    simpa [prefixWord, tailWord_225045, baseEnd_225045] using wordTrace_append hprefix tailTrace_225045
  have hstable : (prefixWord ++ tailWord_225045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225045).length < 2 ^ (prefixWord ++ tailWord_225045).sum := by decide
  have hdescent : baseEnd_225045 < baseStart_225045 := by decide
  rcases family_descends (prefixWord ++ tailWord_225045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225068 : List Nat := [2, 2, 1, 1, 1, 5, 3, 2, 6]
def baseStart_225068 : Nat := 118140960795 + 225068 * 2 ^ 59
def prefixEnd_225068 : Nat := 4983230072969 + 3 ^ 40 * 225068 * 2
def baseEnd_225068 : Nat := 12840895994025628234993

theorem tailTrace_225068 : CollatzResearch.WordTrace tailWord_225068 prefixEnd_225068 12840895994025628234993 := by
  unfold tailWord_225068
  simp only [CollatzResearch.WordTrace]
  refine ⟨4104452174312274699629929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5472602899083032932839905 4104452174312274699629929)
  ·
    refine ⟨3078339130734206024722447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4104452174312274699629929 3078339130734206024722447)
    ·
      refine ⟨4617508696101309037083671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3078339130734206024722447 4617508696101309037083671)
      ·
        refine ⟨6926263044151963555625507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4617508696101309037083671 6926263044151963555625507)
        ·
          refine ⟨10389394566227945333438261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6926263044151963555625507 10389394566227945333438261)
          ·
            refine ⟨974005740583869875009837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10389394566227945333438261 974005740583869875009837)
            ·
              refine ⟨365252152718951203128689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 974005740583869875009837 365252152718951203128689)
              ·
                refine ⟨273939114539213402346517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 365252152718951203128689 273939114539213402346517)
                ·
                  refine ⟨12840895994025628234993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 273939114539213402346517 12840895994025628234993)
                  ·
                    rfl

theorem cell23_225068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 6].length) (baseStart_225068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225068 prefixEnd_225068 := by exact prefixLift 225068
  have htrace : WordTrace (prefixWord ++ tailWord_225068) baseStart_225068 baseEnd_225068 := by
    simpa [prefixWord, tailWord_225068, baseEnd_225068] using wordTrace_append hprefix tailTrace_225068
  have hstable : (prefixWord ++ tailWord_225068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225068).length < 2 ^ (prefixWord ++ tailWord_225068).sum := by decide
  have hdescent : baseEnd_225068 < baseStart_225068 := by decide
  rcases family_descends (prefixWord ++ tailWord_225068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225095 : List Nat := [1, 1, 4, 1, 2, 1, 4, 2, 3, 1, 3]
def baseStart_225095 : Nat := 118140960795 + 225095 * 2 ^ 59
def prefixEnd_225095 : Nat := 4983230072969 + 3 ^ 40 * 225095 * 2
def baseEnd_225095 : Nat := 115581927923902048477313

theorem tailTrace_225095 : CollatzResearch.WordTrace tailWord_225095 prefixEnd_225095 115581927923902048477313 := by
  unfold tailWord_225095
  simp only [CollatzResearch.WordTrace]
  refine ⟨8209889119526733010492739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5473259413017822006995159 8209889119526733010492739)
  ·
    refine ⟨12314833679290099515739109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8209889119526733010492739 12314833679290099515739109)
    ·
      refine ⟨2309031314866893659201083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12314833679290099515739109 2309031314866893659201083)
      ·
        refine ⟨3463546972300340488801625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2309031314866893659201083 3463546972300340488801625)
        ·
          refine ⟨2597660229225255366601219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3463546972300340488801625 2597660229225255366601219)
          ·
            refine ⟨3896490343837883049901829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2597660229225255366601219 3896490343837883049901829)
            ·
              refine ⟨730591939469603071856593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3896490343837883049901829 730591939469603071856593)
              ·
                refine ⟨547943954602202303892445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 730591939469603071856593 547943954602202303892445)
                ·
                  refine ⟨205478982975825863959667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 547943954602202303892445 205478982975825863959667)
                  ·
                    refine ⟨308218474463738795939501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 205478982975825863959667 308218474463738795939501)
                    ·
                      refine ⟨115581927923902048477313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 308218474463738795939501 115581927923902048477313)
                      ·
                        rfl

theorem cell23_225095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_225095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225095 prefixEnd_225095 := by exact prefixLift 225095
  have htrace : WordTrace (prefixWord ++ tailWord_225095) baseStart_225095 baseEnd_225095 := by
    simpa [prefixWord, tailWord_225095, baseEnd_225095] using wordTrace_append hprefix tailTrace_225095
  have hstable : (prefixWord ++ tailWord_225095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225095).length < 2 ^ (prefixWord ++ tailWord_225095).sum := by decide
  have hdescent : baseEnd_225095 < baseStart_225095 := by decide
  rcases family_descends (prefixWord ++ tailWord_225095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225105 : List Nat := [1, 2, 2, 1, 5, 1, 2, 1, 1, 5, 2]
def baseStart_225105 : Nat := 118140960795 + 225105 * 2 ^ 59
def prefixEnd_225105 : Nat := 4983230072969 + 3 ^ 40 * 225105 * 2
def baseEnd_225105 : Nat := 115587062730447009352267

theorem tailTrace_225105 : CollatzResearch.WordTrace tailWord_225105 prefixEnd_225105 115587062730447009352267 := by
  unfold tailWord_225105
  simp only [CollatzResearch.WordTrace]
  refine ⟨8210253849490504718356769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5473502566327003145571179 8210253849490504718356769)
  ·
    refine ⟨6157690387117878538767577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8210253849490504718356769 6157690387117878538767577)
    ·
      refine ⟨4618267790338408904075683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6157690387117878538767577 4618267790338408904075683)
      ·
        refine ⟨6927401685507613356113525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4618267790338408904075683 6927401685507613356113525)
        ·
          refine ⟨649443908016338752135643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6927401685507613356113525 649443908016338752135643)
          ·
            refine ⟨974165862024508128203465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649443908016338752135643 974165862024508128203465)
            ·
              refine ⟨730624396518381096152599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 974165862024508128203465 730624396518381096152599)
              ·
                refine ⟨1095936594777571644228899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 730624396518381096152599 1095936594777571644228899)
                ·
                  refine ⟨1643904892166357466343349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1095936594777571644228899 1643904892166357466343349)
                  ·
                    refine ⟨154116083640596012469689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1643904892166357466343349 154116083640596012469689)
                    ·
                      refine ⟨115587062730447009352267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 154116083640596012469689 115587062730447009352267)
                      ·
                        rfl

theorem cell23_225105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 5, 2].length) (baseStart_225105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225105 prefixEnd_225105 := by exact prefixLift 225105
  have htrace : WordTrace (prefixWord ++ tailWord_225105) baseStart_225105 baseEnd_225105 := by
    simpa [prefixWord, tailWord_225105, baseEnd_225105] using wordTrace_append hprefix tailTrace_225105
  have hstable : (prefixWord ++ tailWord_225105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225105).length < 2 ^ (prefixWord ++ tailWord_225105).sum := by decide
  have hdescent : baseEnd_225105 < baseStart_225105 := by decide
  rcases family_descends (prefixWord ++ tailWord_225105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225122 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 4, 3, 2]
def baseStart_225122 : Nat := 118140960795 + 225122 * 2 ^ 59
def prefixEnd_225122 : Nat := 4983230072969 + 3 ^ 40 * 225122 * 2
def baseEnd_225122 : Nat := 115595791901573442839689

theorem tailTrace_225122 : CollatzResearch.WordTrace tailWord_225122 prefixEnd_225122 115595791901573442839689 := by
  unfold tailWord_225122
  simp only [CollatzResearch.WordTrace]
  refine ⟨2052718472607229155431405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5473915926952611081150413 2052718472607229155431405)
  ·
    refine ⟨769769427227710933286777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2052718472607229155431405 769769427227710933286777)
    ·
      refine ⟨577327070420783199965083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 769769427227710933286777 577327070420783199965083)
      ·
        refine ⟨865990605631174799947625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577327070420783199965083 865990605631174799947625)
        ·
          refine ⟨649492954223381099960719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 865990605631174799947625 649492954223381099960719)
          ·
            refine ⟨974239431335071649941079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649492954223381099960719 974239431335071649941079)
            ·
              refine ⟨1461359147002607474911619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 974239431335071649941079 1461359147002607474911619)
              ·
                refine ⟨2192038720503911212367429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1461359147002607474911619 2192038720503911212367429)
                ·
                  refine ⟨411007260094483352318893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2192038720503911212367429 411007260094483352318893)
                  ·
                    refine ⟨154127722535431257119585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 411007260094483352318893 154127722535431257119585)
                    ·
                      refine ⟨115595791901573442839689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 154127722535431257119585 115595791901573442839689)
                      ·
                        rfl

theorem cell23_225122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_225122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225122 prefixEnd_225122 := by exact prefixLift 225122
  have htrace : WordTrace (prefixWord ++ tailWord_225122) baseStart_225122 baseEnd_225122 := by
    simpa [prefixWord, tailWord_225122, baseEnd_225122] using wordTrace_append hprefix tailTrace_225122
  have hstable : (prefixWord ++ tailWord_225122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225122).length < 2 ^ (prefixWord ++ tailWord_225122).sum := by decide
  have hdescent : baseEnd_225122 < baseStart_225122 := by decide
  rcases family_descends (prefixWord ++ tailWord_225122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225138 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 2, 6, 3]
def baseStart_225138 : Nat := 118140960795 + 225138 * 2 ^ 59
def prefixEnd_225138 : Nat := 4983230072969 + 3 ^ 40 * 225138 * 2
def baseEnd_225138 : Nat := 115604007592045380239615

theorem tailTrace_225138 : CollatzResearch.WordTrace tailWord_225138 prefixEnd_225138 115604007592045380239615 := by
  unfold tailWord_225138
  simp only [CollatzResearch.WordTrace]
  refine ⟨2052864364592737838577017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5474304972247300902872045 2052864364592737838577017)
  ·
    refine ⟨1539648273444553378932763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2052864364592737838577017 1539648273444553378932763)
    ·
      refine ⟨2309472410166830068399145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1539648273444553378932763 2309472410166830068399145)
      ·
        refine ⟨1732104307625122551299359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2309472410166830068399145 1732104307625122551299359)
        ·
          refine ⟨2598156461437683826949039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1732104307625122551299359 2598156461437683826949039)
          ·
            refine ⟨3897234692156525740423559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2598156461437683826949039 3897234692156525740423559)
            ·
              refine ⟨5845852038234788610635339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3897234692156525740423559 5845852038234788610635339)
              ·
                refine ⟨8768778057352182915953009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5845852038234788610635339 8768778057352182915953009)
                ·
                  refine ⟨6576583543014137186964757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8768778057352182915953009 6576583543014137186964757)
                  ·
                    refine ⟨308277353578787680638973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6576583543014137186964757 308277353578787680638973)
                    ·
                      refine ⟨115604007592045380239615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 308277353578787680638973 115604007592045380239615)
                      ·
                        rfl

theorem cell23_225138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_225138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225138 prefixEnd_225138 := by exact prefixLift 225138
  have htrace : WordTrace (prefixWord ++ tailWord_225138) baseStart_225138 baseEnd_225138 := by
    simpa [prefixWord, tailWord_225138, baseEnd_225138] using wordTrace_append hprefix tailTrace_225138
  have hstable : (prefixWord ++ tailWord_225138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225138).length < 2 ^ (prefixWord ++ tailWord_225138).sum := by decide
  have hdescent : baseEnd_225138 < baseStart_225138 := by decide
  rcases family_descends (prefixWord ++ tailWord_225138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225145 : List Nat := [1, 2, 1, 3, 2, 2, 3, 3, 2, 4]
def baseStart_225145 : Nat := 118140960795 + 225145 * 2 ^ 59
def prefixEnd_225145 : Nat := 4983230072969 + 3 ^ 40 * 225145 * 2
def baseEnd_225145 : Nat := 38535867318875617617361

theorem tailTrace_225145 : CollatzResearch.WordTrace tailWord_225145 prefixEnd_225145 38535867318875617617361 := by
  unfold tailWord_225145
  simp only [CollatzResearch.WordTrace]
  refine ⟨8211712769345591549812889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5474475179563727699875259 8211712769345591549812889)
  ·
    refine ⟨6158784577009193662359667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8211712769345591549812889 6158784577009193662359667)
    ·
      refine ⟨9238176865513790493539501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6158784577009193662359667 9238176865513790493539501)
      ·
        refine ⟨3464316324567671435077313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9238176865513790493539501 3464316324567671435077313)
        ·
          refine ⟨2598237243425753576307985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3464316324567671435077313 2598237243425753576307985)
          ·
            refine ⟨1948677932569315182230989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2598237243425753576307985 1948677932569315182230989)
            ·
              refine ⟨730754224713493193336621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1948677932569315182230989 730754224713493193336621)
              ·
                refine ⟨274032834267559947501233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 730754224713493193336621 274032834267559947501233)
                ·
                  refine ⟨205524625700669960625925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274032834267559947501233 205524625700669960625925)
                  ·
                    refine ⟨38535867318875617617361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 205524625700669960625925 38535867318875617617361)
                    ·
                      rfl

theorem cell23_225145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2, 4].length) (baseStart_225145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225145 prefixEnd_225145 := by exact prefixLift 225145
  have htrace : WordTrace (prefixWord ++ tailWord_225145) baseStart_225145 baseEnd_225145 := by
    simpa [prefixWord, tailWord_225145, baseEnd_225145] using wordTrace_append hprefix tailTrace_225145
  have hstable : (prefixWord ++ tailWord_225145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225145).length < 2 ^ (prefixWord ++ tailWord_225145).sum := by decide
  have hdescent : baseEnd_225145 < baseStart_225145 := by decide
  rcases family_descends (prefixWord ++ tailWord_225145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225155 : List Nat := [1, 1, 1, 3, 4, 3, 1, 1, 3, 2, 3]
def baseStart_225155 : Nat := 118140960795 + 225155 * 2 ^ 59
def prefixEnd_225155 : Nat := 4983230072969 + 3 ^ 40 * 225155 * 2
def baseEnd_225155 : Nat := 115612736763171813727037

theorem tailTrace_225155 : CollatzResearch.WordTrace tailWord_225155 prefixEnd_225155 115612736763171813727037 := by
  unfold tailWord_225155
  simp only [CollatzResearch.WordTrace]
  refine ⟨8212077499309363257676919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5474718332872908838451279 8212077499309363257676919)
  ·
    refine ⟨12318116248964044886515379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8212077499309363257676919 12318116248964044886515379)
    ·
      refine ⟨18477174373446067329773069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12318116248964044886515379 18477174373446067329773069)
      ·
        refine ⟨6928940390042275248664901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18477174373446067329773069 6928940390042275248664901)
        ·
          refine ⟨1299176323132926609124669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6928940390042275248664901 1299176323132926609124669)
          ·
            refine ⟨487191121174847478421751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1299176323132926609124669 487191121174847478421751)
            ·
              refine ⟨730786681762271217632627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487191121174847478421751 730786681762271217632627)
              ·
                refine ⟨1096180022643406826448941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 730786681762271217632627 1096180022643406826448941)
                ·
                  refine ⟨411067508491277559918353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1096180022643406826448941 411067508491277559918353)
                  ·
                    refine ⟨308300631368458169938765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 411067508491277559918353 308300631368458169938765)
                    ·
                      refine ⟨115612736763171813727037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 308300631368458169938765 115612736763171813727037)
                      ·
                        rfl

theorem cell23_225155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2, 3].length) (baseStart_225155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225155 prefixEnd_225155 := by exact prefixLift 225155
  have htrace : WordTrace (prefixWord ++ tailWord_225155) baseStart_225155 baseEnd_225155 := by
    simpa [prefixWord, tailWord_225155, baseEnd_225155] using wordTrace_append hprefix tailTrace_225155
  have hstable : (prefixWord ++ tailWord_225155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225155).length < 2 ^ (prefixWord ++ tailWord_225155).sum := by decide
  have hdescent : baseEnd_225155 < baseStart_225155 := by decide
  rcases family_descends (prefixWord ++ tailWord_225155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225168 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 3]
def baseStart_225168 : Nat := 118140960795 + 225168 * 2 ^ 59
def prefixEnd_225168 : Nat := 4983230072969 + 3 ^ 40 * 225168 * 2
def baseEnd_225168 : Nat := 115619412011680262864477

theorem tailTrace_225168 : CollatzResearch.WordTrace tailWord_225168 prefixEnd_225168 115619412011680262864477 := by
  unfold tailWord_225168
  simp only [CollatzResearch.WordTrace]
  refine ⟨4106275824131133238950079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5475034432174844318600105 4106275824131133238950079)
  ·
    refine ⟨6159413736196699858425119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4106275824131133238950079 6159413736196699858425119)
    ·
      refine ⟨9239120604295049787637679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6159413736196699858425119 9239120604295049787637679)
      ·
        refine ⟨13858680906442574681456519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9239120604295049787637679 13858680906442574681456519)
        ·
          refine ⟨20788021359663862022184779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13858680906442574681456519 20788021359663862022184779)
          ·
            refine ⟨31182032039495793033277169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20788021359663862022184779 31182032039495793033277169)
            ·
              refine ⟨23386524029621844774957877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31182032039495793033277169 23386524029621844774957877)
              ·
                refine ⟨2192486627777047947652301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23386524029621844774957877 2192486627777047947652301)
                ·
                  refine ⟨822182485416392980369613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2192486627777047947652301 822182485416392980369613)
                  ·
                    refine ⟨308318432031147367638605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 822182485416392980369613 308318432031147367638605)
                    ·
                      refine ⟨115619412011680262864477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 308318432031147367638605 115619412011680262864477)
                      ·
                        rfl

theorem cell23_225168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 3].length) (baseStart_225168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225168 prefixEnd_225168 := by exact prefixLift 225168
  have htrace : WordTrace (prefixWord ++ tailWord_225168) baseStart_225168 baseEnd_225168 := by
    simpa [prefixWord, tailWord_225168, baseEnd_225168] using wordTrace_append hprefix tailTrace_225168
  have hstable : (prefixWord ++ tailWord_225168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225168).length < 2 ^ (prefixWord ++ tailWord_225168).sum := by decide
  have hdescent : baseEnd_225168 < baseStart_225168 := by decide
  rcases family_descends (prefixWord ++ tailWord_225168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225172 : List Nat := [2, 4, 2, 1, 1, 4, 1, 1, 1, 1, 5]
def baseStart_225172 : Nat := 118140960795 + 225172 * 2 ^ 59
def prefixEnd_225172 : Nat := 4983230072969 + 3 ^ 40 * 225172 * 2
def baseEnd_225172 : Nat := 115621465934298247214459

theorem tailTrace_225172 : CollatzResearch.WordTrace tailWord_225172 prefixEnd_225172 115621465934298247214459 := by
  unfold tailWord_225172
  simp only [CollatzResearch.WordTrace]
  refine ⟨4106348770123887580522885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5475131693498516774030513 4106348770123887580522885)
  ·
    refine ⟨769940394398228921348041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4106348770123887580522885 769940394398228921348041)
    ·
      refine ⟨577455295798671691011031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 769940394398228921348041 577455295798671691011031)
      ·
        refine ⟨866182943698007536516547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577455295798671691011031 866182943698007536516547)
        ·
          refine ⟨1299274415547011304774821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 866182943698007536516547 1299274415547011304774821)
          ·
            refine ⟨243613952915064619645279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1299274415547011304774821 243613952915064619645279)
            ·
              refine ⟨365420929372596929467919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243613952915064619645279 365420929372596929467919)
              ·
                refine ⟨548131394058895394201879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365420929372596929467919 548131394058895394201879)
                ·
                  refine ⟨822197091088343091302819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 548131394058895394201879 822197091088343091302819)
                  ·
                    refine ⟨1233295636632514636954229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 822197091088343091302819 1233295636632514636954229)
                    ·
                      refine ⟨115621465934298247214459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1233295636632514636954229 115621465934298247214459)
                      ·
                        rfl

theorem cell23_225172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_225172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225172 prefixEnd_225172 := by exact prefixLift 225172
  have htrace : WordTrace (prefixWord ++ tailWord_225172) baseStart_225172 baseEnd_225172 := by
    simpa [prefixWord, tailWord_225172, baseEnd_225172] using wordTrace_append hprefix tailTrace_225172
  have hstable : (prefixWord ++ tailWord_225172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225172).length < 2 ^ (prefixWord ++ tailWord_225172).sum := by decide
  have hdescent : baseEnd_225172 < baseStart_225172 := by decide
  rcases family_descends (prefixWord ++ tailWord_225172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225188 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 2, 7]
def baseStart_225188 : Nat := 118140960795 + 225188 * 2 ^ 59
def prefixEnd_225188 : Nat := 4983230072969 + 3 ^ 40 * 225188 * 2
def baseEnd_225188 : Nat := 38543227208256728204795

theorem tailTrace_225188 : CollatzResearch.WordTrace tailWord_225188 prefixEnd_225188 38543227208256728204795 := by
  unfold tailWord_225188
  simp only [CollatzResearch.WordTrace]
  refine ⟨4106640554094904946814109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5475520738793206595752145 4106640554094904946814109)
  ·
    refine ⟨1539990207785589355055291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4106640554094904946814109 1539990207785589355055291)
    ·
      refine ⟨2309985311678384032582937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1539990207785589355055291 2309985311678384032582937)
      ·
        refine ⟨1732488983758788024437203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2309985311678384032582937 1732488983758788024437203)
        ·
          refine ⟨2598733475638182036655805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1732488983758788024437203 2598733475638182036655805)
          ·
            refine ⟨974525053364318263745927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2598733475638182036655805 974525053364318263745927)
            ·
              refine ⟨1461787580046477395618891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 974525053364318263745927 1461787580046477395618891)
              ·
                refine ⟨2192681370069716093428337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1461787580046477395618891 2192681370069716093428337)
                ·
                  refine ⟨1644511027552287070071253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2192681370069716093428337 1644511027552287070071253)
                  ·
                    refine ⟨38543227208256728204795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1644511027552287070071253 38543227208256728204795)
                    ·
                      rfl

theorem cell23_225188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_225188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225188 prefixEnd_225188 := by exact prefixLift 225188
  have htrace : WordTrace (prefixWord ++ tailWord_225188) baseStart_225188 baseEnd_225188 := by
    simpa [prefixWord, tailWord_225188, baseEnd_225188] using wordTrace_append hprefix tailTrace_225188
  have hstable : (prefixWord ++ tailWord_225188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225188).length < 2 ^ (prefixWord ++ tailWord_225188).sum := by decide
  have hdescent : baseEnd_225188 < baseStart_225188 := by decide
  rcases family_descends (prefixWord ++ tailWord_225188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225208 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 2, 3, 4]
def baseStart_225208 : Nat := 118140960795 + 225208 * 2 ^ 59
def prefixEnd_225208 : Nat := 4983230072969 + 3 ^ 40 * 225208 * 2
def baseEnd_225208 : Nat := 115639951237860106364293

theorem tailTrace_225208 : CollatzResearch.WordTrace tailWord_225208 prefixEnd_225208 115639951237860106364293 := by
  unfold tailWord_225208
  simp only [CollatzResearch.WordTrace]
  refine ⟨4107005284058676654678139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5476007045411568872904185 4107005284058676654678139)
  ·
    refine ⟨6160507926088014982017209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4107005284058676654678139 6160507926088014982017209)
    ·
      refine ⟨4620380944566011236512907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6160507926088014982017209 4620380944566011236512907)
      ·
        refine ⟨6930571416849016854769361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4620380944566011236512907 6930571416849016854769361)
        ·
          refine ⟨5197928562636762641077021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6930571416849016854769361 5197928562636762641077021)
          ·
            refine ⟨1949223210988785990403883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5197928562636762641077021 1949223210988785990403883)
            ·
              refine ⟨2923834816483178985605825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1949223210988785990403883 2923834816483178985605825)
              ·
                refine ⟨2192876112362384239204369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2923834816483178985605825 2192876112362384239204369)
                ·
                  refine ⟨1644657084271788179403277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2192876112362384239204369 1644657084271788179403277)
                  ·
                    refine ⟨616746406601920567276229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1644657084271788179403277 616746406601920567276229)
                    ·
                      refine ⟨115639951237860106364293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 616746406601920567276229 115639951237860106364293)
                      ·
                        rfl

theorem cell23_225208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_225208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225208 prefixEnd_225208 := by exact prefixLift 225208
  have htrace : WordTrace (prefixWord ++ tailWord_225208) baseStart_225208 baseEnd_225208 := by
    simpa [prefixWord, tailWord_225208, baseEnd_225208] using wordTrace_append hprefix tailTrace_225208
  have hstable : (prefixWord ++ tailWord_225208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225208).length < 2 ^ (prefixWord ++ tailWord_225208).sum := by decide
  have hdescent : baseEnd_225208 < baseStart_225208 := by decide
  rcases family_descends (prefixWord ++ tailWord_225208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225315 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 4]
def baseStart_225315 : Nat := 118140960795 + 225315 * 2 ^ 59
def prefixEnd_225315 : Nat := 4983230072969 + 3 ^ 40 * 225315 * 2
def baseEnd_225315 : Nat := 115694893667891187726301

theorem tailTrace_225315 : CollatzResearch.WordTrace tailWord_225315 prefixEnd_225315 115694893667891187726301 := by
  unfold tailWord_225315
  simp only [CollatzResearch.WordTrace]
  refine ⟨8217913178729710583501399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5478608785819807055667599 8217913178729710583501399)
  ·
    refine ⟨12326869768094565875252099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8217913178729710583501399 12326869768094565875252099)
    ·
      refine ⟨18490304652141848812878149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12326869768094565875252099 18490304652141848812878149)
      ·
        refine ⟨3466932122276596652414653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18490304652141848812878149 3466932122276596652414653)
        ·
          refine ⟨1300099545853723744655495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3466932122276596652414653 1300099545853723744655495)
          ·
            refine ⟨1950149318780585616983243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1300099545853723744655495 1950149318780585616983243)
            ·
              refine ⟨2925223978170878425474865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1950149318780585616983243 2925223978170878425474865)
              ·
                refine ⟨2193917983628158819106149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2925223978170878425474865 2193917983628158819106149)
                ·
                  refine ⟨411359621930279778582403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2193917983628158819106149 411359621930279778582403)
                  ·
                    refine ⟨617039432895419667873605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 411359621930279778582403 617039432895419667873605)
                    ·
                      refine ⟨115694893667891187726301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 617039432895419667873605 115694893667891187726301)
                      ·
                        rfl

theorem cell23_225315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_225315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225315 prefixEnd_225315 := by exact prefixLift 225315
  have htrace : WordTrace (prefixWord ++ tailWord_225315) baseStart_225315 baseEnd_225315 := by
    simpa [prefixWord, tailWord_225315, baseEnd_225315] using wordTrace_append hprefix tailTrace_225315
  have hstable : (prefixWord ++ tailWord_225315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225315).length < 2 ^ (prefixWord ++ tailWord_225315).sum := by decide
  have hdescent : baseEnd_225315 < baseStart_225315 := by decide
  rcases family_descends (prefixWord ++ tailWord_225315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225335 : List Nat := [1, 1, 3, 1, 2, 2, 2, 3, 1, 4, 3]
def baseStart_225335 : Nat := 118140960795 + 225335 * 2 ^ 59
def prefixEnd_225335 : Nat := 4983230072969 + 3 ^ 40 * 225335 * 2
def baseEnd_225335 : Nat := 115705163280981109476209

theorem tailTrace_225335 : CollatzResearch.WordTrace tailWord_225335 prefixEnd_225335 115705163280981109476209 := by
  unfold tailWord_225335
  simp only [CollatzResearch.WordTrace]
  refine ⟨8218642638657253999229459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5479095092438169332819639 8218642638657253999229459)
  ·
    refine ⟨12327963957985880998844189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8218642638657253999229459 12327963957985880998844189)
    ·
      refine ⟨4622986484244705374566571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12327963957985880998844189 4622986484244705374566571)
      ·
        refine ⟨6934479726367058061849857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4622986484244705374566571 6934479726367058061849857)
        ·
          refine ⟨5200859794775293546387393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6934479726367058061849857 5200859794775293546387393)
          ·
            refine ⟨3900644846081470159790545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5200859794775293546387393 3900644846081470159790545)
            ·
              refine ⟨2925483634561102619842909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3900644846081470159790545 2925483634561102619842909)
              ·
                refine ⟨1097056362960413482441091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2925483634561102619842909 1097056362960413482441091)
                ·
                  refine ⟨1645584544440620223661637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1097056362960413482441091 1645584544440620223661637)
                  ·
                    refine ⟨308547102082616291936557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1645584544440620223661637 308547102082616291936557)
                    ·
                      refine ⟨115705163280981109476209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 308547102082616291936557 115705163280981109476209)
                      ·
                        rfl

theorem cell23_225335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4, 3].length) (baseStart_225335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225335 prefixEnd_225335 := by exact prefixLift 225335
  have htrace : WordTrace (prefixWord ++ tailWord_225335) baseStart_225335 baseEnd_225335 := by
    simpa [prefixWord, tailWord_225335, baseEnd_225335] using wordTrace_append hprefix tailTrace_225335
  have hstable : (prefixWord ++ tailWord_225335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225335).length < 2 ^ (prefixWord ++ tailWord_225335).sum := by decide
  have hdescent : baseEnd_225335 < baseStart_225335 := by decide
  rcases family_descends (prefixWord ++ tailWord_225335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225366 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2]
def baseStart_225366 : Nat := 118140960795 + 225366 * 2 ^ 59
def prefixEnd_225366 : Nat := 4983230072969 + 3 ^ 40 * 225366 * 2
def baseEnd_225366 : Nat := 115721081181270488188567

theorem tailTrace_225366 : CollatzResearch.WordTrace tailWord_225366 prefixEnd_225366 115721081181270488188567 := by
  unfold tailWord_225366
  simp only [CollatzResearch.WordTrace]
  refine ⟨513735831346559143350497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5479848867696630862405301 513735831346559143350497)
  ·
    refine ⟨385301873509919357512873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 513735831346559143350497 385301873509919357512873)
    ·
      refine ⟨288976405132439518134655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385301873509919357512873 288976405132439518134655)
      ·
        refine ⟨433464607698659277201983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288976405132439518134655 433464607698659277201983)
        ·
          refine ⟨650196911547988915802975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433464607698659277201983 650196911547988915802975)
          ·
            refine ⟨975295367321983373704463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650196911547988915802975 975295367321983373704463)
            ·
              refine ⟨1462943050982975060556695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 975295367321983373704463 1462943050982975060556695)
              ·
                refine ⟨2194414576474462590835043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1462943050982975060556695 2194414576474462590835043)
                ·
                  refine ⟨3291621864711693886252565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2194414576474462590835043 3291621864711693886252565)
                  ·
                    refine ⟨154294774908360650918089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3291621864711693886252565 154294774908360650918089)
                    ·
                      refine ⟨115721081181270488188567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 154294774908360650918089 115721081181270488188567)
                      ·
                        rfl

theorem cell23_225366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_225366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225366 prefixEnd_225366 := by exact prefixLift 225366
  have htrace : WordTrace (prefixWord ++ tailWord_225366) baseStart_225366 baseEnd_225366 := by
    simpa [prefixWord, tailWord_225366, baseEnd_225366] using wordTrace_append hprefix tailTrace_225366
  have hstable : (prefixWord ++ tailWord_225366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225366).length < 2 ^ (prefixWord ++ tailWord_225366).sum := by decide
  have hdescent : baseEnd_225366 < baseStart_225366 := by decide
  rcases family_descends (prefixWord ++ tailWord_225366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225372 : List Nat := [2, 2, 4, 1, 1, 2, 2, 3, 6]
def baseStart_225372 : Nat := 118140960795 + 225372 * 2 ^ 59
def prefixEnd_225372 : Nat := 4983230072969 + 3 ^ 40 * 225372 * 2
def baseEnd_225372 : Nat := 12858240229466384968171

theorem tailTrace_225372 : CollatzResearch.WordTrace tailWord_225372 prefixEnd_225372 12858240229466384968171 := by
  unfold tailWord_225372
  simp only [CollatzResearch.WordTrace]
  refine ⟨4109996069761604659163185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5479994759682139545550913 4109996069761604659163185)
  ·
    refine ⟨3082497052321203494372389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4109996069761604659163185 3082497052321203494372389)
    ·
      refine ⟨577968197310225655194823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3082497052321203494372389 577968197310225655194823)
      ·
        refine ⟨866952295965338482792235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577968197310225655194823 866952295965338482792235)
        ·
          refine ⟨1300428443948007724188353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 866952295965338482792235 1300428443948007724188353)
          ·
            refine ⟨975321332961005793141265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1300428443948007724188353 975321332961005793141265)
            ·
              refine ⟨731490999720754344855949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 975321332961005793141265 731490999720754344855949)
              ·
                refine ⟨274309124895282879320981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 731490999720754344855949 274309124895282879320981)
                ·
                  refine ⟨12858240229466384968171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 274309124895282879320981 12858240229466384968171)
                  ·
                    rfl

theorem cell23_225372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 6].length) (baseStart_225372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225372 prefixEnd_225372 := by exact prefixLift 225372
  have htrace : WordTrace (prefixWord ++ tailWord_225372) baseStart_225372 baseEnd_225372 := by
    simpa [prefixWord, tailWord_225372, baseEnd_225372] using wordTrace_append hprefix tailTrace_225372
  have hstable : (prefixWord ++ tailWord_225372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225372).length < 2 ^ (prefixWord ++ tailWord_225372).sum := by decide
  have hdescent : baseEnd_225372 < baseStart_225372 := by decide
  rcases family_descends (prefixWord ++ tailWord_225372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225385 : List Nat := [1, 2, 1, 1, 1, 5, 1, 3, 3, 5]
def baseStart_225385 : Nat := 118140960795 + 225385 * 2 ^ 59
def prefixEnd_225385 : Nat := 4983230072969 + 3 ^ 40 * 225385 * 2
def baseEnd_225385 : Nat := 38576945771235304616993

theorem tailTrace_225385 : CollatzResearch.WordTrace tailWord_225385 prefixEnd_225385 38576945771235304616993 := by
  unfold tailWord_225385
  simp only [CollatzResearch.WordTrace]
  refine ⟨8220466288476112538549609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5480310858984075025699739 8220466288476112538549609)
  ·
    refine ⟨6165349716357084403912207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8220466288476112538549609 6165349716357084403912207)
    ·
      refine ⟨9248024574535626605868311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6165349716357084403912207 9248024574535626605868311)
      ·
        refine ⟨13872036861803439908802467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9248024574535626605868311 13872036861803439908802467)
        ·
          refine ⟨20808055292705159863203701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13872036861803439908802467 20808055292705159863203701)
          ·
            refine ⟨1950755183691108737175347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20808055292705159863203701 1950755183691108737175347)
            ·
              refine ⟨2926132775536663105763021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1950755183691108737175347 2926132775536663105763021)
              ·
                refine ⟨1097299790826248664661133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2926132775536663105763021 1097299790826248664661133)
                ·
                  refine ⟨411487421559843249247925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1097299790826248664661133 411487421559843249247925)
                  ·
                    refine ⟨38576945771235304616993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 411487421559843249247925 38576945771235304616993)
                    ·
                      rfl

theorem cell23_225385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 5].length) (baseStart_225385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225385 prefixEnd_225385 := by exact prefixLift 225385
  have htrace : WordTrace (prefixWord ++ tailWord_225385) baseStart_225385 baseEnd_225385 := by
    simpa [prefixWord, tailWord_225385, baseEnd_225385] using wordTrace_append hprefix tailTrace_225385
  have hstable : (prefixWord ++ tailWord_225385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225385).length < 2 ^ (prefixWord ++ tailWord_225385).sum := by decide
  have hdescent : baseEnd_225385 < baseStart_225385 := by decide
  rcases family_descends (prefixWord ++ tailWord_225385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225386 : List Nat := [3, 1, 3, 2, 3, 2, 1, 1, 2, 2, 3]
def baseStart_225386 : Nat := 118140960795 + 225386 * 2 ^ 59
def prefixEnd_225386 : Nat := 4983230072969 + 3 ^ 40 * 225386 * 2
def baseEnd_225386 : Nat := 115731350794360409938475

theorem tailTrace_225386 : CollatzResearch.WordTrace tailWord_225386 prefixEnd_225386 115731350794360409938475 := by
  unfold tailWord_225386
  simp only [CollatzResearch.WordTrace]
  refine ⟨2055125690368122427334003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5480335174314993139557341 2055125690368122427334003)
  ·
    refine ⟨3082688535552183641001005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2055125690368122427334003 3082688535552183641001005)
    ·
      refine ⟨1156008200832068865375377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3082688535552183641001005 1156008200832068865375377)
      ·
        refine ⟨867006150624051649031533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1156008200832068865375377 867006150624051649031533)
        ·
          refine ⟨325127306484019368386825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 867006150624051649031533 325127306484019368386825)
          ·
            refine ⟨243845479863014526290119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325127306484019368386825 243845479863014526290119)
            ·
              refine ⟨365768219794521789435179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243845479863014526290119 365768219794521789435179)
              ·
                refine ⟨548652329691782684152769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365768219794521789435179 548652329691782684152769)
                ·
                  refine ⟨411489247268837013114577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 548652329691782684152769 411489247268837013114577)
                  ·
                    refine ⟨308616935451627759835933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 411489247268837013114577 308616935451627759835933)
                    ·
                      refine ⟨115731350794360409938475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 308616935451627759835933 115731350794360409938475)
                      ·
                        rfl

theorem cell23_225386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_225386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225386 prefixEnd_225386 := by exact prefixLift 225386
  have htrace : WordTrace (prefixWord ++ tailWord_225386) baseStart_225386 baseEnd_225386 := by
    simpa [prefixWord, tailWord_225386, baseEnd_225386] using wordTrace_append hprefix tailTrace_225386
  have hstable : (prefixWord ++ tailWord_225386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225386).length < 2 ^ (prefixWord ++ tailWord_225386).sum := by decide
  have hdescent : baseEnd_225386 < baseStart_225386 := by decide
  rcases family_descends (prefixWord ++ tailWord_225386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225415 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 3, 6]
def baseStart_225415 : Nat := 118140960795 + 225415 * 2 ^ 59
def prefixEnd_225415 : Nat := 4983230072969 + 3 ^ 40 * 225415 * 2
def baseEnd_225415 : Nat := 38582080577780265491947

theorem tailTrace_225415 : CollatzResearch.WordTrace tailWord_225415 prefixEnd_225415 38582080577780265491947 := by
  unfold tailWord_225415
  simp only [CollatzResearch.WordTrace]
  refine ⟨8221560478367427662141699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5481040318911618441427799 8221560478367427662141699)
  ·
    refine ⟨12332340717551141493212549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8221560478367427662141699 12332340717551141493212549)
    ·
      refine ⟨2312313884540839029977353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12332340717551141493212549 2312313884540839029977353)
      ·
        refine ⟨1734235413405629272483015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2312313884540839029977353 1734235413405629272483015)
        ·
          refine ⟨2601353120108443908724523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1734235413405629272483015 2601353120108443908724523)
          ·
            refine ⟨3902029680162665863086785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2601353120108443908724523 3902029680162665863086785)
            ·
              refine ⟨2926522260121999397315089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3902029680162665863086785 2926522260121999397315089)
              ·
                refine ⟨2194891695091499547986317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2926522260121999397315089 2194891695091499547986317)
                ·
                  refine ⟨823084385659312330494869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2194891695091499547986317 823084385659312330494869)
                  ·
                    refine ⟨38582080577780265491947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 823084385659312330494869 38582080577780265491947)
                    ·
                      rfl

theorem cell23_225415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_225415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225415 prefixEnd_225415 := by exact prefixLift 225415
  have htrace : WordTrace (prefixWord ++ tailWord_225415) baseStart_225415 baseEnd_225415 := by
    simpa [prefixWord, tailWord_225415, baseEnd_225415] using wordTrace_append hprefix tailTrace_225415
  have hstable : (prefixWord ++ tailWord_225415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225415).length < 2 ^ (prefixWord ++ tailWord_225415).sum := by decide
  have hdescent : baseEnd_225415 < baseStart_225415 := by decide
  rcases family_descends (prefixWord ++ tailWord_225415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225416 : List Nat := [2, 1, 3, 4, 1, 2, 2, 1, 3, 1, 3]
def baseStart_225416 : Nat := 118140960795 + 225416 * 2 ^ 59
def prefixEnd_225416 : Nat := 4983230072969 + 3 ^ 40 * 225416 * 2
def baseEnd_225416 : Nat := 115746755213995292563337

theorem tailTrace_225416 : CollatzResearch.WordTrace tailWord_225416 prefixEnd_225416 115746755213995292563337 := by
  unfold tailWord_225416
  simp only [CollatzResearch.WordTrace]
  refine ⟨4110798475681902416464051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5481064634242536555285401 4110798475681902416464051)
  ·
    refine ⟨6166197713522853624696077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4110798475681902416464051 6166197713522853624696077)
    ·
      refine ⟨2312324142571070109261029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6166197713522853624696077 2312324142571070109261029)
      ·
        refine ⟨433560776732075645486443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2312324142571070109261029 433560776732075645486443)
        ·
          refine ⟨650341165098113468229665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433560776732075645486443 650341165098113468229665)
          ·
            refine ⟨487755873823585101172249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 650341165098113468229665 487755873823585101172249)
            ·
              refine ⟨365816905367688825879187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487755873823585101172249 365816905367688825879187)
              ·
                refine ⟨548725358051533238818781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365816905367688825879187 548725358051533238818781)
                ·
                  refine ⟨205772009269324964557043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 548725358051533238818781 205772009269324964557043)
                  ·
                    refine ⟨308658013903987446835565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 205772009269324964557043 308658013903987446835565)
                    ·
                      refine ⟨115746755213995292563337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 308658013903987446835565 115746755213995292563337)
                      ·
                        rfl

theorem cell23_225416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_225416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225416 prefixEnd_225416 := by exact prefixLift 225416
  have htrace : WordTrace (prefixWord ++ tailWord_225416) baseStart_225416 baseEnd_225416 := by
    simpa [prefixWord, tailWord_225416, baseEnd_225416] using wordTrace_append hprefix tailTrace_225416
  have hstable : (prefixWord ++ tailWord_225416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225416).length < 2 ^ (prefixWord ++ tailWord_225416).sum := by decide
  have hdescent : baseEnd_225416 < baseStart_225416 := by decide
  rcases family_descends (prefixWord ++ tailWord_225416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225435 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 4]
def baseStart_225435 : Nat := 118140960795 + 225435 * 2 ^ 59
def prefixEnd_225435 : Nat := 4983230072969 + 3 ^ 40 * 225435 * 2
def baseEnd_225435 : Nat := 115756511346430718225749

theorem tailTrace_225435 : CollatzResearch.WordTrace tailWord_225435 prefixEnd_225435 115756511346430718225749 := by
  unfold tailWord_225435
  simp only [CollatzResearch.WordTrace]
  refine ⟨8222289938294971077869759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5481526625529980718579839 8222289938294971077869759)
  ·
    refine ⟨12333434907442456616804639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8222289938294971077869759 12333434907442456616804639)
    ·
      refine ⟨18500152361163684925206959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12333434907442456616804639 18500152361163684925206959)
      ·
        refine ⟨27750228541745527387810439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18500152361163684925206959 27750228541745527387810439)
        ·
          refine ⟨41625342812618291081715659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27750228541745527387810439 41625342812618291081715659)
          ·
            refine ⟨62438014218927436622573489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41625342812618291081715659 62438014218927436622573489)
            ·
              refine ⟨46828510664195577466930117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62438014218927436622573489 46828510664195577466930117)
              ·
                refine ⟨8780345749536670775049397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46828510664195577466930117 8780345749536670775049397)
                ·
                  refine ⟨823157414019062885160881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8780345749536670775049397 823157414019062885160881)
                  ·
                    refine ⟨617368060514297163870661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 823157414019062885160881 617368060514297163870661)
                    ·
                      refine ⟨115756511346430718225749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 617368060514297163870661 115756511346430718225749)
                      ·
                        rfl

theorem cell23_225435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 4].length) (baseStart_225435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225435 prefixEnd_225435 := by exact prefixLift 225435
  have htrace : WordTrace (prefixWord ++ tailWord_225435) baseStart_225435 baseEnd_225435 := by
    simpa [prefixWord, tailWord_225435, baseEnd_225435] using wordTrace_append hprefix tailTrace_225435
  have hstable : (prefixWord ++ tailWord_225435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225435).length < 2 ^ (prefixWord ++ tailWord_225435).sum := by decide
  have hdescent : baseEnd_225435 < baseStart_225435 := by decide
  rcases family_descends (prefixWord ++ tailWord_225435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225439 : List Nat := [1, 1, 2, 6, 1, 1, 1, 4, 1, 1, 4]
def baseStart_225439 : Nat := 118140960795 + 225439 * 2 ^ 59
def prefixEnd_225439 : Nat := 4983230072969 + 3 ^ 40 * 225439 * 2
def baseEnd_225439 : Nat := 115758565269048702575731

theorem tailTrace_225439 : CollatzResearch.WordTrace tailWord_225439 prefixEnd_225439 115758565269048702575731 := by
  unfold tailWord_225439
  simp only [CollatzResearch.WordTrace]
  refine ⟨8222435830280479761015371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5481623886853653174010247 8222435830280479761015371)
  ·
    refine ⟨12333653745420719641523057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8222435830280479761015371 12333653745420719641523057)
    ·
      refine ⟨9250240309065539731142293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12333653745420719641523057 9250240309065539731142293)
      ·
        refine ⟨433605014487447174897295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9250240309065539731142293 433605014487447174897295)
        ·
          refine ⟨650407521731170762345943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433605014487447174897295 650407521731170762345943)
          ·
            refine ⟨975611282596756143518915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650407521731170762345943 975611282596756143518915)
            ·
              refine ⟨1463416923895134215278373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 975611282596756143518915 1463416923895134215278373)
              ·
                refine ⟨274390673230337665364695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1463416923895134215278373 274390673230337665364695)
                ·
                  refine ⟨411586009845506498047043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 274390673230337665364695 411586009845506498047043)
                  ·
                    refine ⟨617379014768259747070565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 411586009845506498047043 617379014768259747070565)
                    ·
                      refine ⟨115758565269048702575731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 617379014768259747070565 115758565269048702575731)
                      ·
                        rfl

theorem cell23_225439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_225439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225439 prefixEnd_225439 := by exact prefixLift 225439
  have htrace : WordTrace (prefixWord ++ tailWord_225439) baseStart_225439 baseEnd_225439 := by
    simpa [prefixWord, tailWord_225439, baseEnd_225439] using wordTrace_append hprefix tailTrace_225439
  have hstable : (prefixWord ++ tailWord_225439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225439).length < 2 ^ (prefixWord ++ tailWord_225439).sum := by decide
  have hdescent : baseEnd_225439 < baseStart_225439 := by decide
  rcases family_descends (prefixWord ++ tailWord_225439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225445 : List Nat := [1, 3, 1, 2, 1, 3, 3, 9]
def baseStart_225445 : Nat := 118140960795 + 225445 * 2 ^ 59
def prefixEnd_225445 : Nat := 4983230072969 + 3 ^ 40 * 225445 * 2
def baseEnd_225445 : Nat := 4287468376036136262989

theorem tailTrace_225445 : CollatzResearch.WordTrace tailWord_225445 prefixEnd_225445 4287468376036136262989 := by
  unfold tailWord_225445
  simp only [CollatzResearch.WordTrace]
  refine ⟨8222654668258742785733789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5481769778839161857155859 8222654668258742785733789)
  ·
    refine ⟨3083495500597028544650171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8222654668258742785733789 3083495500597028544650171)
    ·
      refine ⟨4625243250895542816975257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3083495500597028544650171 4625243250895542816975257)
      ·
        refine ⟨3468932438171657112731443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4625243250895542816975257 3468932438171657112731443)
        ·
          refine ⟨5203398657257485669097165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3468932438171657112731443 5203398657257485669097165)
          ·
            refine ⟨1951274496471557125911437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5203398657257485669097165 1951274496471557125911437)
            ·
              refine ⟨731727936176833922216789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1951274496471557125911437 731727936176833922216789)
              ·
                refine ⟨4287468376036136262989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 731727936176833922216789 4287468376036136262989)
                ·
                  rfl

theorem cell23_225445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 9].length) (baseStart_225445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225445 prefixEnd_225445 := by exact prefixLift 225445
  have htrace : WordTrace (prefixWord ++ tailWord_225445) baseStart_225445 baseEnd_225445 := by
    simpa [prefixWord, tailWord_225445, baseEnd_225445] using wordTrace_append hprefix tailTrace_225445
  have hstable : (prefixWord ++ tailWord_225445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225445).length < 2 ^ (prefixWord ++ tailWord_225445).sum := by decide
  have hdescent : baseEnd_225445 < baseStart_225445 := by decide
  rcases family_descends (prefixWord ++ tailWord_225445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225493 : List Nat := [1, 3, 2, 4, 2, 2, 1, 2, 1, 2, 3]
def baseStart_225493 : Nat := 118140960795 + 225493 * 2 ^ 59
def prefixEnd_225493 : Nat := 4983230072969 + 3 ^ 40 * 225493 * 2
def baseEnd_225493 : Nat := 115786293224391491300483

theorem tailTrace_225493 : CollatzResearch.WordTrace tailWord_225493 prefixEnd_225493 115786293224391491300483 := by
  unfold tailWord_225493
  simp only [CollatzResearch.WordTrace]
  refine ⟨8224405372084846983481133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5482936914723231322320755 8224405372084846983481133)
  ·
    refine ⟨3084152014531817618805425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8224405372084846983481133 3084152014531817618805425)
    ·
      refine ⟨2313114010898863214104069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3084152014531817618805425 2313114010898863214104069)
      ·
        refine ⟨433708877043536852644513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2313114010898863214104069 433708877043536852644513)
        ·
          refine ⟨325281657782652639483385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 433708877043536852644513 325281657782652639483385)
          ·
            refine ⟨243961243336989479612539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325281657782652639483385 243961243336989479612539)
            ·
              refine ⟨365941865005484219418809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243961243336989479612539 365941865005484219418809)
              ·
                refine ⟨274456398754113164564107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 365941865005484219418809 274456398754113164564107)
                ·
                  refine ⟨411684598131169746846161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 274456398754113164564107 411684598131169746846161)
                  ·
                    refine ⟨308763448598377310134621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 411684598131169746846161 308763448598377310134621)
                    ·
                      refine ⟨115786293224391491300483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 308763448598377310134621 115786293224391491300483)
                      ·
                        rfl

theorem cell23_225493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_225493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225493 prefixEnd_225493 := by exact prefixLift 225493
  have htrace : WordTrace (prefixWord ++ tailWord_225493) baseStart_225493 baseEnd_225493 := by
    simpa [prefixWord, tailWord_225493, baseEnd_225493] using wordTrace_append hprefix tailTrace_225493
  have hstable : (prefixWord ++ tailWord_225493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225493).length < 2 ^ (prefixWord ++ tailWord_225493).sum := by decide
  have hdescent : baseEnd_225493 < baseStart_225493 := by decide
  rcases family_descends (prefixWord ++ tailWord_225493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225495 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 8]
def baseStart_225495 : Nat := 118140960795 + 225495 * 2 ^ 59
def prefixEnd_225495 : Nat := 4983230072969 + 3 ^ 40 * 225495 * 2
def baseEnd_225495 : Nat := 115787320185700483475473

theorem tailTrace_225495 : CollatzResearch.WordTrace tailWord_225495 prefixEnd_225495 115787320185700483475473 := by
  unfold tailWord_225495
  simp only [CollatzResearch.WordTrace]
  refine ⟨8224478318077601325053939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5482985545385067550035959 8224478318077601325053939)
  ·
    refine ⟨12336717477116401987580909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8224478318077601325053939 12336717477116401987580909)
    ·
      refine ⟨4626269053918650745342841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12336717477116401987580909 4626269053918650745342841)
      ·
        refine ⟨3469701790438988059007131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4626269053918650745342841 3469701790438988059007131)
        ·
          refine ⟨5204552685658482088510697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3469701790438988059007131 5204552685658482088510697)
          ·
            refine ⟨3903414514243861566383023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5204552685658482088510697 3903414514243861566383023)
            ·
              refine ⟨5855121771365792349574535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3903414514243861566383023 5855121771365792349574535)
              ·
                refine ⟨8782682657048688524361803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5855121771365792349574535 8782682657048688524361803)
                ·
                  refine ⟨13174023985573032786542705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8782682657048688524361803 13174023985573032786542705)
                  ·
                    refine ⟨9880517989179774589907029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13174023985573032786542705 9880517989179774589907029)
                    ·
                      refine ⟨115787320185700483475473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 9880517989179774589907029 115787320185700483475473)
                      ·
                        rfl

theorem cell23_225495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_225495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225495 prefixEnd_225495 := by exact prefixLift 225495
  have htrace : WordTrace (prefixWord ++ tailWord_225495) baseStart_225495 baseEnd_225495 := by
    simpa [prefixWord, tailWord_225495, baseEnd_225495] using wordTrace_append hprefix tailTrace_225495
  have hstable : (prefixWord ++ tailWord_225495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225495).length < 2 ^ (prefixWord ++ tailWord_225495).sum := by decide
  have hdescent : baseEnd_225495 < baseStart_225495 := by decide
  rcases family_descends (prefixWord ++ tailWord_225495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225569 : List Nat := [1, 2, 3, 2, 1, 1, 3, 5, 5]
def baseStart_225569 : Nat := 118140960795 + 225569 * 2 ^ 59
def prefixEnd_225569 : Nat := 4983230072969 + 3 ^ 40 * 225569 * 2
def baseEnd_225569 : Nat := 12869479750459243772237

theorem tailTrace_225569 : CollatzResearch.WordTrace tailWord_225569 prefixEnd_225569 12869479750459243772237 := by
  unfold tailWord_225569
  simp only [CollatzResearch.WordTrace]
  refine ⟨8227177319809511963247761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5484784879873007975498507 8227177319809511963247761)
  ·
    refine ⟨6170382989857133972435821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8227177319809511963247761 6170382989857133972435821)
    ·
      refine ⟨2313893621196425239663433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6170382989857133972435821 2313893621196425239663433)
      ·
        refine ⟨1735420215897318929747575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2313893621196425239663433 1735420215897318929747575)
        ·
          refine ⟨2603130323845978394621363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1735420215897318929747575 2603130323845978394621363)
          ·
            refine ⟨3904695485768967591932045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2603130323845978394621363 3904695485768967591932045)
            ·
              refine ⟨1464260807163362846974517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3904695485768967591932045 1464260807163362846974517)
              ·
                refine ⟨137274450671565266903861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1464260807163362846974517 137274450671565266903861)
                ·
                  refine ⟨12869479750459243772237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137274450671565266903861 12869479750459243772237)
                  ·
                    rfl

theorem cell23_225569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5, 5].length) (baseStart_225569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225569 prefixEnd_225569 := by exact prefixLift 225569
  have htrace : WordTrace (prefixWord ++ tailWord_225569) baseStart_225569 baseEnd_225569 := by
    simpa [prefixWord, tailWord_225569, baseEnd_225569] using wordTrace_append hprefix tailTrace_225569
  have hstable : (prefixWord ++ tailWord_225569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225569).length < 2 ^ (prefixWord ++ tailWord_225569).sum := by decide
  have hdescent : baseEnd_225569 < baseStart_225569 := by decide
  rcases family_descends (prefixWord ++ tailWord_225569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225592 : List Nat := [2, 1, 2, 1, 3, 1, 2, 3, 1, 2, 5]
def baseStart_225592 : Nat := 118140960795 + 225592 * 2 ^ 59
def prefixEnd_225592 : Nat := 4983230072969 + 3 ^ 40 * 225592 * 2
def baseEnd_225592 : Nat := 115837127809186603962527

theorem tailTrace_225592 : CollatzResearch.WordTrace tailWord_225592 prefixEnd_225592 115837127809186603962527 := by
  unfold tailWord_225592
  simp only [CollatzResearch.WordTrace]
  refine ⟨4114008099363093445667515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5485344132484124594223353 4114008099363093445667515)
  ·
    refine ⟨6171012149044640168501273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4114008099363093445667515 6171012149044640168501273)
    ·
      refine ⟨4628259111783480126375955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6171012149044640168501273 4628259111783480126375955)
      ·
        refine ⟨6942388667675220189563933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4628259111783480126375955 6942388667675220189563933)
        ·
          refine ⟨2603395750378207571086475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6942388667675220189563933 2603395750378207571086475)
          ·
            refine ⟨3905093625567311356629713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2603395750378207571086475 3905093625567311356629713)
            ·
              refine ⟨2928820219175483517472285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3905093625567311356629713 2928820219175483517472285)
              ·
                refine ⟨1098307582190806319052107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2928820219175483517472285 1098307582190806319052107)
                ·
                  refine ⟨1647461373286209478578161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1098307582190806319052107 1647461373286209478578161)
                  ·
                    refine ⟨1235596029964657108933621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1647461373286209478578161 1235596029964657108933621)
                    ·
                      refine ⟨115837127809186603962527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1235596029964657108933621 115837127809186603962527)
                      ·
                        rfl

theorem cell23_225592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_225592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_225592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_225592 prefixEnd_225592 := by exact prefixLift 225592
  have htrace : WordTrace (prefixWord ++ tailWord_225592) baseStart_225592 baseEnd_225592 := by
    simpa [prefixWord, tailWord_225592, baseEnd_225592] using wordTrace_append hprefix tailTrace_225592
  have hstable : (prefixWord ++ tailWord_225592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225592).length < 2 ^ (prefixWord ++ tailWord_225592).sum := by decide
  have hdescent : baseEnd_225592 < baseStart_225592 := by decide
  rcases family_descends (prefixWord ++ tailWord_225592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
